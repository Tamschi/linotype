use crate::Linotype;
use alloc::{borrow::ToOwned, boxed::Box, vec::Vec};
use core::{
	borrow::Borrow,
	cell::RefCell,
	convert::Infallible,
	iter,
	mem::{self, MaybeUninit},
	ops::Deref,
	pin::Pin,
	ptr::{drop_in_place, NonNull},
};
use scopeguard::ScopeGuard;
use tap::{Pipe, Tap};
use typed_arena::Arena;

/// The value-pinning [`Linotype`] API.
///
/// This can't be associated directly because `self: Pin<Self>` is currently not a valid method receiver.
pub trait PinningLinotype {
	/// The type of stored keys.
	type K;
	/// The type of values.
	type V;

	/// Retrieves a reference to the first value associated with `key`, iff available.
	fn get<Q>(&self, key: &Q) -> Option<Pin<&Self::V>>
	where
		Self::K: Borrow<Q>,
		Q: Eq;

	/// Retrieves a mutable reference to the first value associated with `key`, iff available.
	fn get_mut<Q>(&mut self, key: &Q) -> Option<Pin<&mut Self::V>>
	where
		Self::K: Borrow<Q>,
		Q: Eq;

	/// **Lazily** updates this map according to a sequence of key and **fallible** factory **pairs**.
	///
	/// Resulting values are pinned.
	///
	/// Values that aren't reused are dropped together with the returned iterator or on the next `.update…` method call.
	#[allow(clippy::type_complexity)]
	fn update_try_with_keyed<'a: 'b, 'b, Q, F, I, E>(
		&'a mut self,
		keyed_factories: I,
	) -> Box<dyn 'b + Iterator<Item = Result<(&'b Q, Pin<&'a mut Self::V>), E>>>
	where
		Self::K: Borrow<Q>,
		Q: 'b + Eq + ToOwned<Owned = Self::K>,
		F: 'b + FnOnce(&'b Q) -> Result<Self::V, E>,
		I: 'b + IntoIterator<Item = (&'b Q, F)>,
		E: 'b;

	/// **Lazily** updates this map according to a sequence of keys and a **fallible** factory.
	///
	/// Values that aren't reused are dropped together with the returned iterator or on the next `.update…` method call.
	#[allow(clippy::type_complexity)]
	fn update_try_with<'a: 'b, 'b, Q, F, I, E>(
		&'a mut self,
		keys: I,
		factory: F,
	) -> Box<dyn 'b + Iterator<Item = Result<(&'b Q, Pin<&'a mut Self::V>), E>>>
	where
		Self::K: Borrow<Q>,
		Q: 'b + Eq + ToOwned<Owned = Self::K>,
		F: 'b + FnMut(&'b Q) -> Result<Self::V, E>,
		I: 'b + IntoIterator<Item = &'b Q>,
		E: 'b;

	/// **Lazily** updates this map according to a sequence of key and **infallible** factory **pairs**.
	///
	/// Values that aren't reused are dropped together with the returned iterator or on the next `.update…` method call.
	fn update_with_keyed<'a: 'b, 'b, Q, F, I>(
		&'a mut self,
		keyed_factories: I,
	) -> Box<dyn 'b + Iterator<Item = (&'b Q, Pin<&'a mut Self::V>)>>
	where
		Self::K: Borrow<Q>,
		Q: 'b + Eq + ToOwned<Owned = Self::K>,
		F: 'b + FnOnce(&'b Q) -> Self::V,
		I: 'b + IntoIterator<Item = (&'b Q, F)>;

	/// **Lazily** updates this map according to a sequence of keys and an **infallible** factory.
	///
	/// Values that aren't reused are dropped together with the returned iterator or on the next `.update…` method call.
	fn update_with<'a: 'b, 'b, Q, F, I>(
		&'a mut self,
		keys: I,
		factory: F,
	) -> Box<dyn 'b + Iterator<Item = (&'b Q, Pin<&'a mut Self::V>)>>
	where
		Self::K: Borrow<Q>,
		Q: 'b + Eq + ToOwned<Owned = Self::K>,
		F: 'b + FnMut(&'b Q) -> Self::V,
		I: 'b + IntoIterator<Item = &'b Q>;
}
// impl<K, V> PinningLinotype for Pin<Linotype<K, V>> {
// 	type K = K;
// 	type V = V;

// 	/// Retrieves a reference to the first value associated with `key`, iff available.
// 	fn get<Q>(&self, key: &Q) -> Option<Pin<&V>>
// 	where
// 		K: Borrow<Q>,
// 		Q: Eq,
// 	{
// 		self.as_non_pin().get(key).map(wrap_in_pin)
// 	}

// 	/// Retrieves a mutable reference to the first value associated with `key`, iff available.
// 	fn get_mut<Q>(&mut self, key: &Q) -> Option<Pin<&mut V>>
// 	where
// 		K: Borrow<Q>,
// 		Q: Eq,
// 	{
// 		self.as_non_pin_mut().get_mut(key).map(wrap_in_pin)
// 	}

// 	#[allow(clippy::type_complexity)]
// 	fn update_try_with_keyed<'a: 'b, 'b, Q, F, I, E>(
// 		&'a mut self,
// 		keyed_factories: I,
// 	) -> Box<dyn 'b + Iterator<Item = Result<(&'b Q, Pin<&'a mut V>), E>>>
// 	where
// 		K: Borrow<Q>,
// 		Q: 'b + Eq + ToOwned<Owned = K>,
// 		F: 'b + FnOnce(&'b Q) -> Result<V, E>,
// 		I: 'b + IntoIterator<Item = (&'b Q, F)>,
// 		E: 'b,
// 	{
// 		self.as_non_pin_mut()
// 			.update_try_by_try_with_keyed(keyed_factories)
// 			.map(|result| result.map(|(k, v)| (k, wrap_in_pin(v))))
// 			.pipe(Box::new)
// 	}

// 	#[allow(clippy::type_complexity)]
// 	fn update_try_with<'a: 'b, 'b, Q, F, I, E>(
// 		&'a mut self,
// 		keys: I,
// 		factory: F,
// 	) -> Box<dyn 'b + Iterator<Item = Result<(&'b Q, Pin<&'a mut V>), E>>>
// 	where
// 		K: Borrow<Q>,
// 		Q: 'b + Eq + ToOwned<Owned = K>,
// 		F: 'b + FnMut(&'b Q) -> Result<V, E>,
// 		I: 'b + IntoIterator<Item = &'b Q>,
// 		E: 'b,
// 	{
// 		self.as_non_pin_mut()
// 			.update_try_with(keys, factory)
// 			.map(|result| result.map(|(k, v)| (k, wrap_in_pin(v))))
// 			.pipe(Box::new)
// 	}

// 	fn update_with_keyed<'a: 'b, 'b, Q, F, I>(
// 		&'a mut self,
// 		keyed_factories: I,
// 	) -> Box<dyn 'b + Iterator<Item = (&'b Q, Pin<&'a mut V>)>>
// 	where
// 		K: Borrow<Q>,
// 		Q: 'b + Eq + ToOwned<Owned = K>,
// 		F: 'b + FnOnce(&'b Q) -> V,
// 		I: 'b + IntoIterator<Item = (&'b Q, F)>,
// 	{
// 		self.as_non_pin_mut()
// 			.update_with_keyed(keyed_factories)
// 			.map(|(k, v)| (k, wrap_in_pin(v)))
// 			.pipe(Box::new)
// 	}

// 	fn update_with<'a: 'b, 'b, Q, F, I>(
// 		&'a mut self,
// 		keys: I,
// 		factory: F,
// 	) -> Box<dyn 'b + Iterator<Item = (&'b Q, Pin<&'a mut V>)>>
// 	where
// 		K: Borrow<Q>,
// 		Q: 'b + Eq + ToOwned<Owned = K>,
// 		F: 'b + FnMut(&'b Q) -> V,
// 		I: 'b + IntoIterator<Item = &'b Q>,
// 	{
// 		self.as_non_pin_mut()
// 			.update_with(keys, factory)
// 			.map(|(k, v)| (k, wrap_in_pin(v)))
// 			.pipe(Box::new)
// 	}
// }

/// # Safety
///
/// This trait is only safe to implement if not misused.
unsafe trait PinHelper {
	type T;

	fn as_non_pin(&self) -> &Self::T;
	fn as_non_pin_mut(&mut self) -> &mut Self::T;
}

/// # Safety Notes
///
/// All methods on [`Linotype`] that are callable through the pinning API act as if the values were always pinned.
unsafe impl<K, V> PinHelper for Pin<Linotype<K, V>> {
	type T = Linotype<K, V>;

	fn as_non_pin(&self) -> &Self::T {
		unsafe { &*(self as *const Pin<Linotype<K, V>>).cast::<Linotype<K, V>>() }
	}

	fn as_non_pin_mut(&mut self) -> &mut Self::T {
		unsafe { &mut *(self as *mut Pin<Linotype<K, V>>).cast::<Linotype<K, V>>() }
	}
}

/// # Safety Notes
///
/// This would be horribly unsafe if exposed. It acts as adapter in the pinning API here,
/// since the non-pinning API (privately!) already acts as if the values were pinned,
/// as far as it is callable through the public pinning API.
fn wrap_in_pin<T: Deref>(value: T) -> Pin<T> {
	unsafe { Pin::new_unchecked(value) }
}
