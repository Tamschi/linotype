use crate::Linotype;
use alloc::{borrow::ToOwned, boxed::Box};
use core::{
	borrow::Borrow,
	mem::{self},
	ops::Deref,
	pin::Pin,
};
use tap::{Pipe};


/// The value-pinning [`Linotype`] API.
///
/// This can't be associated directly because `self: Pin<Self>` is currently not a valid method receiver.
pub trait PinningLinotype {
	/// The type of stored keys.
	type K;
	/// The type of values.
	type V;

	/// Converts this instance back into a non-pinning [`Linotype<K, V>`].
	fn unpin(self) -> Linotype<Self::K, Self::V>
	where
		Self::V: Unpin;

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

	/// **Lazily** updates this map according to a sequence of item, **fallible** selector and **fallible** factory **triples**.
	///
	/// Values that aren't reused are dropped together with the returned iterator or on the next `.update…` method call.
	#[allow(clippy::type_complexity)]
	fn update_try_by_keyed_try_with_keyed<'a: 'b, 'b, T, Q, S, F, I, E>(
		&'a mut self,
		items_selectors_factories: I,
	) -> Box<dyn 'b + Iterator<Item = Result<(T, Pin<&'a mut Self::V>), E>>>
	where
		Self::K: Borrow<Q>,
		T: 'b,
		Q: 'b + Eq + ToOwned<Owned = Self::K>,
		S: 'b + FnOnce(&mut T) -> Result<&Q, E>,
		F: 'b + FnOnce(&mut T) -> Result<Self::V, E>,
		I: 'b + IntoIterator<Item = (T, S, F)>,
		E: 'b;

	/// **Lazily** updates this map according to a sequence of items, a **fallible** selector and **fallible** factory.
	///
	/// Values that aren't reused are dropped together with the returned iterator or on the next `.update…` method call.
	#[allow(clippy::type_complexity)]
	fn update_try_by_try_with<'a: 'b, 'b, T, Q, S, F, I, E>(
		&'a mut self,
		items: I,
		selector: S,
		factory: F,
	) -> Box<dyn 'b + Iterator<Item = Result<(T, Pin<&'a mut Self::V>), E>>>
	where
		Self::K: Borrow<Q>,
		T: 'b,
		Q: 'b + Eq + ToOwned<Owned = Self::K>,
		S: 'b + FnMut(&mut T) -> Result<&Q, E>,
		F: 'b + FnMut(&mut T) -> Result<Self::V, E>,
		I: 'b + IntoIterator<Item = T>,
		E: 'b;

	/// **Lazily** updates this map according to a sequence of item, selector and factory **triples**.
	///
	/// Values that aren't reused are dropped together with the returned iterator or on the next `.update…` method call.
	fn update_by_keyed_with_keyed<'a: 'b, 'b, T, Q, S, F, I>(
		&'a mut self,
		items_selectors_factories: I,
	) -> Box<dyn 'b + Iterator<Item = (T, Pin<&'a mut Self::V>)>>
	where
		Self::K: Borrow<Q>,
		T: 'b,
		Q: 'b + Eq + ToOwned<Owned = Self::K>,
		S: 'b + FnOnce(&mut T) -> &Q,
		F: 'b + FnOnce(&mut T) -> Self::V,
		I: 'b + IntoIterator<Item = (T, S, F)>;

	/// **Lazily** updates this map according to a sequence of items, a selector and a factory.
	///
	/// Values that aren't reused are dropped together with the returned iterator or on the next `.update…` method call.
	fn update_by_with<'a: 'b, 'b, T, Q: 'b, S, F, I>(
		&'a mut self,
		items: I,
		selector: S,
		factory: F,
	) -> Box<dyn 'b + Iterator<Item = (T, Pin<&'a mut Self::V>)>>
	where
		Self::K: Borrow<Q>,
		T: 'b,
		Q: Eq + ToOwned<Owned = Self::K>,
		S: 'b + FnMut(&mut T) -> &Q,
		F: 'b + FnMut(&mut T) -> Self::V,
		I: 'b + IntoIterator<Item = T>;
}
impl<K, V> PinningLinotype for Pin<Linotype<K, V>> {
	type K = K;

	type V = V;

	fn unpin(self) -> Linotype<K, V>
	where
		V: Unpin,
	{
		unsafe { mem::transmute(self) }
	}

	fn get<Q>(&self, key: &Q) -> Option<Pin<&V>>
	where
		K: Borrow<Q>,
		Q: Eq,
	{
		self.as_non_pin().get(key).map(wrap_in_pin)
	}

	fn get_mut<Q>(&mut self, key: &Q) -> Option<Pin<&mut V>>
	where
		K: Borrow<Q>,
		Q: Eq,
	{
		self.as_non_pin_mut().get_mut(key).map(wrap_in_pin)
	}

	#[allow(clippy::type_complexity)]
	fn update_try_by_keyed_try_with_keyed<'a: 'b, 'b, T, Q, S, F, I, E>(
		&'a mut self,
		items_selectors_factories: I,
	) -> Box<dyn 'b + Iterator<Item = Result<(T, Pin<&'a mut V>), E>>>
	where
		K: Borrow<Q>,
		T: 'b,
		Q: 'b + Eq + ToOwned<Owned = K>,
		S: 'b + FnOnce(&mut T) -> Result<&Q, E>,
		F: 'b + FnOnce(&mut T) -> Result<V, E>,
		I: 'b + IntoIterator<Item = (T, S, F)>,
		E: 'b,
	{
		self.as_non_pin_mut()
			.update_try_by_keyed_try_with_keyed(items_selectors_factories)
			.map(wrap_value_in_result_in_pin)
			.pipe(Box::new)
	}

	#[allow(clippy::type_complexity)]
	fn update_try_by_try_with<'a: 'b, 'b, T, Q, S, F, I, E>(
		&'a mut self,
		items: I,
		selector: S,
		factory: F,
	) -> Box<dyn 'b + Iterator<Item = Result<(T, Pin<&'a mut V>), E>>>
	where
		K: Borrow<Q>,
		T: 'b,
		Q: 'b + Eq + ToOwned<Owned = K>,
		S: 'b + FnMut(&mut T) -> Result<&Q, E>,
		F: 'b + FnMut(&mut T) -> Result<V, E>,
		I: 'b + IntoIterator<Item = T>,
		E: 'b,
	{
		self.as_non_pin_mut()
			.update_try_by_try_with(items, selector, factory)
			.map(wrap_value_in_result_in_pin)
			.pipe(Box::new)
	}

	fn update_by_keyed_with_keyed<'a: 'b, 'b, T, Q, S, F, I>(
		&'a mut self,
		items_selectors_factories: I,
	) -> Box<dyn 'b + Iterator<Item = (T, Pin<&'a mut V>)>>
	where
		K: Borrow<Q>,
		T: 'b,
		Q: 'b + Eq + ToOwned<Owned = K>,
		S: 'b + FnOnce(&mut T) -> &Q,
		F: 'b + FnOnce(&mut T) -> V,
		I: 'b + IntoIterator<Item = (T, S, F)>,
	{
		self.as_non_pin_mut()
			.update_by_keyed_with_keyed(items_selectors_factories)
			.map(wrap_value_in_pin)
			.pipe(Box::new)
	}

	fn update_by_with<'a: 'b, 'b, T, Q: 'b, S, F, I>(
		&'a mut self,
		items: I,
		selector: S,
		factory: F,
	) -> Box<dyn 'b + Iterator<Item = (T, Pin<&'a mut V>)>>
	where
		K: Borrow<Q>,
		T: 'b,
		Q: Eq + ToOwned<Owned = K>,
		S: 'b + FnMut(&mut T) -> &Q,
		F: 'b + FnMut(&mut T) -> V,
		I: 'b + IntoIterator<Item = T>,
	{
		self.as_non_pin_mut()
			.update_by_with(items, selector, factory)
			.map(wrap_value_in_pin)
			.pipe(Box::new)
	}
}

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
fn wrap_in_pin<V: Deref>(value: V) -> Pin<V> {
	unsafe { Pin::new_unchecked(value) }
}

/// # Safety Notes
///
/// This would be horribly unsafe if exposed. It acts as adapter in the pinning API here,
/// since the non-pinning API (privately!) already acts as if the values were pinned,
/// as far as it is callable through the public pinning API.
fn wrap_value_in_pin<T, V: Deref>((item, value): (T, V)) -> (T, Pin<V>) {
	(item, wrap_in_pin(value))
}

/// # Safety Notes
///
/// This would be horribly unsafe if exposed. It acts as adapter in the pinning API here,
/// since the non-pinning API (privately!) already acts as if the values were pinned,
/// as far as it is callable through the public pinning API.
fn wrap_value_in_result_in_pin<T, V: Deref, E>(
	result: Result<(T, V), E>,
) -> Result<(T, Pin<V>), E> {
	result.map(wrap_value_in_pin)
}
