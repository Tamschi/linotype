//! A stable transactionally-incremental indexed map that can pin its values.
//!
//! [![Zulip Chat](https://img.shields.io/endpoint?label=chat&url=https%3A%2F%2Fiteration-square-automation.schichler.dev%2F.netlify%2Ffunctions%2Fstream_subscribers_shield%3Fstream%3Dproject%252Flinotype)](https://iteration-square.schichler.dev/#narrow/stream/project.2Flinotype)
//!
//! # Features
//!
//! ## `"std"`
//!
//! Allows this crate to avoid memory leaks into the internal value storage arena in case of panicking [`Drop`] implementations, but has otherwise no effect.
//!
//! > This is legal
//!
//! # Performance Focus
//!
//! This implementation is optimised for relatively small entry counts,
//! like instances of a GUI component in a mutable list generated from some input sequence.
#![no_std]
#![doc(html_root_url = "https://docs.rs/linotype/0.0.1")]
#![warn(clippy::pedantic, missing_docs)]
#![allow(clippy::semicolon_if_nothing_returned)]

#[cfg(doctest)]
#[doc = include_str!("../README.md")]
mod readme {}

extern crate alloc;

#[cfg(feature = "std")]
extern crate std;

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

/// [`Some`]-ness of [`Index::1`] indicates initialisation status of [`Index::0`].
type Index<K, V> = Vec<(MaybeUninit<K>, Option<NonNull<V>>)>;

/// A keyed list reprojector.
pub struct Linotype<K, V> {
	live: Index<K, V>,
	stale: Index<K, V>,
	storage: Arena<V>,
	dropped: Vec<NonNull<V>>,
	pinning: bool,
}

impl<K, V> Default for Linotype<K, V> {
	fn default() -> Self {
		Self::new()
	}
}

impl<K, V> Drop for Linotype<K, V> {
	fn drop(&mut self) {
		// It's a bit roundabout, but nicely takes care of the panic-handling.

		struct Waste;
		impl<T> Extend<T> for Waste {
			fn extend<I: IntoIterator<Item = T>>(&mut self, _: I) {}
		}
		drop_stale(&mut self.stale, &mut Waste);
		drop_stale(&mut self.live, &mut Waste);
	}
}

fn drop_stale<K, V>(stale: &mut Index<K, V>, dropped: &mut impl Extend<NonNull<V>>) {
	#[cfg(feature = "std")]
	let mut panic = None;

	let guard = scopeguard::guard((), |()| {
		panic!("`Pin<Linotype>`: A key or value drop implementation panicked. The `drop`-guarantee cannot be upheld without the `\"std\"` feature.")
	});

	for (k, v) in stale.drain(..) {
		match v {
			None => (),
			Some(v) => unsafe {
				#[cfg(feature = "std")]
				{
					use std::panic::{catch_unwind, AssertUnwindSafe};

					let k_ = catch_unwind(AssertUnwindSafe(|| drop(k.assume_init()))).err();
					let v_ = catch_unwind(AssertUnwindSafe(|| drop_in_place(v.as_ptr()))).err();
					panic = panic.or(k_).or(v_);
				}
				#[cfg(not(feature = "std"))]
				{
					drop(k.assume_init());
					drop_in_place(v.as_ptr());
				}
				dropped.extend(iter::once(v))
			},
		}
	}
	ScopeGuard::into_inner(guard);

	#[cfg(feature = "std")]
	if let Some(panic) = panic {
		std::panic::resume_unwind(panic)
	}
}

impl<K, V> Linotype<K, V> {
	/// Creates a new non-pinning [`Linotype`] instance.
	///
	/// > TODO:
	/// >
	/// > This can *nearly* be `const`.
	/// > It may be worthwhile to contribute a second constructor to [`Arena`].
	#[must_use]
	pub fn new() -> Self {
		Self {
			live: Vec::new(),
			stale: Vec::new(),
			storage: Arena::new(),
			dropped: Vec::new(),
			pinning: false,
		}
	}

	/// Turns this [`Linotype`] into a [`Pin`] of its values.
	///
	/// # Safety Notes
	///
	/// Note that this sets a flag to abort on panics from key and value [`Drop`] implementations iff the `"std"` feature is not active.
	///
	/// This means that transmuting a [`Linotype`] to wrap it in a [`Pin`] is normally **not** a sound operation.  
	/// However, [`Linotype`] itself never relies on this flag in other circumstances.
	pub const fn pin(mut self) -> Pin<Self> {
		self.pinning = true;
		unsafe { mem::transmute(self) }
	}

	/// Retrieves a reference to the first value associated with `key`, iff available.
	pub fn get<Q>(&self, key: &Q) -> Option<&V>
	where
		K: Borrow<Q>,
		Q: Eq,
	{
		self.live.iter().find_map(|(k, v)| match v {
			Some(v) if key == unsafe { k.assume_init_ref() }.borrow() => {
				Some(unsafe { v.as_ref() })
			}
			_ => None,
		})
	}

	/// Retrieves a mutable reference to the first value associated with `key`, iff available.
	pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
	where
		K: Borrow<Q>,
		Q: Eq,
	{
		self.live.iter_mut().find_map(|(k, v)| match v {
			Some(v) if key == unsafe { k.assume_init_ref() }.borrow() => {
				Some(unsafe { v.as_mut() })
			}
			_ => None,
		})
	}

	/// **Lazily** updates this map according to a sequence of item, **fallible** selector and **fallible** factory **triples**.
	///
	/// Values that aren't reused are dropped together with the returned iterator or on the next `.update…` method call.
	pub fn update_try_by_keyed_try_with_keyed<'a: 'b, 'b, T, Qr, S, F, I, E>(
		&'a mut self,
		items_selectors_factories: I,
	) -> impl 'b + Iterator<Item = Result<(T, &'a mut V), E>>
	where
		K: Borrow<Qr::Target>,
		T: 'b,
		Qr: Deref,
		Qr::Target: Eq + ToOwned<Owned = K>,
		S: 'b + FnOnce(&mut T) -> Result<Qr, E>,
		F: 'b + FnOnce(&mut T, Qr) -> Result<V, E>,
		I: 'b + IntoIterator<Item = (T, S, F)>,
		E: 'b,
	{
		drop_stale(&mut self.stale, &mut self.dropped);
		mem::swap(&mut self.live, &mut self.stale);

		let mut stale_and_dropped =
			scopeguard::guard((&mut self.stale, &mut self.dropped), |(stale, dropped)| {
				drop_stale(stale, dropped)
			});
		let live = &mut self.live;
		let values = &self.storage;

		items_selectors_factories
			.into_iter()
			.map(move |(mut item, selector, factory)| {
				// Double-references 😬
				// Well, the compiler should be able to figure this out.
				let (stale, dropped) = &mut *stale_and_dropped;
				let key = selector(&mut item)?;
				let v = stale
					.iter_mut()
					.find_map(|(k, v)| match v {
						Some(_) if key.deref() == unsafe { k.assume_init_ref() }.borrow() => v
							.take()
							.tap(|v| {
								live.push((MaybeUninit::new(unsafe { k.as_ptr().read() }), *v))
							})
							.map(|mut v| unsafe { v.as_mut() })
							.map(Ok),
						_ => None,
					})
					.unwrap_or_else(|| {
						let k = key.to_owned();
						let v = if let Some(mut v) = dropped.pop() {
							unsafe {
								v.as_ptr().write(factory(&mut item, key)?);
								v.as_mut()
							}
						} else {
							values.alloc(factory(&mut item, key)?)
						};

						// I'm *pretty* sure this is okay like that:
						live.push((MaybeUninit::new(k), NonNull::new(v)));
						Ok(v)
					})?;
				Ok((item, v))
			})
	}

	/// **Lazily** updates this map according to a sequence of items and a **fallible** selector and **fallible** factory.
	///
	/// Values that aren't reused are dropped together with the returned iterator or on the next `.update…` method call.
	pub fn update_try_by_try_with<'a: 'b, 'b, T, Qr, S, F, I, E>(
		&'a mut self,
		items: I,
		selector: S,
		factory: F,
	) -> impl 'b + Iterator<Item = Result<(T, &'a mut V), E>>
	where
		K: Borrow<Qr::Target>,
		T: 'b,
		Qr: Deref,
		Qr::Target: Eq + ToOwned<Owned = K>,
		S: 'b + FnMut(&mut T) -> Result<Qr, E>,
		F: 'b + FnMut(&mut T, Qr) -> Result<V, E>,
		I: 'b + IntoIterator<Item = T>,
		E: 'b,
	{
		self.update_try_by_keyed_try_with_keyed(items.into_iter().map(move |item| {
			let selector = NonNull::from(&mut selector);
			let factory = NonNull::from(&mut factory);
			(
				item,
				//SAFETY:
				// We know (due to `update_try_by_keyed_try_with_keyed`) that during each result iterator step,
				// the pointers above will be taken and the functions called without any opportunity for the iterator
				// to move, which means this outer closure here won't move during that time,
				// keeping selector and factory in place.
				//
				//BUG: Iterator::map is probably implement this way, but the specification doesn't actually
				// guarantee it I think, and which implementation we use may actually differ here… which
				// means I'll have to use a custom Map implementation that I *know* won't shift the closure around internally,
				// and in `update_try_by_keyed_try_with_keyed` I'll have to use one I know won't shift the iterator before calling the closure.
				move |item| unsafe { selector.as_mut() }(item),
				move |item, key| unsafe { factory.as_mut() }(item, key),
			)
		}))
	}

	/// **Lazily** updates this map according to a sequence of keys and a **fallible** factory.
	///
	/// Values that aren't reused are dropped together with the returned iterator or on the next `.update…` method call.
	pub fn update_try_with<'a: 'b, 'b, Q, F, I, E>(
		&'a mut self,
		keys: I,
		mut factory: F,
	) -> impl 'b + Iterator<Item = Result<(&'b Q, &'a mut V), E>>
	where
		K: Borrow<Q>,
		Q: 'b + Eq + ToOwned<Owned = K>,
		F: 'b + FnMut(&'b Q) -> Result<V, E>,
		I: 'b + IntoIterator<Item = &'b Q>,
		E: 'b,
	{
		let keyed_factories = keys.into_iter().map(move |key| {
			let factory = RefCell::new(unsafe { &mut *(&mut factory as *mut _) });
			(key, move |key| factory.borrow_mut()(key))
		});
		self.update_try_by_try_with_keyed(keyed_factories)
	}

	/// **Lazily** updates this map according to a sequence of key and **infallible** factory **pairs**.
	///
	/// Values that aren't reused are dropped together with the returned iterator or on the next `.update…` method call.
	pub fn update_with_keyed<'a: 'b, 'b, Q, F, I>(
		&'a mut self,
		keyed_factories: I,
	) -> impl 'b + Iterator<Item = (&'b Q, &'a mut V)>
	where
		K: Borrow<Q>,
		Q: 'b + Eq + ToOwned<Owned = K>,
		F: 'b + FnOnce(&'b Q) -> V,
		I: 'b + IntoIterator<Item = (&'b Q, F)>,
	{
		let keyed_factories = keyed_factories
			.into_iter()
			.map(|(key, factory)| (key, |k| Ok(factory(k))));
		self.update_try_by_try_with_keyed(keyed_factories)
			.map(unwrap_infallible)
	}

	/// **Lazily** updates this map according to a sequence of keys and an **infallible** factory.
	///
	/// Values that aren't reused are dropped together with the returned iterator or on the next `.update…` method call.
	pub fn update_with<'a: 'b, 'b, Q, F, I>(
		&'a mut self,
		keys: I,
		mut factory: F,
	) -> impl 'b + Iterator<Item = (&'b Q, &'a mut V)>
	where
		K: Borrow<Q>,
		Q: 'b + Eq + ToOwned<Owned = K>,
		F: 'b + FnMut(&'b Q) -> V,
		I: 'b + IntoIterator<Item = &'b Q>,
	{
		let keyed_factories = keys.into_iter().map(move |key| {
			let factory = RefCell::new(unsafe { &mut *(&mut factory as *mut _) });
			(key, move |key| factory.borrow_mut()(key))
		});
		self.update_with_keyed(keyed_factories)
	}
}

fn unwrap_infallible<T>(infallible: Result<T, Infallible>) -> T {
	infallible.unwrap()
}

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
impl<K, V> PinningLinotype for Pin<Linotype<K, V>> {
	type K = K;
	type V = V;

	/// Retrieves a reference to the first value associated with `key`, iff available.
	fn get<Q>(&self, key: &Q) -> Option<Pin<&V>>
	where
		K: Borrow<Q>,
		Q: Eq,
	{
		self.as_non_pin().get(key).map(wrap_in_pin)
	}

	/// Retrieves a mutable reference to the first value associated with `key`, iff available.
	fn get_mut<Q>(&mut self, key: &Q) -> Option<Pin<&mut V>>
	where
		K: Borrow<Q>,
		Q: Eq,
	{
		self.as_non_pin_mut().get_mut(key).map(wrap_in_pin)
	}

	#[allow(clippy::type_complexity)]
	fn update_try_with_keyed<'a: 'b, 'b, Q, F, I, E>(
		&'a mut self,
		keyed_factories: I,
	) -> Box<dyn 'b + Iterator<Item = Result<(&'b Q, Pin<&'a mut V>), E>>>
	where
		K: Borrow<Q>,
		Q: 'b + Eq + ToOwned<Owned = K>,
		F: 'b + FnOnce(&'b Q) -> Result<V, E>,
		I: 'b + IntoIterator<Item = (&'b Q, F)>,
		E: 'b,
	{
		self.as_non_pin_mut()
			.update_try_by_try_with_keyed(keyed_factories)
			.map(|result| result.map(|(k, v)| (k, wrap_in_pin(v))))
			.pipe(Box::new)
	}

	#[allow(clippy::type_complexity)]
	fn update_try_with<'a: 'b, 'b, Q, F, I, E>(
		&'a mut self,
		keys: I,
		factory: F,
	) -> Box<dyn 'b + Iterator<Item = Result<(&'b Q, Pin<&'a mut V>), E>>>
	where
		K: Borrow<Q>,
		Q: 'b + Eq + ToOwned<Owned = K>,
		F: 'b + FnMut(&'b Q) -> Result<V, E>,
		I: 'b + IntoIterator<Item = &'b Q>,
		E: 'b,
	{
		self.as_non_pin_mut()
			.update_try_with(keys, factory)
			.map(|result| result.map(|(k, v)| (k, wrap_in_pin(v))))
			.pipe(Box::new)
	}

	fn update_with_keyed<'a: 'b, 'b, Q, F, I>(
		&'a mut self,
		keyed_factories: I,
	) -> Box<dyn 'b + Iterator<Item = (&'b Q, Pin<&'a mut V>)>>
	where
		K: Borrow<Q>,
		Q: 'b + Eq + ToOwned<Owned = K>,
		F: 'b + FnOnce(&'b Q) -> V,
		I: 'b + IntoIterator<Item = (&'b Q, F)>,
	{
		self.as_non_pin_mut()
			.update_with_keyed(keyed_factories)
			.map(|(k, v)| (k, wrap_in_pin(v)))
			.pipe(Box::new)
	}

	fn update_with<'a: 'b, 'b, Q, F, I>(
		&'a mut self,
		keys: I,
		factory: F,
	) -> Box<dyn 'b + Iterator<Item = (&'b Q, Pin<&'a mut V>)>>
	where
		K: Borrow<Q>,
		Q: 'b + Eq + ToOwned<Owned = K>,
		F: 'b + FnMut(&'b Q) -> V,
		I: 'b + IntoIterator<Item = &'b Q>,
	{
		self.as_non_pin_mut()
			.update_with(keys, factory)
			.map(|(k, v)| (k, wrap_in_pin(v)))
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
fn wrap_in_pin<T: Deref>(value: T) -> Pin<T> {
	unsafe { Pin::new_unchecked(value) }
}
