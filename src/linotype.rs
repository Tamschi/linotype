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

use crate::Index;

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