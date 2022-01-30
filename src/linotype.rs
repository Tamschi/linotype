use crate::{
	cohesive_map::CohesiveMapExt,
	shunting_map::{Direction, ShuntingMapExt},
	Index,
};
use alloc::{borrow::ToOwned, vec::Vec};
use core::{
	borrow::Borrow,
	convert::Infallible,
	iter,
	mem::{self, MaybeUninit},
	pin::Pin,
	ptr::{drop_in_place, NonNull},
};
use higher_order_closure::higher_order_closure;
use scopeguard::ScopeGuard;
use tap::{Pipe, Tap};
use typed_arena::Arena;

/// A keyed list reprojector.
pub struct Linotype<K, V> {
	live: Index<K, V>,
	stale: Index<K, V>,
	storage: Arena<V>,
	dropped: Vec<NonNull<V>>,
	/// Used by [`PinningLinotype::unpin`](`crate::PinningLinotype::unpin`).
	pub(crate) pinning: bool,
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
		drop_stale(&mut self.stale, &mut Waste, self.pinning);
		drop_stale(&mut self.live, &mut Waste, self.pinning);
	}
}

fn drop_stale<K, V>(stale: &mut Index<K, V>, dropped: &mut impl Extend<NonNull<V>>, pinning: bool) {
	#[cfg(feature = "std")]
	let mut panic = None;

	let guard = pinning.then(|| scopeguard::guard((), |()| {
		panic!("`Pin<Linotype>`: A key or value drop implementation panicked. The `drop`-guarantee cannot be upheld without the `\"std\"` feature.")
	}));

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
	guard.map(ScopeGuard::into_inner);

	#[cfg(feature = "std")]
	if let Some(panic) = panic {
		std::panic::resume_unwind(panic)
	}
}

/// This currently uses
///
/// ```ignore
/// K: Borrow<Q>,
/// T: 'b,
/// Q: Eq + ToOwned<Owned = K>,
/// S: 'b + FnOnce(&mut T) -> Result<Qr, E>,
/// F: 'b + FnOnce(&mut T) -> Result<V, E>,
/// ```
///
/// instead of
///
///  ```compile_fail
/// K: Borrow<Qr::Target>,
/// T: 'b,
/// Qr: Deref,
/// Qr::Target: Eq + ToOwned<Owned = K>,
/// S: 'b + FnOnce(&mut T) -> Result<Qr, E>,
/// F: 'b + FnOnce(&mut T) -> Result<V, E>,
/// ```
///
/// because the latter has the compiler ask for lifetime bounds on `Qr`, or a duplicate implementation entirely.
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
	/// Note that a panic in a `K` or `V` [`Drop`] implementation will abort the process via double-panic unless the `"std"` feature is enabled,
	/// as long as this instance remains pinning.
	///
	/// With the `"std"` feature enabled, [`Linotype`] will always continue to clean up as needed, then re-panic the first panic it encountered.
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
	pub fn update_try_by_keyed_try_with_keyed<'a: 'b, 'b, T, Q, S, F, I, E>(
		&'a mut self,
		items_selectors_factories: I,
	) -> impl 'b + Iterator<Item = Result<(T, &'a mut V), E>>
	where
		K: Borrow<Q>,
		T: 'b,
		Q: Eq + ToOwned<Owned = K>,
		S: 'b + FnOnce(&mut T) -> Result<&Q, E>,
		F: 'b + FnOnce(&mut T) -> Result<V, E>,
		I: 'b + IntoIterator<Item = (T, S, F)>,
		E: 'b,
	{
		let pinning = self.pinning;
		drop_stale(&mut self.stale, &mut self.dropped, pinning);
		mem::swap(&mut self.live, &mut self.stale);

		let mut stale_and_dropped = scopeguard::guard(
			(&mut self.stale, &mut self.dropped),
			move |(stale, dropped)| drop_stale(stale, dropped, pinning),
		);
		let live = &mut self.live;
		let values = &self.storage;

		items_selectors_factories.into_iter().shunting_map(
			move |(mut item, selector, factory), direction| {
				// Double-references 😬
				// Well, the compiler should be able to figure this out.
				let (stale, dropped) = &mut *stale_and_dropped;
				let key = selector(&mut item)?;
				let mut stale = stale.iter_mut();
				let predicate = |(k, v): &mut (MaybeUninit<K>, _)| match v {
					Some(_) if &*key == unsafe { k.assume_init_ref() }.borrow() => v
						.take()
						.tap(|v| live.push((MaybeUninit::new(unsafe { k.as_ptr().read() }), *v)))
						.map(|mut v| unsafe { v.as_mut() })
						.map(Ok),
					_ => None,
				};
				let v = match direction {
					Direction::Forwards => stale.find_map(predicate),
					Direction::Backwards => stale.rev().find_map(predicate),
				};

				if let Some(v) = v {
					v.map(|v| (item, v))
				} else {
					let k = key.to_owned();
					let v = if let Some(mut v) = dropped.pop() {
						unsafe {
							v.as_ptr().write(factory(&mut item)?);
							v.as_mut()
						}
					} else {
						values.alloc(factory(&mut item)?)
					};

					// I'm *pretty* sure this is okay like that:
					live.push((MaybeUninit::new(k), NonNull::new(v)));
					Ok((item, v))
				}
			},
		)
	}

	/// **Lazily** updates this map according to a sequence of items, a **fallible** selector and **fallible** factory.
	///
	/// Values that aren't reused are dropped together with the returned iterator or on the next `.update…` method call.
	pub fn update_try_by_try_with<'a: 'b, 'b, T, Q, S, F, I, E>(
		&'a mut self,
		items: I,
		mut selector: S,
		mut factory: F,
	) -> impl 'b + Iterator<Item = Result<(T, &'a mut V), E>>
	where
		K: Borrow<Q>,
		T: 'b,
		Q: 'b + Eq + ToOwned<Owned = K>,
		S: 'b + FnMut(&mut T) -> Result<&Q, E>,
		F: 'b + FnMut(&mut T) -> Result<V, E>,
		I: 'b + IntoIterator<Item = T>,
		E: 'b,
	{
		self.update_try_by_keyed_try_with_keyed(items.into_iter().cohesive_map(move |item| {
			let mut selector = NonNull::from(&mut selector);
			let mut factory = NonNull::from(&mut factory);
			(
				item,
				//SAFETY:
				// We know (due to `update_try_by_keyed_try_with_keyed`'s implementation details and `CohesiveMap`)
				// that during each result iterator step, the pointers above will be taken and the functions called without any
				// opportunity for the iterator to move, which means this outer closure here won't move during that time,
				// keeping selector and factory in place.
				higher_order_closure! {
					#![with<T, Q, E>]
					move |item: &mut T| -> Result<&Q, E> {
						(unsafe { selector.as_mut() })(item)
					}
				},
				move |item: &mut T| unsafe { factory.as_mut() }(item)?.pipe(Ok),
			)
		}))
	}

	/// **Lazily** updates this map according to a sequence of item, selector and factory **triples**.
	///
	/// Values that aren't reused are dropped together with the returned iterator or on the next `.update…` method call.
	pub fn update_by_keyed_with_keyed<'a: 'b, 'b, T, Q, S, F, I>(
		&'a mut self,
		items_selectors_factories: I,
	) -> impl 'b + Iterator<Item = (T, &'a mut V)>
	where
		K: Borrow<Q>,
		T: 'b,
		Q: 'b + Eq + ToOwned<Owned = K>,
		S: 'b + FnOnce(&mut T) -> &Q,
		F: 'b + FnOnce(&mut T) -> V,
		I: 'b + IntoIterator<Item = (T, S, F)>,
	{
		self.update_try_by_keyed_try_with_keyed(items_selectors_factories.into_iter().map(
			|(key, selector, factory)| {
				(
					key,
					higher_order_closure! {
						#![with<T, Q>]
						|item: &mut T| -> Result<&Q, Infallible> {
							Ok(selector(item))
						}
					},
					|item: &mut T| Ok(factory(item)),
				)
			},
		))
		.map(unwrap_infallible)
	}

	/// **Lazily** updates this map according to a sequence of items, a selector and a factory.
	///
	/// Values that aren't reused are dropped together with the returned iterator or on the next `.update…` method call.
	pub fn update_by_with<'a: 'b, 'b, T, Q: 'b, S, F, I>(
		&'a mut self,
		items: I,
		mut selector: S,
		mut factory: F,
	) -> impl 'b + Iterator<Item = (T, &'a mut V)>
	where
		K: Borrow<Q>,
		T: 'b,
		Q: Eq + ToOwned<Owned = K>,
		S: 'b + FnMut(&mut T) -> &Q,
		F: 'b + FnMut(&mut T) -> V,
		I: 'b + IntoIterator<Item = T>,
	{
		self.update_try_by_try_with(
			items,
			move |item| Ok(selector(item)),
			move |item| Ok(factory(item)),
		)
		.map(unwrap_infallible)
	}
}

fn unwrap_infallible<T>(infallible: Result<T, Infallible>) -> T {
	infallible.unwrap()
}
