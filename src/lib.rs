//! A stable transactionally-incremental indexed map that can pin its values.
//!
//! [![Zulip Chat](https://img.shields.io/endpoint?label=chat&url=https%3A%2F%2Fiteration-square-automation.schichler.dev%2F.netlify%2Ffunctions%2Fstream_subscribers_shield%3Fstream%3Dproject%252Flinotype)](https://iteration-square.schichler.dev/#narrow/stream/project.2Flinotype)
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

use alloc::{borrow::ToOwned, vec::Vec};
use core::{borrow::Borrow, convert::Infallible, ptr::NonNull};
use typed_arena::Arena;

pub struct Linotype<K, V> {
	hot_index: Vec<(Option<K>, NonNull<V>)>,
	cold_index: Vec<(Option<K>, NonNull<V>)>,
	values: Arena<V>,
}

impl<K, V> Linotype<K, V> {
	/// Retrieves a reference to the first value associated with `key`, iff available.
	pub fn get<Q>(&self, key: &Q) -> Option<&V>
	where
		K: Borrow<Q>,
		Q: Eq,
	{
		self.hot_index.iter().find_map(|(k, v)| match k {
			Some(k) if key == k.borrow() => Some(unsafe { v.as_ref() }),
			_ => None,
		})
	}

	/// Retrieves a mutable reference to the first value associated with `key`, iff available.
	pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
	where
		K: Borrow<Q>,
		Q: Eq,
	{
		self.hot_index.iter_mut().find_map(|(k, v)| match k {
			Some(k) if key == (*k).borrow() => Some(unsafe { v.as_mut() }),
			_ => None,
		})
	}

	pub fn update_try_with_keyed<'a: 'b, 'b, Q, F, I, E>(
		&'a mut self,
		keyed_factories: I,
	) -> impl 'b + Iterator<Item = Result<(&'a K, &'a mut V), E>>
	where
		Q: 'b + Eq + ToOwned<Owned = K>,
		F: 'b + FnOnce(&'a K) -> Result<V, E>,
		I: 'b + IntoIterator<Item = (&'b Q, F)>,
	{
		todo!()
	}

	pub fn update_try_with<'a: 'b, 'b, Q, F, I, E>(
		&'a mut self,
		keys: I,
		mut factory: F,
	) -> impl 'b + Iterator<Item = Result<(&'a K, &'a mut V), E>>
	where
		Q: 'b + Eq + ToOwned<Owned = K>,
		F: 'b + FnMut(&'a K) -> Result<V, E>,
		I: 'b + IntoIterator<Item = &'b Q>,
		E: 'b,
	{
		let keys = keys.into_iter();
		self.update_try_with_keyed(keys.map(move |key| {
			let factory = unsafe { &mut *(&mut factory as *mut F) };
			(key, move |k| factory(k))
		}))
	}

	pub fn update_with_keyed<'a: 'b, 'b, Q, F, I>(
		&'a mut self,
		keyed_factories: I,
	) -> impl 'b + Iterator<Item = (&'a K, &'a mut V)>
	where
		Q: 'b + Eq + ToOwned<Owned = K>,
		F: 'b + FnOnce(&'a K) -> V,
		I: 'b + IntoIterator<Item = (&'b Q, F)>,
	{
		let keyed_factories = keyed_factories.into_iter();
		self.update_try_with_keyed(keyed_factories.map(|(key, factory)| (key, |k| Ok(factory(k)))))
			.map(unwrap_infallible)
	}

	pub fn update_with<'a: 'b, 'b, Q, F, I>(
		&'a mut self,
		keys: I,
		mut factory: F,
	) -> impl 'b + Iterator<Item = (&'a K, &'a mut V)>
	where
		Q: 'b + Eq + ToOwned<Owned = K>,
		F: 'b + FnMut(&'a K) -> V,
		I: 'b + IntoIterator<Item = &'b Q>,
	{
		let keys = keys.into_iter();
		self.update_with_keyed(keys.map(move |key| {
			let factory = unsafe { &mut *(&mut factory as *mut F) };
			(key, move |k| factory(k))
		}))
	}
}

fn unwrap_infallible<T>(infallible: Result<T, Infallible>) -> T {
	infallible.unwrap()
}
