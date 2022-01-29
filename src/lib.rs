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

mod linotype;
mod pinning_linotype;

pub use linotype::Linotype;
pub use pinning_linotype::PinningLinotype;

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
