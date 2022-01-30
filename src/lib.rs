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
//! > This is legal because pinning only implies an *attempt* to drop a pinned instance before it can be freed¹
//! > (also since if a [`Drop`] implementation panics, that instance is (in general) considered dropped²).
//! >
//! > ¹ [`core::pin`: `Drop` guarantee](`core::pin`#drop-guarantee)  
//! > ² [`Drop::drop`: Panics](`Drop`#panics)
//!
//! # Performance Focus
//!
//! This implementation is optimised for relatively small entry counts,
//! like instances of a GUI component in a mutable list generated from some input sequence.
//!
//! # (Current) Caveats
//!
//! - [`Linotype`] updates have quadratic time complexity over the number of items.
//!
//!   This could largely be mitigated by remembering how many entries in `stale` already have [`None`] instead of a value pointer, counting from each end.
//!
//! - Return types are improper.
//!
//!   Even if the closure types can't be fully specified right now, it should be possible to expose the compound iterators directly.
//!   This would give access to the [`DoubleEndedIterator`], [`ExactSizeIterator`] and [`FusedIterator`](`core::iter::FusedIterator`) implementations where appropriate.
//!
//!   Moving the dynamic call further inwards would likely also improve [`Pin<Linotype>`](`PinningLinotype`#impl-PinningLinotype-for-Pin<Linotype<K%2C%20V>>)'s performance for at least some operations.
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

pub mod cohesive_map;
mod linotype;
mod pinning_linotype;
pub mod shunting_map;

pub use self::linotype::Linotype;
pub use pinning_linotype::PinningLinotype;

use alloc::vec::Vec;
use core::{mem::MaybeUninit, ptr::NonNull};

/// [`Some`]-ness of [`Index::1`] indicates initialisation status of [`Index::0`].
type Index<K, V> = Vec<(MaybeUninit<K>, Option<NonNull<V>>)>;
