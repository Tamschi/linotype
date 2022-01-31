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
//! - [`OwnedProjection`] updates have quadratic time complexity over the number of items.
//!
//!   This could largely be mitigated by remembering how many entries in `stale` already have [`None`] instead of a value pointer, counting from each end.
//!
//! - Return types are improper.
//!
//!   Even if the closure types can't be fully specified for now, it should be possible to expose the compound iterators directly.
//!   This would give access to the [`DoubleEndedIterator`], [`ExactSizeIterator`] and [`FusedIterator`](`core::iter::FusedIterator`) implementations where appropriate.
//!
//!   Moving the dynamic call further inwards would likely also improve [`Pin<OwnedProjection>`](`PinningOwnedProjection`#impl-PinningOwnedProjection-for-Pin<OwnedProjection<K%2C%20V>>)'s performance for at least some operations.
//!
//! - Use-case coverage isn't great.
//!
//!   This is mainly due to me right now needing only a (very) limited subset of what this type could in theory support.
//!
//!   The most significant omission right now is likely any way to index the collection directly, or to extract entries by value.
//!
//! [Visit the repository](https://github.com/Tamschi/linotype) to file an issue or pull-request.
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
mod owned_projection;
mod pinning_owned_projection;
pub mod shunting_map;

pub use self::owned_projection::OwnedProjection;
pub use pinning_owned_projection::PinningOwnedProjection;

use alloc::vec::Vec;
use core::{mem::MaybeUninit, ptr::NonNull};

/// [`Some`]-ness of [`Index::1`] indicates initialisation status of [`Index::0`].
type Index<K, V> = Vec<(MaybeUninit<K>, Option<NonNull<V>>)>;
