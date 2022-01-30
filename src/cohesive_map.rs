//! A guaranteed-to-be-cohesive in memory [`Map`](`core::iter::Map`) re-implementation.

use core::iter::FusedIterator;

/// A [`Map`](`core::iter::Map`) re-implementation that… really does nothing all that significantly differently right now.
///
/// It's likely a little slower than the standard library's, due to relying on default implementations more.
///
/// However, [`CohesiveMap`] hereby does guarantee not to move its instances of `I` and `F` by itself and also that it won't buffer anything (by itself).
/// This makes it suitable for certain cross-closure pointer tricks used elsewhere in this crate to avoid overhead.
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[derive(Clone)]
pub struct CohesiveMap<I, F> {
	iter: I,
	f: F,
}

#[allow(clippy::module_name_repetitions)]
pub(crate) trait CohesiveMapExt: Sized + Iterator {
	fn cohesive_map<F: FnMut(Self::Item) -> U, U>(self, f: F) -> CohesiveMap<Self, F> {
		CohesiveMap { iter: self, f }
	}
}
impl<I: Iterator> CohesiveMapExt for I {}

impl<I: Iterator, F, U> Iterator for CohesiveMap<I, F>
where
	F: FnMut(I::Item) -> U,
{
	type Item = U;

	fn next(&mut self) -> Option<Self::Item> {
		self.iter.next().map(&mut self.f)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.iter.size_hint()
	}
}

impl<I: DoubleEndedIterator, F, U> DoubleEndedIterator for CohesiveMap<I, F>
where
	F: FnMut(I::Item) -> U,
{
	fn next_back(&mut self) -> Option<Self::Item> {
		self.iter.next_back().map(&mut self.f)
	}
}

impl<I: ExactSizeIterator, F, U> ExactSizeIterator for CohesiveMap<I, F> where F: FnMut(I::Item) -> U
{}

impl<I: FusedIterator, F, U> FusedIterator for CohesiveMap<I, F> where F: FnMut(I::Item) -> U {}
