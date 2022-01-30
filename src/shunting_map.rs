//! A guaranteed-to-be-cohesive in memory **direction-aware** [`Map`](`core::iter::Map`) re-implementation.

use core::iter::FusedIterator;

/// A [`Map`](`core::iter::Map`) re-implementation that tells its closure the direction it runs in
/// each time [`Iterator::next`] or [`DoubleEndedIterator::next_back`] is called.
///
/// It makes the same cohesiveness guarantees as [`CohesiveMap`](`crate::cohesive_map::CohesiveMap`);
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[derive(Clone)]
pub struct ShuntingMap<I, F> {
	iter: I,
	f: F,
}

/// Indicates the direction in which a [`ShuntingMap`] is being evaluated.
pub enum Direction {
	/// The iterator is being polled as normal through [`Iterator::next`].
	Forwards,
	/// The iterator is being polled through [`DoubleEndedIterator::next_back`].
	Backwards,
}

#[allow(clippy::module_name_repetitions)]
pub(crate) trait ShuntingMapExt: Sized + Iterator {
	fn shunting_map<F: FnMut(Self::Item, Direction) -> U, U>(self, f: F) -> ShuntingMap<Self, F> {
		ShuntingMap { iter: self, f }
	}
}
impl<I: Iterator> ShuntingMapExt for I {}

impl<I: Iterator, F, U> Iterator for ShuntingMap<I, F>
where
	F: FnMut(I::Item, Direction) -> U,
{
	type Item = U;

	fn next(&mut self) -> Option<Self::Item> {
		self.iter
			.next()
			.map(|item| (self.f)(item, Direction::Forwards))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.iter.size_hint()
	}
}

impl<I: DoubleEndedIterator, F, U> DoubleEndedIterator for ShuntingMap<I, F>
where
	F: FnMut(I::Item, Direction) -> U,
{
	fn next_back(&mut self) -> Option<Self::Item> {
		self.iter
			.next_back()
			.map(|item| (self.f)(item, Direction::Backwards))
	}
}

impl<I: ExactSizeIterator, F, U> ExactSizeIterator for ShuntingMap<I, F> where
	F: FnMut(I::Item, Direction) -> U
{
}

impl<I: FusedIterator, F, U> FusedIterator for ShuntingMap<I, F> where
	F: FnMut(I::Item, Direction) -> U
{
}
