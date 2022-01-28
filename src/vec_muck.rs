//! Iterator-like [`Vec`]-manipulation.

use alloc::vec::Vec;

pub struct NonLocal<'a, T> {
	vec: &'a mut Vec<T>,
	cursor: usize,
}

impl<'a, T> NonLocal<'a, T> {
	pub fn new(vec: &'a mut Vec<T>) -> Self {
		Self { vec, cursor: 0 }
	}

	pub fn next(&mut self) -> VecEntry<'_, 'a, T> {
		if self.cursor < self.vec.len() {
			self.cursor += 1;
			VecEntry::Occupied(Occupied { parent: self })
		} else {
			VecEntry::Vacant(Vacant { parent: self })
		}
	}
}

pub enum VecEntry<'a, 'b, T> {
	Occupied(Occupied<'a, 'b, T>),
	Vacant(Vacant<'a, 'b, T>),
}

pub struct Occupied<'a, 'b, T> {
	parent: &'a mut NonLocal<'b, T>,
}

pub struct Vacant<'a, 'b, T> {
	parent: &'a mut NonLocal<'b, T>,
}

impl<T> Occupied<'_, '_, T> {
	pub fn swap_remove(self) -> T {
		self.parent.cursor -= 1;
		self.parent.vec.swap_remove(self.parent.cursor)
	}
}
