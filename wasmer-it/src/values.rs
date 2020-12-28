use crate::IValue;

use std::slice::Iter;

#[cfg(feature = "serde")]
pub use crate::serde::{de::from_interface_values, ser::to_interface_value};

/// Iterates over a vector of `IValues` but flatten all the
/// values. So `I32(1), Record([I32(2), I32(3)]), I32(4)` will be
/// iterated like `I32(1), I32(2), I32(3), I32(4)`.
pub(crate) struct FlattenIValueIterator<'a> {
    iterators: Vec<Iter<'a, IValue>>,
}

impl<'a> FlattenIValueIterator<'a> {
    pub(crate) fn new(values: &'a [IValue]) -> Self {
        Self {
            iterators: vec![values.iter()],
        }
    }
}

impl<'a> Iterator for FlattenIValueIterator<'a> {
    type Item = &'a IValue;

    fn next(&mut self) -> Option<Self::Item> {
        match self.iterators.last_mut()?.next() {
            // End of the current iterator, go back to the previous
            // one.
            None => {
                self.iterators.pop();
                self.next()
            }

            // Recursively iterate over the record.
            Some(IValue::Record(fields)) => {
                self.iterators.push(fields.iter());
                self.next()
            }

            // A regular item.
            e @ Some(_) => e,
        }
    }
}
