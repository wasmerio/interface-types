//! `NEVec<T>` represents a non-empty `Vec<T>`.

use serde::{Deserialize, Serialize};
use std::{
    error,
    fmt::{self, Debug},
    ops,
};

/// `NEVec<T>` represents a non-empty `Vec<T>`. It derefs to `Vec<T>`
/// directly.
#[derive(Clone, PartialEq, Eq, Serialize, Hash, Deserialize, Default)]
pub struct NEVec<T>(Vec<T>)
where
    T: Debug;

/// Represents the only error that can be emitted by `NEVec`, i.e. when
/// the number of items is zero.
#[derive(Debug)]
pub struct EmptyVec;

impl error::Error for EmptyVec {}

impl fmt::Display for EmptyVec {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "NEVec must as least contain one item, zero given"
        )
    }
}

impl<T> NEVec<T>
where
    T: Debug,
{
    /// Creates a new non-empty vector, based on an inner `Vec<T>`. If
    /// the inner vector is empty, a `EmptyVec` error is returned.
    pub fn new(items: Vec<T>) -> Result<Self, EmptyVec> {
        if items.is_empty() {
            Err(EmptyVec)
        } else {
            Ok(Self(items))
        }
    }

    /// Converts this NEVec into Vec
    pub fn into_vec(self) -> Vec<T> {
        self.0
    }
}

impl<T> fmt::Debug for NEVec<T>
where
    T: Debug,
{
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{:?}", self.0)
    }
}

impl<T> ops::Deref for NEVec<T>
where
    T: Debug,
{
    type Target = Vec<T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
