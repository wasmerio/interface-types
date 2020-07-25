//! `Vec1<T>` represents a non-empty `Vec<T>`.

use serde::{Deserialize, Serialize};
use std::{
    error,
    fmt::{self, Debug},
    ops,
};

/// `Vec1<T>` represents a non-empty `Vec<T>`. It derefs to `Vec<T>`
/// directly.
#[derive(Clone, PartialEq, Serialize, Deserialize, Default)]
pub struct Vec1<T>(pub(crate) Vec<T>)
where
    T: Debug;

/// Represents the only error that can be emitted by `Vec1`, i.e. when
/// the number of items is zero.
#[derive(Debug)]
pub struct EmptyVec;

impl error::Error for EmptyVec {}

impl fmt::Display for EmptyVec {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "Vec1 must as least contain one item, zero given")
    }
}

impl<T> Vec1<T>
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

    /// Converts this Vec1 into Vec
    pub fn into_vec(self) -> Vec<T> {
        self.0
    }
}

impl<T> fmt::Debug for Vec1<T>
where
    T: Debug,
{
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{:?}", self.0)
    }
}

impl<T> ops::Deref for Vec1<T>
where
    T: Debug,
{
    type Target = Vec<T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
