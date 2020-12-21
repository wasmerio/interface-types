use crate::IType;
use crate::IValue;
use crate::IValueImpl;
use crate::{errors::WasmValueNativeCastError, types::IType, vec1::Vec1};
use std::{convert::TryFrom, slice::Iter};

#[cfg(feature = "serde")]
pub use crate::serde::{de::from_interface_values, ser::to_interface_value};

/// Represents a native type supported by WIT.
pub trait NativeType {
    /// The associated interface type that maps to the native type.
    const INTERFACE_TYPE: IType;
}

macro_rules! native {
    ($native_type:ty, $variant:ident) => {
        impl NativeType for $native_type {
            const INTERFACE_TYPE: IType = IType::$variant;
        }

        impl From<$native_type> for IValueImpl {
            fn from(n: $native_type) -> Self {
                let ivalue = IValue::$variant(n);
                Self(ivalue)
            }
        }

        impl TryFrom<&IValueImpl> for $native_type {
            type Error = WasmValueNativeCastError;

            fn try_from(w: &IValue) -> Result<Self, Self::Error> {
                match w {
                    IValue::$variant(n) => Ok(n.clone()),
                    _ => Err(WasmValueNativeCastError {
                        from: w.clone(),
                        to: <$native_type>::INTERFACE_TYPE,
                    }),
                }
            }
        }
    };
}

native!(i8, S8);
native!(i16, S16);
native!(i32, I32);
native!(i64, I64);
native!(u8, U8);
native!(u16, U16);
native!(u32, U32);
native!(u64, U64);
native!(f32, F32);
native!(f64, F64);
native!(String, String);

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
