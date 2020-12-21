//! Defines WIT values and associated operations.

use crate::vec1::Vec1;

/// A WIT value.
#[derive(Debug, Clone, PartialEq)]
pub enum InterfaceValue {
    /// A 8-bits signed integer.
    S8(i8),

    /// A 16-bits signed integer.
    S16(i16),

    /// A 32-bits signed integer.
    S32(i32),

    /// A 64-bits signed integer.
    S64(i64),

    /// A 8-bits unsigned integer.
    U8(u8),

    /// A 16-bits unsigned integer.
    U16(u16),

    /// A 32-bits unsigned integer.
    U32(u32),

    /// A 64-bits unsigned integer.
    U64(u64),

    /// A 32-bits float.
    F32(f32),

    /// A 64-bits float.
    F64(f64),

    /// A string.
    String(String),

    /// A byte array.
    Array(Vec<InterfaceValue>),

    //Anyref(?),
    /// A 32-bits integer (as defined in WebAssembly core).
    I32(i32),

    /// A 64-bits integer (as defiend in WebAssembly core).
    I64(i64),

    /// A record.
    Record(Vec1<InterfaceValue>),
}

impl Default for InterfaceValue {
    fn default() -> Self {
        Self::I32(0)
    }
}
