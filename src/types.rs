//! This module defines the WIT types.

use crate::vec1::Vec1;
use serde::{Deserialize, Serialize};

/// Represents the types supported by WIT.
#[derive(PartialEq, Eq, Debug, Clone, Serialize, Deserialize)]
pub enum InterfaceType {
    /// A 8-bits signed integer.
    S8,

    /// A 16-bits signed integer.
    S16,

    /// A 32-bits signed integer.
    S32,

    /// A 64-bits signed integer.
    S64,

    /// A 8-bits unsigned integer.
    U8,

    /// A 16-bits unsigned integer.
    U16,

    /// A 32-bits unsigned integer.
    U32,

    /// A 64-bits unsigned integer.
    U64,

    /// A 32-bits float.
    F32,

    /// A 64-bits float.
    F64,

    /// A string.
    String,

    /// A byte array.
    ByteArray,

    /// An `any` reference.
    Anyref,

    /// A 32-bits integer (as defined in WebAssembly core).
    I32,

    /// A 64-bits integer (as defiend in WebAssembly core).
    I64,

    /// A record contains type name.
    // TODO: consider making it &str
    Record(String),
}

/// Represents a record field type.
#[derive(PartialEq, Eq, Debug, Clone, Serialize, Deserialize)]
pub struct RecordFieldType {
    // TODO: make name optional to support structures with anonymous fields in Rust
    /// A field name.
    pub name: String,

    /// A field type.
    pub ty: InterfaceType,
}

/// Represents a record type.
#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct RecordType {
    /// A record name.
    pub name: String,

    /// Types and names representing the fields.
    /// A record must have at least one field, hence the
    /// [`Vec1`][crate::vec1::Vec1].
    pub fields: Vec1<RecordFieldType>,
}
