//! This module defines the WIT types.

use crate::ne_vec::NEVec;

use serde::Deserialize;
use serde::Serialize;

/// Represents the types supported by WIT.
#[derive(PartialEq, Eq, Debug, Clone, Hash, Serialize, Deserialize)]
pub enum IType {
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

    /// An array of values of the same type.
    Array(Box<IType>),

    /// An `any` reference.
    Anyref,

    /// A 32-bits integer (as defined in WebAssembly core).
    I32,

    /// A 64-bits integer (as defined in WebAssembly core).
    I64,

    /// A record contains record index from interfaces AST.
    Record(u64),
}

/// Represents a record field type.
#[derive(PartialEq, Eq, Debug, Clone, Hash, Serialize, Deserialize)]
pub struct RecordFieldType {
    // TODO: make name optional to support structures with anonymous fields in Rust
    /// A field name.
    pub name: String,

    /// A field type.
    pub ty: IType,
}

/// Represents a record type.
#[derive(PartialEq, Eq, Debug, Clone, Hash, Serialize, Deserialize)]
pub struct RecordType {
    /// A record name.
    pub name: String,

    /// Types and names representing the fields.
    /// A record must have at least one field, hence the
    /// [`Vec1`][crate::vec1::Vec1].
    pub fields: NEVec<RecordFieldType>,
}

impl Default for RecordType {
    fn default() -> Self {
        Self {
            name: String::new(),
            fields: NEVec::new(vec![RecordFieldType {
                name: String::new(),
                ty: IType::S8,
            }])
            .unwrap(),
        }
    }
}

/// Encode an `IType` into a string.
// TODO: consider change to impl Display
impl ToString for &IType {
    fn to_string(&self) -> String {
        match &self {
            IType::S8 => "s8".to_string(),
            IType::S16 => "s16".to_string(),
            IType::S32 => "s32".to_string(),
            IType::S64 => "s64".to_string(),
            IType::U8 => "u8".to_string(),
            IType::U16 => "u16".to_string(),
            IType::U32 => "u32".to_string(),
            IType::U64 => "u64".to_string(),
            IType::F32 => "f32".to_string(),
            IType::F64 => "f64".to_string(),
            IType::String => "string".to_string(),
            IType::Array(ty) => format!("array ({})", ty.as_ref().to_string()),
            IType::Anyref => "anyref".to_string(),
            IType::I32 => "i32".to_string(),
            IType::I64 => "i64".to_string(),
            IType::Record(record_type_id) => format!("record {}", record_type_id),
        }
    }
}

impl ToString for &RecordType {
    fn to_string(&self) -> String {
        format!(
            "record ${} (\n{fields})",
            self.name,
            fields = self
                .fields
                .iter()
                .fold(String::new(), |mut accumulator, field_type| {
                    accumulator.push(' ');
                    accumulator.push_str(&format!(
                        "field ${}: {}\n",
                        field_type.name,
                        (&field_type.ty).to_string()
                    ));
                    accumulator
                }),
        )
    }
}
