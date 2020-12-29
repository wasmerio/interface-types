use crate::IType;
use crate::IValue;

use std::error::Error;
use std::fmt::Display;
use std::fmt::Formatter;
use std::fmt::Result;

/// Structure to represent errors when casting from an `IType`
/// to a native value.
#[derive(Debug)]
pub struct WasmValueNativeCastError {
    /// The initial type.
    pub from: IValue,

    /// The targeted type.
    ///
    /// `IType` is used to represent the native type by
    /// associativity.
    pub to: IType,
}

impl Error for WasmValueNativeCastError {}

impl Display for WasmValueNativeCastError {
    fn fmt(&self, formatter: &mut Formatter) -> Result {
        write!(formatter, "{:?}", self)
    }
}
