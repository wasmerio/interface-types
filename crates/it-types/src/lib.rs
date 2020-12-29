#[cfg(feature = "impls")]
mod impls;
pub mod ne_vec;
mod types;
mod values;

// types
pub use types::IType;
pub use types::RecordFieldType as IRecordFieldType;
pub use types::RecordType as IRecordType;

#[cfg(feature = "impls")]
pub use impls::NativeType;

// values
pub use values::IValue;

// errors
#[cfg(feature = "impls")]
pub use impls::WasmValueNativeCastError;
