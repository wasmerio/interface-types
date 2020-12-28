use crate::IType;
use crate::IValue;
use crate::WasmValueNativeCastError;

use std::convert::TryFrom;

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

        impl From<$native_type> for IValue {
            fn from(n: $native_type) -> Self {
                IValue::$variant(n)
            }
        }

        impl TryFrom<&IValue> for $native_type {
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
