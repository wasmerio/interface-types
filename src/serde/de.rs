//! Provides a deserializer from WIT values to Rust value.

use crate::{
    types::InterfaceType,
    values::{FlattenInterfaceValueIterator, InterfaceValue},
};
use serde::{de, Deserialize};
use std::{
    fmt::{self, Display},
    iter::Peekable,
};

/// Deserialize a set of `InterfaceValue`s to a type `T` that
/// implements the `Deserialize` trait.
///
/// This is not a requirement to use WIT, but Serde provides an even
/// nicer API to the user to rebuild its complex types from WIT
/// values.
///
/// # Example
///
/// ```rust
/// use wasmer_interface_types::{
///     values::{InterfaceValue, from_interface_values},
///     vec1::Vec1,
/// };
/// use serde::Deserialize;
///
/// #[derive(Deserialize, Debug, PartialEq)]
/// struct S(i32, i64);
///
/// #[derive(Deserialize, Debug, PartialEq)]
/// struct T<'a> {
///     x: &'a str,
///     s: S,
///     y: f32,
/// };
///
/// let values = vec![InterfaceValue::Record(Vec1::new(vec![
///     InterfaceValue::String("abc".to_string()),
///     InterfaceValue::Record(Vec1::new(vec![InterfaceValue::I32(1), InterfaceValue::I64(2)]).unwrap()),
///     InterfaceValue::F32(3.),
/// ]).unwrap())];
/// let t = from_interface_values::<T>(&values).unwrap();
///
/// assert_eq!(
///     t,
///     T {
///         x: "abc",
///         s: S(1, 2),
///         y: 3.,
///     }
/// );
/// ```
pub fn from_interface_values<'a, T>(values: &'a [InterfaceValue]) -> Result<T, DeserializeError>
where
    T: Deserialize<'a>,
{
    let mut deserializer = Deserializer::new(values);
    let result = T::deserialize(&mut deserializer)?;

    match deserializer.iterator.peek() {
        None => Ok(result),
        _ => Err(DeserializeError::InputNotEmpty),
    }
}

/// The deserializer. The iterator iterates over `InterfaceValue`s,
/// all flatten, see `FlattenInterfaceValueIterator`.
struct Deserializer<'de> {
    iterator: Peekable<FlattenInterfaceValueIterator<'de>>,
}

impl<'de> Deserializer<'de> {
    pub fn new(input: &'de [InterfaceValue]) -> Deserializer<'de> {
        Deserializer {
            iterator: FlattenInterfaceValueIterator::new(input).peekable(),
        }
    }
}

macro_rules! next {
    ($method_name:ident, $variant:ident, $type:ty) => {
        fn $method_name(&mut self) -> Result<$type, DeserializeError> {
            match self.iterator.peek() {
                Some(InterfaceValue::$variant(value)) => {
                    self.iterator.next();

                    Ok(*value)
                }

                Some(wrong_value) => Err(DeserializeError::TypeMismatch {
                    expected_type: InterfaceType::$variant,
                    received_type: (*wrong_value).into(),
                }),

                None => Err(DeserializeError::InputEmpty),
            }
        }
    }
}

impl<'de> Deserializer<'de> {
    next!(next_s8, S8, i8);
    next!(next_s16, S16, i16);
    next!(next_s32, S32, i32);
    next!(next_s64, S64, i64);
    next!(next_u8, U8, u8);
    next!(next_u16, U16, u16);
    next!(next_u32, U32, u32);
    next!(next_u64, U64, u64);
    next!(next_f32, F32, f32);
    next!(next_f64, F64, f64);

    fn next_string(&mut self) -> Result<&'de str, DeserializeError> {
        match self.iterator.peek() {
            Some(InterfaceValue::String(v)) => {
                self.iterator.next();

                Ok(v)
            }

            Some(wrong_value) => Err(DeserializeError::TypeMismatch {
                expected_type: InterfaceType::String,
                received_type: (*wrong_value).into(),
            }),

            None => Err(DeserializeError::InputEmpty),
        }
    }

    next!(next_i32, I32, i32);
    next!(next_i64, I64, i64);
}

/// Represents an error while deserializing.
#[derive(Clone, Debug, PartialEq)]
pub enum DeserializeError {
    /// The input isn't empty, i.e. some values aren't deserialized.
    InputNotEmpty,

    /// The input is too short!
    InputEmpty,

    /// The current value hasn't the expected type.
    TypeMismatch {
        /// The expected type.
        expected_type: InterfaceType,

        /// The received type.
        received_type: InterfaceType,
    },

    /// Arbitrary message.
    Message(String),
}

impl de::Error for DeserializeError {
    fn custom<T: Display>(msg: T) -> Self {
        Self::Message(msg.to_string())
    }
}

impl Display for DeserializeError {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::InputNotEmpty => write!(formatter, "Unexpected input remaining"),
            Self::Message(ref msg) => write!(formatter, "{}", msg),
            Self::InputEmpty => write!(formatter, "Unexpected end of input"),
            Self::TypeMismatch {
                ref expected_type,
                ref received_type,
            } => write!(
                formatter,
                "Type mismatch detected, expected `{:?}` but received `{:?}`",
                expected_type, received_type
            ),
        }
    }
}

impl std::error::Error for DeserializeError {}

impl<'de, 'a> de::Deserializer<'de> for &'a mut Deserializer<'de> {
    type Error = DeserializeError;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        match self.iterator.peek() {
            Some(InterfaceValue::S8(_)) => self.deserialize_i8(visitor),
            Some(InterfaceValue::S16(_)) => self.deserialize_i16(visitor),
            Some(InterfaceValue::S32(_)) => self.deserialize_i32(visitor),
            Some(InterfaceValue::S64(_)) => self.deserialize_i64(visitor),
            Some(InterfaceValue::U8(_)) => self.deserialize_u8(visitor),
            Some(InterfaceValue::U16(_)) => self.deserialize_u16(visitor),
            Some(InterfaceValue::U32(_)) => self.deserialize_u32(visitor),
            Some(InterfaceValue::U64(_)) => self.deserialize_u64(visitor),
            Some(InterfaceValue::F32(_)) => self.deserialize_f32(visitor),
            Some(InterfaceValue::F64(_)) => self.deserialize_f64(visitor),
            Some(InterfaceValue::String(_)) => self.deserialize_string(visitor),
            Some(InterfaceValue::I32(_)) => self.deserialize_i32(visitor),
            Some(InterfaceValue::I64(_)) => self.deserialize_i64(visitor),
            Some(InterfaceValue::Record(_)) => unreachable!("Records should have been flattened."), // already flattened
            None => Err(DeserializeError::InputEmpty),
        }
    }

    fn deserialize_bool<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        unimplemented!("`bool` is not supported by WIT for the moment.")
    }

    fn deserialize_i8<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_i8(self.next_s8()?)
    }

    fn deserialize_i16<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_i16(self.next_s16()?)
    }

    fn deserialize_i32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        // Both `InterfaceValue::S32` and `InterfaceValue::I32`
        // represent `i32`.
        visitor.visit_i32(self.next_s32().or_else(|_| self.next_i32())?)
    }

    fn deserialize_i64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        // Both `InterfaceValue::S64` and `InterfaceValue::I64`
        // represent `i64`.
        visitor.visit_i64(self.next_s64().or_else(|_| self.next_i64())?)
    }

    fn deserialize_u8<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_u8(self.next_u8()?)
    }

    fn deserialize_u16<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_u16(self.next_u16()?)
    }

    fn deserialize_u32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_u32(self.next_u32()?)
    }

    fn deserialize_u64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_u64(self.next_u64()?)
    }

    fn deserialize_f32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_f32(self.next_f32()?)
    }

    fn deserialize_f64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_f64(self.next_f64()?)
    }

    fn deserialize_char<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        todo!("`char` is not supported by WIT for the moment.")
    }

    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_borrowed_str(self.next_string()?)
    }

    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        self.deserialize_str(visitor)
    }

    fn deserialize_bytes<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        todo!("`bytes` is not supported by WIT for the moment.")
    }

    fn deserialize_byte_buf<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        todo!("`bytes` buffer is not supported by WIT for the moment.")
    }

    fn deserialize_option<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        todo!("`option` is not supported by WIT for the moment.")
    }

    fn deserialize_unit<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        todo!("`unit` is not supported by WIT for the moment.")
    }

    fn deserialize_unit_struct<V>(
        self,
        _name: &'static str,
        _visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        todo!("`unit_struct` is not supported by WIT for the moment.")
    }

    fn deserialize_newtype_struct<V>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_newtype_struct(self)
    }

    fn deserialize_seq<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        todo!("`seq` is not supported by WIT for the moment.")
    }

    fn deserialize_tuple<V>(self, _len: usize, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        todo!("`tuple` is not supported by WIT for the moment.")
    }

    fn deserialize_tuple_struct<V>(
        mut self,
        _name: &'static str,
        _len: usize,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_seq(Sequence::new(&mut self))
    }

    fn deserialize_map<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        todo!("`map` is not supported by WIT for the moment.")
    }

    fn deserialize_struct<V>(
        mut self,
        _name: &'static str,
        _fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_seq(Sequence::new(&mut self))
    }

    fn deserialize_enum<V>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        _visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        todo!("`enum` is not supported by WIT for the moment.")
    }

    fn deserialize_identifier<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        todo!("`identifier` is not supported by WIT for the moment.");
    }

    fn deserialize_ignored_any<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        todo!("`ignored_any` is not implemented for the moment.")
    }
}

struct Sequence<'a, 'de>
where
    'de: 'a,
{
    de: &'a mut Deserializer<'de>,
}

impl<'a, 'de> Sequence<'a, 'de> {
    fn new(de: &'a mut Deserializer<'de>) -> Self {
        Sequence { de }
    }
}

impl<'de, 'a> de::SeqAccess<'de> for Sequence<'a, 'de> {
    type Error = DeserializeError;

    fn next_element_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>, Self::Error>
    where
        T: de::DeserializeSeed<'de>,
    {
        if self.de.iterator.peek().is_none() {
            return Ok(None);
        }

        seed.deserialize(&mut *self.de).map(Some)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! deserialize_value {
        ($test_name:ident, $variant:ident, $ty:ident, $value:expr) => {
            #[test]
            #[allow(non_snake_case)]
            fn $test_name() {
                let input = vec![InterfaceValue::$variant($value)];
                let output: $ty = $value;

                assert_eq!(from_interface_values::<$ty>(&input).unwrap(), output);
            }
        };
    }

    deserialize_value!(test_deserialize_value__s8, S8, i8, 42);
    deserialize_value!(test_deserialize_value__s16, S16, i16, 42);
    deserialize_value!(test_deserialize_value__s32, S32, i32, 42);
    deserialize_value!(test_deserialize_value__s64, S64, i64, 42);
    deserialize_value!(test_deserialize_value__u8, U8, u8, 42);
    deserialize_value!(test_deserialize_value__u16, U16, u16, 42);
    deserialize_value!(test_deserialize_value__u32, U32, u32, 42);
    deserialize_value!(test_deserialize_value__u64, U64, u64, 42);
    deserialize_value!(test_deserialize_value__f32, F32, f32, 42.);
    deserialize_value!(test_deserialize_value__f64, F32, f32, 42.);
    deserialize_value!(
        test_deserialize_value__string,
        String,
        String,
        "foo".to_string()
    );

    #[test]
    #[allow(non_snake_case)]
    fn test_deserialize_value__str() {
        let foo = "foo".to_string();
        let values = vec![InterfaceValue::String(foo)];
        let input: &str = from_interface_values(&values).unwrap();
        let output: &str = "foo";

        assert_eq!(input, output);
    }

    deserialize_value!(test_deserialize_value__i32, I32, i32, 42);
    deserialize_value!(test_deserialize_value__i64, I64, i64, 42);

    #[test]
    #[allow(non_snake_case)]
    fn test_deserialize_value__newtype_struct() {
        #[derive(Deserialize, Debug, PartialEq)]
        struct S(i8);

        let input = vec![InterfaceValue::Record(vec1![InterfaceValue::S8(42)])];
        let output = S(42);

        assert_eq!(from_interface_values::<S>(&input).unwrap(), output);
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_deserialize_value__tuple_struct() {
        #[derive(Deserialize, Debug, PartialEq)]
        struct S(i8, f32);

        let input = vec![InterfaceValue::Record(vec1![
            InterfaceValue::S8(7),
            InterfaceValue::F32(42.),
        ])];
        let output = S(7, 42.);

        assert_eq!(from_interface_values::<S>(&input).unwrap(), output);
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_deserialize_value__struct() {
        #[derive(Deserialize, Debug, PartialEq)]
        struct S {
            x: i8,
            y: f32,
        }

        let input = vec![InterfaceValue::Record(vec1![
            InterfaceValue::S8(7),
            InterfaceValue::F32(42.),
        ])];
        let output = S { x: 7, y: 42. };

        assert_eq!(from_interface_values::<S>(&input).unwrap(), output);
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_deserialize_value__struct_nested() {
        #[derive(Deserialize, Debug, PartialEq)]
        struct Point {
            x: i32,
            y: i32,
            z: i32,
        }

        #[derive(Deserialize, Debug, PartialEq)]
        struct Line {
            p1: Point,
            p2: Point,
        }

        let input = vec![InterfaceValue::Record(vec1![
            InterfaceValue::Record(vec1![
                InterfaceValue::I32(1),
                InterfaceValue::I32(2),
                InterfaceValue::I32(3),
            ]),
            InterfaceValue::Record(vec1![
                InterfaceValue::I32(4),
                InterfaceValue::I32(5),
                InterfaceValue::I32(6),
            ]),
        ])];
        let output = Line {
            p1: Point { x: 1, y: 2, z: 3 },
            p2: Point { x: 4, y: 5, z: 6 },
        };

        assert_eq!(from_interface_values::<Line>(&input).unwrap(), output);
    }
}
