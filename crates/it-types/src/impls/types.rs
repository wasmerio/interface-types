use crate::ne_vec::NEVec;
use crate::IRecordFieldType;
use crate::IRecordType;
use crate::IType;

use wast::parser::Parse;
use wast::parser::Parser;
use wast::Error as ParseError;

mod keyword {
    pub use wast::{
        custom_keyword,
        kw::{anyref, export, f32, f64, func, i32, i64, import, param, result},
    };

    // New keywords.
    custom_keyword!(record);
    custom_keyword!(field);

    // New types.
    custom_keyword!(s8);
    custom_keyword!(s16);
    custom_keyword!(s32);
    custom_keyword!(s64);
    custom_keyword!(u8);
    custom_keyword!(u16);
    custom_keyword!(u32);
    custom_keyword!(u64);
    custom_keyword!(string);
    custom_keyword!(array);
}

impl Parse<'_> for IType {
    fn parse(parser: Parser<'_>) -> Result<IType, ParseError> {
        let mut lookahead = parser.lookahead1();
        if lookahead.peek::<keyword::s8>() {
            parser.parse::<keyword::s8>()?;

            Ok(IType::S8)
        } else if lookahead.peek::<keyword::s16>() {
            parser.parse::<keyword::s16>()?;

            Ok(IType::S16)
        } else if lookahead.peek::<keyword::s32>() {
            parser.parse::<keyword::s32>()?;

            Ok(IType::S32)
        } else if lookahead.peek::<keyword::s64>() {
            parser.parse::<keyword::s64>()?;

            Ok(IType::S64)
        } else if lookahead.peek::<keyword::u8>() {
            parser.parse::<keyword::u8>()?;

            Ok(IType::U8)
        } else if lookahead.peek::<keyword::u16>() {
            parser.parse::<keyword::u16>()?;

            Ok(IType::U16)
        } else if lookahead.peek::<keyword::u32>() {
            parser.parse::<keyword::u32>()?;

            Ok(IType::U32)
        } else if lookahead.peek::<keyword::u64>() {
            parser.parse::<keyword::u64>()?;

            Ok(IType::U64)
        } else if lookahead.peek::<keyword::f32>() {
            parser.parse::<keyword::f32>()?;

            Ok(IType::F32)
        } else if lookahead.peek::<keyword::f64>() {
            parser.parse::<keyword::f64>()?;

            Ok(IType::F64)
        } else if lookahead.peek::<keyword::string>() {
            parser.parse::<keyword::string>()?;

            Ok(IType::String)
        } else if lookahead.peek::<keyword::array>() {
            parser.parse::<keyword::array>()?;

            let array_type = parser.parens(|p| p.parse())?;

            Ok(IType::Array(Box::new(array_type)))
        } else if lookahead.peek::<keyword::anyref>() {
            parser.parse::<keyword::anyref>()?;

            Ok(IType::Anyref)
        } else if lookahead.peek::<keyword::i32>() {
            parser.parse::<keyword::i32>()?;

            Ok(IType::I32)
        } else if lookahead.peek::<keyword::i64>() {
            parser.parse::<keyword::i64>()?;

            Ok(IType::I64)
        } else if lookahead.peek::<keyword::record>() {
            parser.parse::<keyword::record>()?;

            Ok(IType::Record(parser.parse()?))
        } else {
            Err(lookahead.error())
        }
    }
}

impl Parse<'_> for IRecordType {
    fn parse(parser: Parser<'_>) -> Result<Self, ParseError> {
        parser.parse::<keyword::record>()?;

        let record_name = parser
            .step(|cursor| {
                cursor
                    .id()
                    .ok_or_else(|| cursor.error("expecting argument identifier"))
            })?
            .to_string();

        let mut fields = vec![];

        parser.parens(|parser| {
            while !parser.is_empty() {
                parser.parse::<keyword::field>()?;

                let name = parser
                    .step(|cursor| {
                        cursor
                            .id()
                            .ok_or_else(|| cursor.error("expecting argument identifier"))
                    })?
                    .to_string();

                if !name.ends_with(':') {
                    parser.step(|cursor| {
                        if let Some((":", rest)) = cursor.reserved() {
                            return Ok(("", rest));
                        }
                        Err(cursor.error("expected : between an argument and a type"))
                    })?;
                }

                let ty = parser.parse()?;
                let record_field_type = IRecordFieldType {
                    name: name.trim_end_matches(':').to_string(),
                    ty,
                };

                fields.push(record_field_type);
            }
            Ok(())
        })?;

        let record_type = IRecordType {
            name: record_name,
            fields: NEVec::new(fields).expect("Record must have at least one field, zero given."),
        };

        Ok(record_type)
    }
}
