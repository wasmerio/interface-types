//! Parse the WIT textual representation into an [AST](crate::ast).

use crate::{ast::*, interpreter::Instruction};
pub use wast::parser::ParseBuffer as Buffer;
use wast::parser::{self, Cursor, Parse, Parser, Peek, Result};

mod keyword {
    pub use wast::{
        custom_keyword,
        kw::{anyref, export, f32, f64, func, i32, i64, import, param, result},
    };

    // New keywords.
    custom_keyword!(implement);
    custom_keyword!(r#type = "type");

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

    // Instructions.
    custom_keyword!(argument_get = "arg.get");
    custom_keyword!(call);
    custom_keyword!(call_export = "call-export");
    custom_keyword!(read_utf8 = "read-utf8");
    custom_keyword!(write_utf8 = "write-utf8");
    custom_keyword!(as_wasm = "as-wasm");
    custom_keyword!(as_interface = "as-interface");
    custom_keyword!(table_ref_add = "table-ref-add");
    custom_keyword!(table_ref_get = "table-ref-get");
    custom_keyword!(call_method = "call-method");
    custom_keyword!(make_record = "make-record");
    custom_keyword!(get_field = "get-field");
    custom_keyword!(r#const = "const");
    custom_keyword!(fold_seq = "fold-seq");
    custom_keyword!(add);
    custom_keyword!(mem_to_seq = "mem-to-seq");
    custom_keyword!(load);
    custom_keyword!(seq_new = "seq.new");
    custom_keyword!(list_push = "list.push");
    custom_keyword!(repeat_until = "repeat-until");
}

impl Parse<'_> for InterfaceType {
    fn parse(parser: Parser<'_>) -> Result<Self> {
        let mut lookahead = parser.lookahead1();

        if lookahead.peek::<keyword::s8>() {
            parser.parse::<keyword::s8>()?;

            Ok(InterfaceType::S8)
        } else if lookahead.peek::<keyword::s16>() {
            parser.parse::<keyword::s16>()?;

            Ok(InterfaceType::S16)
        } else if lookahead.peek::<keyword::s32>() {
            parser.parse::<keyword::s32>()?;

            Ok(InterfaceType::S32)
        } else if lookahead.peek::<keyword::s64>() {
            parser.parse::<keyword::s64>()?;

            Ok(InterfaceType::S64)
        } else if lookahead.peek::<keyword::u8>() {
            parser.parse::<keyword::u8>()?;

            Ok(InterfaceType::U8)
        } else if lookahead.peek::<keyword::u16>() {
            parser.parse::<keyword::u16>()?;

            Ok(InterfaceType::U16)
        } else if lookahead.peek::<keyword::u32>() {
            parser.parse::<keyword::u32>()?;

            Ok(InterfaceType::U32)
        } else if lookahead.peek::<keyword::u64>() {
            parser.parse::<keyword::u64>()?;

            Ok(InterfaceType::U64)
        } else if lookahead.peek::<keyword::f32>() {
            parser.parse::<keyword::f32>()?;

            Ok(InterfaceType::F32)
        } else if lookahead.peek::<keyword::f64>() {
            parser.parse::<keyword::f64>()?;

            Ok(InterfaceType::F64)
        } else if lookahead.peek::<keyword::string>() {
            parser.parse::<keyword::string>()?;

            Ok(InterfaceType::String)
        } else if lookahead.peek::<keyword::string>() {
            parser.parse::<keyword::string>()?;

            Ok(InterfaceType::String)
        } else if lookahead.peek::<keyword::anyref>() {
            parser.parse::<keyword::anyref>()?;

            Ok(InterfaceType::Anyref)
        } else if lookahead.peek::<keyword::i32>() {
            parser.parse::<keyword::i32>()?;

            Ok(InterfaceType::I32)
        } else if lookahead.peek::<keyword::i64>() {
            parser.parse::<keyword::i64>()?;

            Ok(InterfaceType::I64)
        } else {
            Err(lookahead.error())
        }
    }
}

impl<'a> Parse<'a> for Instruction<'a> {
    fn parse(parser: Parser<'a>) -> Result<Self> {
        let mut lookahead = parser.lookahead1();

        if lookahead.peek::<keyword::argument_get>() {
            parser.parse::<keyword::argument_get>()?;

            Ok(Instruction::ArgumentGet {
                index: parser.parse()?,
            })
        } else if lookahead.peek::<keyword::call>() {
            parser.parse::<keyword::call>()?;

            Ok(Instruction::Call {
                function_index: parser.parse::<u64>()? as usize,
            })
        } else if lookahead.peek::<keyword::call_export>() {
            parser.parse::<keyword::call_export>()?;

            Ok(Instruction::CallExport {
                export_name: parser.parse()?,
            })
        } else if lookahead.peek::<keyword::read_utf8>() {
            parser.parse::<keyword::read_utf8>()?;

            Ok(Instruction::ReadUtf8)
        } else if lookahead.peek::<keyword::write_utf8>() {
            parser.parse::<keyword::write_utf8>()?;

            Ok(Instruction::WriteUtf8 {
                allocator_name: parser.parse()?,
            })
        } else {
            Err(lookahead.error())
        }
    }
}

struct AtInterface;

impl Peek for AtInterface {
    fn peek(cursor: Cursor<'_>) -> bool {
        cursor.reserved().map(|(string, _)| string) == Some("@interface")
    }

    fn display() -> &'static str {
        "`@interface`"
    }
}

impl Parse<'_> for AtInterface {
    fn parse(parser: Parser<'_>) -> Result<Self> {
        parser.step(|cursor| {
            if let Some(("@interface", rest)) = cursor.reserved() {
                return Ok((AtInterface, rest));
            }

            Err(cursor.error("expected `@interface`"))
        })
    }
}

#[derive(PartialEq, Debug)]
enum FunctionType {
    Input(Vec<InterfaceType>),
    Output(Vec<InterfaceType>),
}

impl Parse<'_> for FunctionType {
    fn parse(parser: Parser<'_>) -> Result<Self> {
        parser.parens(|parser| {
            let mut lookahead = parser.lookahead1();

            if lookahead.peek::<keyword::param>() {
                parser.parse::<keyword::param>()?;

                let mut inputs = vec![];

                while !parser.is_empty() {
                    inputs.push(parser.parse()?);
                }

                Ok(FunctionType::Input(inputs))
            } else if lookahead.peek::<keyword::result>() {
                parser.parse::<keyword::result>()?;

                let mut outputs = vec![];

                while !parser.is_empty() {
                    outputs.push(parser.parse()?);
                }

                Ok(FunctionType::Output(outputs))
            } else {
                Err(lookahead.error())
            }
        })
    }
}

#[derive(PartialEq, Debug)]
enum Interface<'a> {
    Type(Type),
    Import(Import<'a>),
    Adapter(Adapter<'a>),
    Export(Export<'a>),
    Implementation(Implementation),
}

impl<'a> Parse<'a> for Interface<'a> {
    fn parse(parser: Parser<'a>) -> Result<Self> {
        parser.parens(|parser| {
            let mut lookahead = parser.lookahead1();

            if lookahead.peek::<AtInterface>() {
                parser.parse::<AtInterface>()?;

                let mut lookahead = parser.lookahead1();

                if lookahead.peek::<keyword::r#type>() {
                    Ok(Interface::Type(parser.parse()?))
                } else if lookahead.peek::<keyword::import>() {
                    Ok(Interface::Import(parser.parse()?))
                } else if lookahead.peek::<keyword::func>() {
                    Ok(Interface::Adapter(parser.parse()?))
                } else if lookahead.peek::<keyword::export>() {
                    Ok(Interface::Export(parser.parse()?))
                } else if lookahead.peek::<keyword::implement>() {
                    Ok(Interface::Implementation(parser.parse()?))
                } else {
                    Err(lookahead.error())
                }
            } else {
                Err(lookahead.error())
            }
        })
    }
}

impl<'a> Parse<'a> for Type {
    fn parse(parser: Parser<'a>) -> Result<Self> {
        parser.parse::<keyword::r#type>()?;

        let (inputs, outputs) = parser.parens(|parser| {
            parser.parse::<keyword::func>()?;

            let mut input_types = vec![];
            let mut output_types = vec![];

            while !parser.is_empty() {
                let function_type = parser.parse::<FunctionType>()?;

                match function_type {
                    FunctionType::Input(mut inputs) => input_types.append(&mut inputs),
                    FunctionType::Output(mut outputs) => output_types.append(&mut outputs),
                }
            }

            Ok((input_types, output_types))
        })?;

        Ok(Type { inputs, outputs })
    }
}

impl<'a> Parse<'a> for Import<'a> {
    fn parse(parser: Parser<'a>) -> Result<Self> {
        parser.parse::<keyword::import>()?;

        let namespace = parser.parse()?;
        let name = parser.parse()?;

        let signature_type = parser.parens(|parser| {
            parser.parse::<keyword::func>()?;

            parser.parens(|parser| {
                parser.parse::<keyword::r#type>()?;

                parser.parse()
            })
        })?;

        Ok(Import {
            namespace,
            name,
            signature_type,
        })
    }
}

impl<'a> Parse<'a> for Export<'a> {
    fn parse(parser: Parser<'a>) -> Result<Self> {
        parser.parse::<keyword::export>()?;

        let name = parser.parse()?;

        let function_type = parser.parens(|parser| {
            parser.parse::<keyword::func>()?;

            parser.parse()
        })?;

        Ok(Export {
            name,
            function_type,
        })
    }
}

impl<'a> Parse<'a> for Implementation {
    fn parse(parser: Parser<'a>) -> Result<Self> {
        parser.parse::<keyword::implement>()?;

        let core_function_type = parser.parens(|parser| {
            parser.parse::<keyword::func>()?;

            parser.parse()
        })?;

        let adapter_function_type = parser.parens(|parser| {
            parser.parse::<keyword::func>()?;

            parser.parse()
        })?;

        Ok(Implementation {
            core_function_type,
            adapter_function_type,
        })
    }
}

impl<'a> Parse<'a> for Adapter<'a> {
    fn parse(parser: Parser<'a>) -> Result<Self> {
        parser.parse::<keyword::func>()?;

        let function_type = parser.parens(|parser| {
            parser.parse::<keyword::r#type>()?;

            parser.parse()
        })?;

        let mut instructions = vec![];

        while !parser.is_empty() {
            instructions.push(parser.parse()?);
        }

        Ok(Adapter {
            function_type,
            instructions,
        })
    }
}

impl<'a> Parse<'a> for Interfaces<'a> {
    fn parse(parser: Parser<'a>) -> Result<Self> {
        let mut interfaces: Interfaces = Default::default();

        while !parser.is_empty() {
            let interface = parser.parse::<Interface>()?;

            match interface {
                Interface::Type(ty) => interfaces.types.push(ty),
                Interface::Import(import) => interfaces.imports.push(import),
                Interface::Adapter(adapter) => interfaces.adapters.push(adapter),
                Interface::Export(export) => interfaces.exports.push(export),
                Interface::Implementation(implementation) => {
                    interfaces.implementations.push(implementation)
                }
            }
        }

        Ok(interfaces)
    }
}

/// Parse a WIT definition in its textual format, and produces an
/// [AST](crate::ast) with the [`Interfaces`](crate::ast::Interfaces)
/// structure upon succesful.
///
/// # Examples
///
/// ```rust
/// use wasmer_interface_types::{
///     ast::*,
///     decoders::wat::{parse, Buffer},
///     interpreter::Instruction,
/// };
///
/// # fn main() {
/// let input = Buffer::new(
///     r#"(@interface type (func (param i32) (result s8)))
///
/// (@interface import "ns" "foo" (func (type 0)))
///
/// (@interface func (type 0) arg.get 42)
///
/// (@interface export "bar" (func 0))
///
/// (@interface implement (func 0) (func 1))"#,
/// )
/// .unwrap();
/// let output = Interfaces {
///     types: vec![Type {
///         inputs: vec![InterfaceType::I32],
///         outputs: vec![InterfaceType::S8],
///     }],
///     imports: vec![Import {
///         namespace: "ns",
///         name: "foo",
///         signature_type: 0,
///     }],
///     adapters: vec![Adapter {
///         function_type: 0,
///         instructions: vec![Instruction::ArgumentGet { index: 42 }],
///     }],
///     exports: vec![Export {
///         name: "bar",
///         function_type: 0,
///     }],
///     implementations: vec![Implementation {
///         core_function_type: 0,
///         adapter_function_type: 1,
///     }],
/// };
///
/// assert_eq!(parse(&input).unwrap(), output);
/// # }
/// ```
pub fn parse<'input>(input: &'input Buffer) -> Result<Interfaces<'input>> {
    parser::parse::<Interfaces>(&input)
}

#[cfg(test)]
mod tests {
    use super::*;
    use wast::parser;

    fn buffer(input: &str) -> Buffer {
        Buffer::new(input).expect("Failed to build the parser buffer.")
    }

    #[test]
    fn test_interface_type() {
        let inputs = vec![
            "s8", "s16", "s32", "s64", "u8", "u16", "u32", "u64", "f32", "f64", "string", "anyref",
            "i32", "i64",
        ];
        let outputs = vec![
            InterfaceType::S8,
            InterfaceType::S16,
            InterfaceType::S32,
            InterfaceType::S64,
            InterfaceType::U8,
            InterfaceType::U16,
            InterfaceType::U32,
            InterfaceType::U64,
            InterfaceType::F32,
            InterfaceType::F64,
            InterfaceType::String,
            InterfaceType::Anyref,
            InterfaceType::I32,
            InterfaceType::I64,
        ];

        assert_eq!(inputs.len(), outputs.len());

        for (input, output) in inputs.iter().zip(outputs.iter()) {
            assert_eq!(
                &parser::parse::<InterfaceType>(&buffer(input)).unwrap(),
                output
            );
        }
    }

    #[test]
    fn test_instructions() {
        let inputs = vec![
            "arg.get 7",
            "call 7",
            r#"call-export "foo""#,
            "read-utf8",
            r#"write-utf8 "foo""#,
        ];
        let outputs = vec![
            Instruction::ArgumentGet { index: 7 },
            Instruction::Call { function_index: 7 },
            Instruction::CallExport { export_name: "foo" },
            Instruction::ReadUtf8,
            Instruction::WriteUtf8 {
                allocator_name: "foo",
            },
        ];

        assert_eq!(inputs.len(), outputs.len());

        for (input, output) in inputs.iter().zip(outputs.iter()) {
            assert_eq!(
                &parser::parse::<Instruction>(&buffer(input)).unwrap(),
                output
            );
        }
    }

    #[test]
    fn test_param_empty() {
        let input = buffer("(param)");
        let output = FunctionType::Input(vec![]);

        assert_eq!(parser::parse::<FunctionType>(&input).unwrap(), output);
    }

    #[test]
    fn test_param() {
        let input = buffer("(param i32 string)");
        let output = FunctionType::Input(vec![InterfaceType::I32, InterfaceType::String]);

        assert_eq!(parser::parse::<FunctionType>(&input).unwrap(), output);
    }

    #[test]
    fn test_result_empty() {
        let input = buffer("(result)");
        let output = FunctionType::Output(vec![]);

        assert_eq!(parser::parse::<FunctionType>(&input).unwrap(), output);
    }

    #[test]
    fn test_result() {
        let input = buffer("(result i32 string)");
        let output = FunctionType::Output(vec![InterfaceType::I32, InterfaceType::String]);

        assert_eq!(parser::parse::<FunctionType>(&input).unwrap(), output);
    }

    #[test]
    fn test_type() {
        let input = buffer(r#"(@interface type (func (param i32 i32) (result i32)))"#);
        let output = Interface::Type(Type {
            inputs: vec![InterfaceType::I32, InterfaceType::I32],
            outputs: vec![InterfaceType::I32],
        });

        assert_eq!(parser::parse::<Interface>(&input).unwrap(), output);
    }

    #[test]
    fn test_export() {
        let input = buffer(r#"(@interface export "foo" (func 0))"#);
        let output = Interface::Export(Export {
            name: "foo",
            function_type: 0,
        });

        assert_eq!(parser::parse::<Interface>(&input).unwrap(), output);
    }

    #[test]
    fn test_export_escaped_name() {
        let input = buffer(r#"(@interface export "fo\"o" (func 0))"#);
        let output = Interface::Export(Export {
            name: r#"fo"o"#,
            function_type: 0,
        });

        assert_eq!(parser::parse::<Interface>(&input).unwrap(), output);
    }

    #[test]
    fn test_import() {
        let input = buffer(r#"(@interface import "ns" "foo" (func (type 0)))"#);
        let output = Interface::Import(Import {
            namespace: "ns",
            name: "foo",
            signature_type: 0,
        });

        assert_eq!(parser::parse::<Interface>(&input).unwrap(), output);
    }

    #[test]
    fn test_adapter() {
        let input = buffer(r#"(@interface func (type 0) arg.get 42)"#);
        let output = Interface::Adapter(Adapter {
            function_type: 0,
            instructions: vec![Instruction::ArgumentGet { index: 42 }],
        });

        assert_eq!(parser::parse::<Interface>(&input).unwrap(), output);
    }

    #[test]
    fn test_implementation() {
        let input = buffer(r#"(@interface implement (func 0) (func 1))"#);
        let output = Interface::Implementation(Implementation {
            core_function_type: 0,
            adapter_function_type: 1,
        });

        assert_eq!(parser::parse::<Interface>(&input).unwrap(), output);
    }

    #[test]
    fn test_interfaces() {
        let input = buffer(
            r#"(@interface type (func (param i32) (result s8)))

(@interface import "ns" "foo" (func (type 0)))

(@interface func (type 0) arg.get 42)

(@interface export "bar" (func 0))

(@interface implement (func 0) (func 1))"#,
        );
        let output = Interfaces {
            types: vec![Type {
                inputs: vec![InterfaceType::I32],
                outputs: vec![InterfaceType::S8],
            }],
            imports: vec![Import {
                namespace: "ns",
                name: "foo",
                signature_type: 0,
            }],
            adapters: vec![Adapter {
                function_type: 0,
                instructions: vec![Instruction::ArgumentGet { index: 42 }],
            }],
            exports: vec![Export {
                name: "bar",
                function_type: 0,
            }],
            implementations: vec![Implementation {
                core_function_type: 0,
                adapter_function_type: 1,
            }],
        };

        assert_eq!(parser::parse::<Interfaces>(&input).unwrap(), output);
    }
}
