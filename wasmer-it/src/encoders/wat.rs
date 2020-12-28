//! Writes the AST into a string representing WIT with its textual format.
//!
//! # Example
//!
//! ```rust
//! use wasmer_interface_types::{
//!     ast::{Adapter, Export, Implementation, Import, Interfaces, Type},
//!     encoders::wat::*,
//!     interpreter::Instruction,
//!     types::IType,
//! };
//!
//! let input: String = (&Interfaces {
//!     types: vec![Type::Function {
//!         inputs: vec![IType::I32],
//!         outputs: vec![IType::S8],
//!     }],
//!     imports: vec![Import {
//!         namespace: "ns",
//!         name: "foo",
//!         function_type: 0,
//!     }],
//!     adapters: vec![Adapter {
//!         function_type: 0,
//!         instructions: vec![Instruction::ArgumentGet { index: 42 }],
//!     }],
//!     exports: vec![Export {
//!         name: "bar",
//!         function_type: 0,
//!     }],
//!     implementations: vec![Implementation {
//!         core_function_type: 0,
//!         adapter_function_type: 1,
//!     }],
//! })
//!     .to_string();
//! let output = r#";; Types
//! (@interface type (func
//!   (param i32)
//!   (result s8)))
//!
//! ;; Imports
//! (@interface import "ns" "foo" (func (type 0)))
//!
//! ;; Adapters
//! (@interface func (type 0)
//!   arg.get 42)
//!
//! ;; Exports
//! (@interface export "bar" (func 0))
//!
//! ;; Implementations
//! (@interface implement (func 0) (func 1))"#;
//!
//! assert_eq!(input, output);
//! ```

use crate::IType;
use crate::{ast::*, interpreter::Instruction};
use std::string::ToString;

/// Encode an `Instruction` into a string.
impl ToString for &Instruction {
    fn to_string(&self) -> String {
        match self {
            Instruction::ArgumentGet { index } => format!("arg.get {}", index),
            Instruction::CallCore { function_index } => format!("call-core {}", function_index),
            Instruction::S8FromI32 => "s8.from_i32".into(),
            Instruction::S8FromI64 => "s8.from_i64".into(),
            Instruction::S16FromI32 => "s16.from_i32".into(),
            Instruction::S16FromI64 => "s16.from_i64".into(),
            Instruction::S32FromI32 => "s32.from_i32".into(),
            Instruction::S32FromI64 => "s32.from_i64".into(),
            Instruction::S64FromI32 => "s64.from_i32".into(),
            Instruction::S64FromI64 => "s64.from_i64".into(),
            Instruction::I32FromS8 => "i32.from_s8".into(),
            Instruction::I32FromS16 => "i32.from_s16".into(),
            Instruction::I32FromS32 => "i32.from_s32".into(),
            Instruction::I32FromS64 => "i32.from_s64".into(),
            Instruction::I64FromS8 => "i64.from_s8".into(),
            Instruction::I64FromS16 => "i64.from_s16".into(),
            Instruction::I64FromS32 => "i64.from_s32".into(),
            Instruction::I64FromS64 => "i64.from_s64".into(),
            Instruction::U8FromI32 => "u8.from_i32".into(),
            Instruction::U8FromI64 => "u8.from_i64".into(),
            Instruction::U16FromI32 => "u16.from_i32".into(),
            Instruction::U16FromI64 => "u16.from_i64".into(),
            Instruction::U32FromI32 => "u32.from_i32".into(),
            Instruction::U32FromI64 => "u32.from_i64".into(),
            Instruction::U64FromI32 => "u64.from_i32".into(),
            Instruction::U64FromI64 => "u64.from_i64".into(),
            Instruction::I32FromU8 => "i32.from_u8".into(),
            Instruction::I32FromU16 => "i32.from_u16".into(),
            Instruction::I32FromU32 => "i32.from_u32".into(),
            Instruction::I32FromU64 => "i32.from_u64".into(),
            Instruction::I64FromU8 => "i64.from_u8".into(),
            Instruction::I64FromU16 => "i64.from_u16".into(),
            Instruction::I64FromU32 => "i64.from_u32".into(),
            Instruction::I64FromU64 => "i64.from_u64".into(),
            Instruction::StringLiftMemory => "string.lift_memory".into(),
            Instruction::StringLowerMemory => "string.lower_memory".into(),
            Instruction::StringSize => "string.size".into(),
            Instruction::ArrayLiftMemory { value_type } => {
                format!("array.lift_memory {}", value_type.to_string())
            }
            Instruction::ArrayLowerMemory { value_type } => {
                format!("array.lower_memory {}", value_type.to_string())
            }
            /*
            Instruction::ArraySize => "byte_array.size".into(),
            Instruction::RecordLift { type_index } => format!("record.lift {}", type_index),
            Instruction::RecordLower { type_index } => format!("record.lower {}", type_index),
             */
            Instruction::RecordLiftMemory {
                record_type_id: type_index,
            } => format!("record.lift_memory {}", type_index),
            Instruction::RecordLowerMemory {
                record_type_id: type_index,
            } => format!("record.lower_memory {}", type_index),
            Instruction::Dup => "dup".into(),
            Instruction::Swap2 => "swap2".into(),
        }
    }
}

/// Encode a list of `IType` representing inputs into a
/// string.
fn encode_function_arguments(arguments: &[FunctionArg]) -> String {
    // here we know that arg_names and arg_types have the same length
    if arguments.is_empty() {
        String::from("")
    } else {
        format!(
            "\n  (param{})",
            arguments.iter().fold(
                String::new(),
                |mut accumulator, FunctionArg { name, ty }| {
                    accumulator.push_str(" $");
                    accumulator.push_str(name);
                    accumulator.push_str(": ");
                    accumulator.push_str(&ty.to_string());
                    accumulator
                }
            )
        )
    }
}

/// Encode a list of `IType` representing outputs into a
/// string.
fn output_types_to_result(output_types: &[IType]) -> String {
    if output_types.is_empty() {
        "".into()
    } else {
        format!(
            "\n  (result{})",
            output_types
                .iter()
                .fold(String::new(), |mut accumulator, interface_type| {
                    accumulator.push(' ');
                    accumulator.push_str(&interface_type.to_string());
                    accumulator
                })
        )
    }
}

/// Encode a `Type` into a string.
impl<'input> ToString for &Type {
    fn to_string(&self) -> String {
        match self {
            Type::Function {
                arguments,
                output_types,
            } => format!(
                r#"(@interface type (func {args} {output_types}))"#,
                args = encode_function_arguments(arguments),
                output_types = output_types_to_result(&output_types),
            ),

            Type::Record(record_type) => format!(
                r#"(@interface type ({record_type}))"#,
                record_type = record_type.as_ref().to_string(),
            ),
        }
    }
}

/// Encode an `Import` into a string.
impl<'input> ToString for &Import<'input> {
    fn to_string(&self) -> String {
        format!(
            r#"(@interface import "{namespace}" "{name}" (func (type {type})))"#,
            namespace = self.namespace,
            name = self.name,
            type = self.function_type,
        )
    }
}

/// Encode an `Adapter` into a string.
impl ToString for &Adapter {
    fn to_string(&self) -> String {
        format!(
            r#"(@interface func (type {function_type}){instructions})"#,
            function_type = self.function_type,
            instructions =
                self.instructions
                    .iter()
                    .fold(String::new(), |mut accumulator, instruction| {
                        accumulator.push_str("\n  ");
                        accumulator.push_str(&instruction.to_string());
                        accumulator
                    }),
        )
    }
}

/// Encode an `Export` into a string.
impl<'input> ToString for &Export<'input> {
    fn to_string(&self) -> String {
        format!(
            r#"(@interface export "{name}" (func {type}))"#,
            name = self.name,
            type = self.function_type,
        )
    }
}

/// Encode an `Implementation` into a string.
impl<'input> ToString for &Implementation {
    fn to_string(&self) -> String {
        format!(
            r#"(@interface implement (func {core_function_type}) (func {adapter_function_type}))"#,
            core_function_type = self.core_function_type,
            adapter_function_type = self.adapter_function_type,
        )
    }
}

/// Encode an `Interfaces` into a string.
impl<'input> ToString for &Interfaces<'input> {
    fn to_string(&self) -> String {
        let mut output = String::new();

        let types =
            self.types
                .iter()
                .enumerate()
                .fold(String::new(), |mut accumulator, (id, ty)| {
                    accumulator.push('\n');
                    accumulator.push_str(&ty.to_string());
                    accumulator.push_str(&format!("   ;; {}", id));
                    accumulator
                });

        let imports = self
            .imports
            .iter()
            .fold(String::new(), |mut accumulator, import| {
                accumulator.push('\n');
                accumulator.push_str(&import.to_string());
                accumulator
            });

        let adapters = self
            .adapters
            .iter()
            .fold(String::new(), |mut accumulator, adapter| {
                accumulator.push('\n');
                accumulator.push_str(&adapter.to_string());
                accumulator
            });

        let exports = self
            .exports
            .iter()
            .fold(String::new(), |mut accumulator, export| {
                accumulator.push('\n');
                accumulator.push_str(&export.to_string());
                accumulator
            });

        let implementations =
            self.implementations
                .iter()
                .fold(String::new(), |mut accumulator, implementation| {
                    accumulator.push('\n');
                    accumulator.push_str(&implementation.to_string());
                    accumulator
                });

        let separator = |output: &mut String| {
            if !output.is_empty() {
                output.push_str("\n\n");
            }
        };

        if !types.is_empty() {
            output.push_str(";; Types");
            output.push_str(&types);
        }

        separator(&mut output);

        if !imports.is_empty() {
            output.push_str(";; Imports");
            output.push_str(&imports);
        }

        separator(&mut output);

        if !adapters.is_empty() {
            output.push_str(";; Adapters");
            output.push_str(&adapters);
        }

        separator(&mut output);

        if !exports.is_empty() {
            output.push_str(";; Exports");
            output.push_str(&exports);
        }

        separator(&mut output);

        if !implementations.is_empty() {
            output.push_str(";; Implementations");
            output.push_str(&implementations);
        }

        output
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_interface_types() {
        let inputs: Vec<String> = vec![
            (&IType::S8).to_string(),
            (&IType::S16).to_string(),
            (&IType::S32).to_string(),
            (&IType::S64).to_string(),
            (&IType::U8).to_string(),
            (&IType::U16).to_string(),
            (&IType::U32).to_string(),
            (&IType::U64).to_string(),
            (&IType::F32).to_string(),
            (&IType::F64).to_string(),
            (&IType::String).to_string(),
            (&IType::Anyref).to_string(),
            (&IType::I32).to_string(),
            (&IType::I64).to_string(),
            (&IType::Record(RecordType {
                fields: vec1![IType::String],
            }))
                .to_string(),
        ];
        let outputs = vec![
            "s8",
            "s16",
            "s32",
            "s64",
            "u8",
            "u16",
            "u32",
            "u64",
            "f32",
            "f64",
            "string",
            "anyref",
            "i32",
            "i64",
            "record (field string)",
        ];

        assert_eq!(inputs, outputs);
    }

    #[test]
    fn test_record_type() {
        let inputs = vec![
            (&RecordType {
                fields: vec1![IType::String],
            })
                .to_string(),
            (&RecordType {
                fields: vec1![IType::String, IType::I32],
            })
                .to_string(),
            (&RecordType {
                fields: vec1![
                    IType::String,
                    IType::Record(RecordType {
                        fields: vec1![IType::I32, IType::I32],
                    }),
                    IType::F64,
                ],
            })
                .to_string(),
        ];
        let outputs = vec![
            "record (field string)",
            "record (field string) (field i32)",
            "record (field string) (field record (field i32) (field i32)) (field f64)",
        ];

        assert_eq!(inputs, outputs);
    }

    #[test]
    fn test_instructions() {
        let inputs: Vec<String> = vec![
            (&Instruction::ArgumentGet { index: 7 }).to_string(),
            (&Instruction::CallCore { function_index: 7 }).to_string(),
            (&Instruction::S8FromI32).to_string(),
            (&Instruction::S8FromI64).to_string(),
            (&Instruction::S16FromI32).to_string(),
            (&Instruction::S16FromI64).to_string(),
            (&Instruction::S32FromI32).to_string(),
            (&Instruction::S32FromI64).to_string(),
            (&Instruction::S64FromI32).to_string(),
            (&Instruction::S64FromI64).to_string(),
            (&Instruction::I32FromS8).to_string(),
            (&Instruction::I32FromS16).to_string(),
            (&Instruction::I32FromS32).to_string(),
            (&Instruction::I32FromS64).to_string(),
            (&Instruction::I64FromS8).to_string(),
            (&Instruction::I64FromS16).to_string(),
            (&Instruction::I64FromS32).to_string(),
            (&Instruction::I64FromS64).to_string(),
            (&Instruction::U8FromI32).to_string(),
            (&Instruction::U8FromI64).to_string(),
            (&Instruction::U16FromI32).to_string(),
            (&Instruction::U16FromI64).to_string(),
            (&Instruction::U32FromI32).to_string(),
            (&Instruction::U32FromI64).to_string(),
            (&Instruction::U64FromI32).to_string(),
            (&Instruction::U64FromI64).to_string(),
            (&Instruction::I32FromU8).to_string(),
            (&Instruction::I32FromU16).to_string(),
            (&Instruction::I32FromU32).to_string(),
            (&Instruction::I32FromU64).to_string(),
            (&Instruction::I64FromU8).to_string(),
            (&Instruction::I64FromU16).to_string(),
            (&Instruction::I64FromU32).to_string(),
            (&Instruction::I64FromU64).to_string(),
            (&Instruction::StringLiftMemory).to_string(),
            (&Instruction::StringLowerMemory).to_string(),
            (&Instruction::StringSize).to_string(),
            /*
            (&Instruction::RecordLift { type_index: 42 }).to_string(),
            (&Instruction::RecordLower { type_index: 42 }).to_string(),
             */
        ];
        let outputs = vec![
            "arg.get 7",
            "call-core 7",
            "s8.from_i32",
            "s8.from_i64",
            "s16.from_i32",
            "s16.from_i64",
            "s32.from_i32",
            "s32.from_i64",
            "s64.from_i32",
            "s64.from_i64",
            "i32.from_s8",
            "i32.from_s16",
            "i32.from_s32",
            "i32.from_s64",
            "i64.from_s8",
            "i64.from_s16",
            "i64.from_s32",
            "i64.from_s64",
            "u8.from_i32",
            "u8.from_i64",
            "u16.from_i32",
            "u16.from_i64",
            "u32.from_i32",
            "u32.from_i64",
            "u64.from_i32",
            "u64.from_i64",
            "i32.from_u8",
            "i32.from_u16",
            "i32.from_u32",
            "i32.from_u64",
            "i64.from_u8",
            "i64.from_u16",
            "i64.from_u32",
            "i64.from_u64",
            "string.lift_memory",
            "string.lower_memory",
            "string.size",
            "record.lift 42",
            "record.lower 42",
        ];

        assert_eq!(inputs, outputs);
    }

    #[test]
    fn test_types() {
        let inputs: Vec<String> = vec![
            (&Type::Function {
                inputs: vec![IType::I32, IType::F32],
                outputs: vec![IType::I32],
            })
                .to_string(),
            (&Type::Function {
                inputs: vec![IType::I32],
                outputs: vec![],
            })
                .to_string(),
            (&Type::Function {
                inputs: vec![],
                outputs: vec![IType::I32],
            })
                .to_string(),
            (&Type::Function {
                inputs: vec![],
                outputs: vec![],
            })
                .to_string(),
            (&Type::Record(RecordType {
                fields: vec1![IType::String, IType::I32],
            }))
                .to_string(),
        ];
        let outputs = vec![
            r#"(@interface type (func
  (param i32 f32)
  (result i32)))"#,
            r#"(@interface type (func
  (param i32)))"#,
            r#"(@interface type (func
  (result i32)))"#,
            r#"(@interface type (func))"#,
            r#"(@interface type (record (field string) (field i32)))"#,
        ];

        assert_eq!(inputs, outputs);
    }

    #[test]
    fn test_exports() {
        let input = (&Export {
            name: "foo",
            function_type: 0,
        })
            .to_string();
        let output = r#"(@interface export "foo" (func 0))"#;

        assert_eq!(input, output);
    }

    #[test]
    fn test_imports() {
        let input = (&Import {
            namespace: "ns",
            name: "foo",
            function_type: 0,
        })
            .to_string();
        let output = r#"(@interface import "ns" "foo" (func (type 0)))"#;

        assert_eq!(input, output);
    }

    #[test]
    fn test_adapter() {
        let input = (&Adapter {
            function_type: 0,
            instructions: vec![Instruction::ArgumentGet { index: 42 }],
        })
            .to_string();
        let output = r#"(@interface func (type 0)
  arg.get 42)"#;

        assert_eq!(input, output);
    }

    #[test]
    fn test_interfaces() {
        let input: String = (&Interfaces {
            types: vec![Type::Function {
                inputs: vec![IType::I32],
                outputs: vec![IType::S8],
            }],
            imports: vec![Import {
                namespace: "ns",
                name: "foo",
                function_type: 0,
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
        })
            .to_string();
        let output = r#";; Types
(@interface type (func
  (param i32)
  (result s8)))

;; Imports
(@interface import "ns" "foo" (func (type 0)))

;; Adapters
(@interface func (type 0)
  arg.get 42)

;; Exports
(@interface export "bar" (func 0))

;; Implementations
(@interface implement (func 0) (func 1))"#;

        assert_eq!(input, output);
    }
}
