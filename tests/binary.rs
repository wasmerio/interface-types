use wasmer_interface_types::{
    ast::*, decoders::binary::parse, encoders::binary::ToBytes, interpreter::Instruction, types::*,
    vec1,
};

/// Tests an AST to binary, then binary to AST roundtrip.
#[test]
fn test_binary_encoding_decoding_roundtrip() {
    let original_ast = Interfaces {
        types: vec![
            Type::Function {
                inputs: vec![],
                outputs: vec![],
            },
            Type::Function {
                inputs: vec![IType::I32, IType::I32],
                outputs: vec![IType::S32],
            },
            Type::Record(RecordType {
                fields: vec1![IType::String, IType::I32],
            }),
        ],
        imports: vec![Import {
            namespace: "a",
            name: "b",
            function_type: 0,
        }],
        adapters: vec![Adapter {
            function_type: 0,
            instructions: vec![Instruction::ArgumentGet { index: 1 }],
        }],
        exports: vec![Export {
            name: "ab",
            function_type: 1,
        }],
        implementations: vec![Implementation {
            core_function_type: 0,
            adapter_function_type: 0,
        }],
    };

    let mut binary = vec![];

    original_ast
        .to_bytes(&mut binary)
        .expect("Failed to encode the AST.");

    let (remainder, ast) = parse::<()>(binary.as_slice()).expect("Failed to decode the AST.");

    assert!(remainder.is_empty());

    assert_eq!(original_ast, ast);
}
