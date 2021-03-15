//! Represents the WIT language as a tree. This is the central
//! representation of the language.

use crate::{interpreter::Instruction, IRecordType, IType};

use serde::Deserialize;
use serde::Serialize;
use std::rc::Rc;
use std::str;

/// Represents the kind of type.
#[derive(PartialEq, Eq, Debug, Clone, Hash, Serialize, Deserialize)]
pub enum TypeKind {
    /// A function type.
    Function,

    /// A record type.
    Record,
}

/// Represents the function argument type.
#[derive(PartialEq, Eq, Debug, Clone, Hash, Serialize, Deserialize)]
pub struct FunctionArg {
    /// A function argument name.
    pub name: String,

    /// A function argument type.
    pub ty: IType,
}

/// Represents a type.
#[derive(PartialEq, Eq, Debug, Clone, Hash, Serialize, Deserialize)]
pub enum Type {
    /// A function type, like:
    ///
    /// ```wasm,ignore
    /// (@interface type (func (param i32 i32) (result string)))
    /// ```
    Function {
        /// Types for the parameters (`(param (name i32))`).
        arguments: Rc<Vec<FunctionArg>>,

        /// Types for the results (`(result …)`).
        output_types: Rc<Vec<IType>>,
    },

    /// A record type, like:
    ///
    /// ```wasm,ignore
    /// (@interface type (record string i32))
    /// ```
    Record(Rc<IRecordType>),
}

/// Represents an imported function.
#[derive(PartialEq, Eq, Debug, Default, Clone, Hash)]
pub struct Import<'input> {
    /// The function namespace.
    pub namespace: &'input str,

    /// The function name.
    pub name: &'input str,

    /// The type signature.
    pub function_type: u32,
}

/// Represents an exported function signature.
#[derive(PartialEq, Eq, Debug, Default, Clone, Hash)]
pub struct Export<'input> {
    /// The export name.
    pub name: &'input str,

    /// The WIT function type being exported.
    pub function_type: u32,
}

/// Represents an adapter.
#[derive(PartialEq, Eq, Debug, Clone, Hash, Serialize, Deserialize)]
pub struct Adapter {
    /// The adapter function type.
    pub function_type: u32,

    /// The instructions.
    pub instructions: Vec<Instruction>,
}

/// Represents an implementation.
#[derive(PartialEq, Eq, Debug, Default, Clone, Hash, Serialize, Deserialize)]
pub struct Implementation {
    /// The core function type.
    pub core_function_type: u32,

    /// The adapter function type.
    pub adapter_function_type: u32,
}

/// Represents the kind of interface.
#[derive(PartialEq, Eq, Debug, Clone, Hash, Serialize, Deserialize)]
pub enum InterfaceKind {
    /// A version.
    Version,

    /// A type.
    Type,

    /// An imported function.
    Import,

    /// An adapter.
    Adapter,

    /// An exported function.
    Export,

    /// An implementation.
    Implementation,
}

/// Represents a set of interfaces, i.e. it entirely describes a WIT
/// definition.
#[derive(PartialEq, Eq, Debug, Clone, Hash)]
pub struct Interfaces<'input> {
    /// Version of IT.
    pub version: semver::Version,

    /// All the types.
    pub types: Vec<Type>,

    /// All the imported functions.
    pub imports: Vec<Import<'input>>,

    /// All the adapters.
    pub adapters: Vec<Adapter>,

    /// All the exported functions.
    pub exports: Vec<Export<'input>>,

    /// All the implementations.
    pub implementations: Vec<Implementation>,
}
