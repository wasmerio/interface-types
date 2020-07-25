mod utils;

use utils::read_from_instance_mem;
use utils::write_to_instance_mem;

// use crate::interpreter::wasm;

use crate::interpreter::instructions::to_native;
use crate::{
    ast::{Type, TypeKind},
    errors::{InstructionError, InstructionErrorKind},
    interpreter::{
        stack::{Stack, Stackable},
        Instruction,
    },
    types::{InterfaceType, RecordType},
    values::{FlattenInterfaceValueIterator, InterfaceValue},
    vec1::Vec1,
};

use std::collections::VecDeque;
use std::convert::TryInto;

/// Build an `InterfaceValue::Record` based on values on the stack.
///
/// To fill a record, every field `field_1` to `field_n` must get its
/// value from the stack with `value_1` to `value_n`. It is not
/// possible to use `Stack::pop` because the one-pass algorithm does
/// not know exactly the number of values to read from the stack
/// ahead-of-time, so `Stack::pop1` is used. It implies that values
/// are read one after the other from the stack, in a natural reverse
/// order, from `value_n` to `value_1`. Thus, the `values` vector must
/// be filled from the end to the beginning. It is not safely possible
/// to fill the `values` vector with empty values though (so that it
/// is possible to access to last positions). So a `VecDeque` type is
/// used: it is a double-ended queue.
fn record_lift_(
    stack: &mut Stack<InterfaceValue>,
    record_type: &RecordType,
) -> Result<InterfaceValue, InstructionErrorKind> {
    let length = record_type.fields.len();
    let mut values = VecDeque::with_capacity(length);
    for field in record_type.fields.iter().rev() {
        match field {
            InterfaceType::Record(record_type) => {
                values.push_front(record_lift_(stack, &record_type)?)
            }
            ty => {
                let value = stack.pop1().unwrap();
                let value_type = (&value).into();
                if ty != &value_type {
                    return Err(InstructionErrorKind::InvalidValueOnTheStack {
                        expected_type: ty.clone(),
                        received_type: value_type,
                    });
                }
                values.push_front(value)
            }
        }
    }
    Ok(InterfaceValue::Record(
        Vec1::new(values.into_iter().collect())
            .expect("Record must have at least one field, zero given"),
    ))
}

pub(crate) fn record_lift<Instance, Export, LocalImport, Memory, MemoryView>(
    type_index: u32,
    instruction: Instruction,
) -> crate::interpreter::ExecutableInstruction<Instance, Export, LocalImport, Memory, MemoryView>
where
    Export: crate::interpreter::wasm::structures::Export,
    LocalImport: crate::interpreter::wasm::structures::LocalImport,
    Memory: crate::interpreter::wasm::structures::Memory<MemoryView>,
    MemoryView: crate::interpreter::wasm::structures::MemoryView,
    Instance:
        crate::interpreter::wasm::structures::Instance<Export, LocalImport, Memory, MemoryView>,
{
    #[allow(unused_imports)]
    use crate::interpreter::stack::Stackable;
    Box::new({
        move |runtime| -> _ {
            let instance = &runtime.wasm_instance;
            let record_type = match instance.wit_type(type_index).ok_or_else(|| {
                InstructionError::new(
                    instruction,
                    InstructionErrorKind::TypeIsMissing { type_index },
                )
            })? {
                Type::Record(record_type) => record_type,
                Type::Function { .. } => {
                    return Err(InstructionError::new(
                        instruction,
                        InstructionErrorKind::InvalidTypeKind {
                            expected_kind: TypeKind::Record,
                            received_kind: TypeKind::Function,
                        },
                    ))
                }
            };
            let record = record_lift_(&mut runtime.stack, &record_type)
                .map_err(|k| InstructionError::new(instruction, k))?;
            runtime.stack.push(record);
            Ok(())
        }
    })
}

fn record_lift_memory_<'instance, Instance, Export, LocalImport, Memory, MemoryView>(
    instance: &'instance mut Instance,
    record_type: RecordType,
    offset: usize,
    size: usize,
    instruction: Instruction,
) -> Result<InterfaceValue, InstructionError>
where
    Export: crate::interpreter::wasm::structures::Export,
    LocalImport: crate::interpreter::wasm::structures::LocalImport,
    Memory: crate::interpreter::wasm::structures::Memory<MemoryView>,
    MemoryView: crate::interpreter::wasm::structures::MemoryView,
    Instance: crate::interpreter::wasm::structures::Instance<Export, LocalImport, Memory, MemoryView>
        + 'instance,
{
    let length = record_type.fields.len();
    let mut values = VecDeque::with_capacity(length);
    let data = read_from_instance_mem(instance, instruction, offset, size)?;
    // TODO: add error handling
    let data =
        safe_transmute::transmute_many::<u64, safe_transmute::SingleManyGuard>(&data).unwrap();

    let mut field_id = 0;
    for field in record_type.fields.0 {
        let value = data[field_id];
        match field {
            InterfaceType::S8 => {
                values.push_front(InterfaceValue::S8(value as _));
            }
            InterfaceType::S16 => {
                values.push_front(InterfaceValue::S16(value as _));
            }
            InterfaceType::S32 => {
                values.push_front(InterfaceValue::S32(value as _));
            }
            InterfaceType::S64 => {
                values.push_front(InterfaceValue::S64(value as _));
            }
            InterfaceType::I32 => {
                values.push_front(InterfaceValue::I32(value as _));
            }
            InterfaceType::I64 => {
                values.push_front(InterfaceValue::I64(value as _));
            }
            InterfaceType::U8 => {
                values.push_front(InterfaceValue::U8(value as _));
            }
            InterfaceType::U16 => {
                values.push_front(InterfaceValue::U16(value as _));
            }
            InterfaceType::U32 => {
                values.push_front(InterfaceValue::U32(value as _));
            }
            InterfaceType::U64 => {
                values.push_front(InterfaceValue::U64(value as _));
            }
            InterfaceType::F32 => {
                values.push_front(InterfaceValue::F32(value as _));
            }
            InterfaceType::F64 => {
                unsafe {
                    values.push_front(InterfaceValue::F64(std::mem::transmute::<u64, f64>(value)))
                };
            }
            InterfaceType::Anyref => {}
            InterfaceType::String => {
                let offset = value;
                field_id += 1;
                let size = data[field_id];

                let string_mem =
                    read_from_instance_mem(instance, instruction, offset as _, size as _)?;
                // TODO: check
                let string = String::from_utf8(string_mem).unwrap();

                utils::deallocate(instance, instruction, offset as _, size as _)?;

                values.push_front(InterfaceValue::String(string));
            }
            InterfaceType::ByteArray => {
                let offset = value;
                field_id += 1;
                let size = data[field_id];

                let byte_array =
                    read_from_instance_mem(instance, instruction, offset as _, size as _)?;

                values.push_front(InterfaceValue::ByteArray(byte_array));
            }
            InterfaceType::Record(record_type) => {
                let offset = value;
                field_id += 1;
                let size = data[field_id];

                values.push_front(record_lift_memory_(
                    instance,
                    record_type,
                    offset as _,
                    size as _,
                    instruction,
                )?)
            }
        }
        field_id += 1;
    }
    Ok(InterfaceValue::Record(
        Vec1::new(values.into_iter().collect())
            .expect("Record must have at least one field, zero given"),
    ))
}

pub(crate) fn record_lift_memory<Instance, Export, LocalImport, Memory, MemoryView>(
    type_index: u32,
    instruction: Instruction,
) -> crate::interpreter::ExecutableInstruction<Instance, Export, LocalImport, Memory, MemoryView>
where
    Export: crate::interpreter::wasm::structures::Export,
    LocalImport: crate::interpreter::wasm::structures::LocalImport,
    Memory: crate::interpreter::wasm::structures::Memory<MemoryView>,
    MemoryView: crate::interpreter::wasm::structures::MemoryView,
    Instance:
        crate::interpreter::wasm::structures::Instance<Export, LocalImport, Memory, MemoryView>,
{
    #[allow(unused_imports)]
    use crate::interpreter::stack::Stackable;
    Box::new({
        move |runtime| -> _ {
            let inputs = runtime.stack.pop(2).ok_or_else(|| {
                InstructionError::new(
                    instruction,
                    InstructionErrorKind::StackIsTooSmall { needed: 2 },
                )
            })?;

            let offset: usize = to_native::<i32>(&inputs[0], instruction)?
                .try_into()
                .map_err(|e| (e, "offset").into())
                .map_err(|k| InstructionError::new(instruction, k))?;
            let size: usize = to_native::<i32>(&inputs[1], instruction)?
                .try_into()
                .map_err(|e| (e, "size").into())
                .map_err(|k| InstructionError::new(instruction, k))?;

            // TODO: size = 0
            let instance = &mut runtime.wasm_instance;
            let record_type = match instance.wit_type(type_index).ok_or_else(|| {
                InstructionError::new(
                    instruction,
                    InstructionErrorKind::TypeIsMissing { type_index },
                )
            })? {
                Type::Record(record_type) => record_type.clone(),
                Type::Function { .. } => {
                    return Err(InstructionError::new(
                        instruction,
                        InstructionErrorKind::InvalidTypeKind {
                            expected_kind: TypeKind::Record,
                            received_kind: TypeKind::Function,
                        },
                    ))
                }
            };

            let record = record_lift_memory_(*instance, record_type, offset, size, instruction)?;
            runtime.stack.push(record);

            Ok(())
        }
    })
}

fn record_lower_memory_<Instance, Export, LocalImport, Memory, MemoryView>(
    instance: &mut Instance,
    instruction: Instruction,
    values: Vec1<InterfaceValue>,
) -> Result<(i32, i32), InstructionError>
where
    Export: crate::interpreter::wasm::structures::Export,
    LocalImport: crate::interpreter::wasm::structures::LocalImport,
    Memory: crate::interpreter::wasm::structures::Memory<MemoryView>,
    MemoryView: crate::interpreter::wasm::structures::MemoryView,
    Instance:
        crate::interpreter::wasm::structures::Instance<Export, LocalImport, Memory, MemoryView>,
{
    let mut result: Vec<u64> = Vec::with_capacity(values.len());

    for value in values.0 {
        match value {
            InterfaceValue::S8(value) => result.push(value as _),
            InterfaceValue::S16(value) => result.push(value as _),
            InterfaceValue::S32(value) => result.push(value as _),
            InterfaceValue::S64(value) => result.push(value as _),
            InterfaceValue::U8(value) => result.push(value as _),
            InterfaceValue::U16(value) => result.push(value as _),
            InterfaceValue::U32(value) => result.push(value as _),
            InterfaceValue::U64(value) => result.push(value as _),
            InterfaceValue::I32(value) => result.push(value as _),
            InterfaceValue::I64(value) => result.push(value as _),
            InterfaceValue::F32(value) => result.push(value as _),
            InterfaceValue::F64(value) => {
                result.push(unsafe { std::mem::transmute::<f64, u64>(value) })
            }
            InterfaceValue::String(value) => {
                let string_pointer =
                    write_to_instance_mem(instance, instruction.clone(), value.as_bytes())?;
                result.push(string_pointer as _);
                result.push(value.len() as _);
            }

            InterfaceValue::ByteArray(value) => {
                let byte_array_pointer =
                    write_to_instance_mem(instance, instruction.clone(), &value)?;
                result.push(byte_array_pointer as _);
                result.push(value.len() as _);
            }

            InterfaceValue::Record(record) => {
                let (record_ptr, record_size) =
                    record_lower_memory_(instance, instruction, record)?;

                result.push(record_ptr as _);
                result.push(record_size as _);
            }
        }
    }

    let result = safe_transmute::transmute_to_bytes::<u64>(&result);
    let result_pointer = write_to_instance_mem(instance, instruction.clone(), &result)?;

    Ok((result_pointer, result.len() as _))
}

pub(crate) fn record_lower_memory<Instance, Export, LocalImport, Memory, MemoryView>(
    type_index: u32,
    instruction: Instruction,
) -> crate::interpreter::ExecutableInstruction<Instance, Export, LocalImport, Memory, MemoryView>
where
    Export: crate::interpreter::wasm::structures::Export,
    LocalImport: crate::interpreter::wasm::structures::LocalImport,
    Memory: crate::interpreter::wasm::structures::Memory<MemoryView>,
    MemoryView: crate::interpreter::wasm::structures::MemoryView,
    Instance:
        crate::interpreter::wasm::structures::Instance<Export, LocalImport, Memory, MemoryView>,
{
    #[allow(unused_imports)]
    use crate::interpreter::stack::Stackable;
    Box::new({
        move |runtime| -> _ {
            let instance = &mut runtime.wasm_instance;
            let record_type = match instance.wit_type(type_index).ok_or_else(|| {
                InstructionError::new(
                    instruction,
                    InstructionErrorKind::TypeIsMissing { type_index },
                )
            })? {
                Type::Record(record_type) => record_type,
                Type::Function { .. } => {
                    return Err(InstructionError::new(
                        instruction,
                        InstructionErrorKind::InvalidTypeKind {
                            expected_kind: TypeKind::Record,
                            received_kind: TypeKind::Function,
                        },
                    ))
                }
            };
            match runtime.stack.pop1() {
                Some(InterfaceValue::Record(record_values))
                    if record_type == &(&*record_values).into() =>
                {
                    /*
                    let value: Vec<u8> = crate::serde::de::from_interface_values(&record_values)
                        .map_err(|e| {
                            InstructionError::new(
                                instruction,
                                InstructionErrorKind::SerdeError(e.to_string()),
                            )
                        })?;

                    let value_pointer = write_to_instance_mem(*instance, instruction, &value)?;
                    runtime.stack.push(InterfaceValue::I32(value_pointer));
                    runtime.stack.push(InterfaceValue::I32(value.len() as _));
                     */
                    let (offset, size) =
                        record_lower_memory_(*instance, instruction, record_values)?;
                    runtime.stack.push(InterfaceValue::I32(offset));
                    runtime.stack.push(InterfaceValue::I32(size));

                    Ok(())
                }
                Some(value) => Err(InstructionError::new(
                    instruction,
                    InstructionErrorKind::InvalidValueOnTheStack {
                        expected_type: InterfaceType::Record(record_type.clone()),
                        received_type: (&value).into(),
                    },
                )),
                None => Err(InstructionError::new(
                    instruction,
                    InstructionErrorKind::StackIsTooSmall { needed: 1 },
                )),
            }
        }
    })
}

pub(crate) fn record_lower<Instance, Export, LocalImport, Memory, MemoryView>(
    type_index: u32,
    instruction: Instruction,
) -> crate::interpreter::ExecutableInstruction<Instance, Export, LocalImport, Memory, MemoryView>
where
    Export: crate::interpreter::wasm::structures::Export,
    LocalImport: crate::interpreter::wasm::structures::LocalImport,
    Memory: crate::interpreter::wasm::structures::Memory<MemoryView>,
    MemoryView: crate::interpreter::wasm::structures::MemoryView,
    Instance:
        crate::interpreter::wasm::structures::Instance<Export, LocalImport, Memory, MemoryView>,
{
    #[allow(unused_imports)]
    use crate::interpreter::stack::Stackable;
    Box::new({
        move |runtime| -> _ {
            let instance = &runtime.wasm_instance;
            let record_type = match instance.wit_type(type_index).ok_or_else(|| {
                InstructionError::new(
                    instruction,
                    InstructionErrorKind::TypeIsMissing { type_index },
                )
            })? {
                Type::Record(record_type) => record_type,
                Type::Function { .. } => {
                    return Err(InstructionError::new(
                        instruction,
                        InstructionErrorKind::InvalidTypeKind {
                            expected_kind: TypeKind::Record,
                            received_kind: TypeKind::Function,
                        },
                    ))
                }
            };
            match runtime.stack.pop1() {
                Some(InterfaceValue::Record(record_values))
                    if record_type == &(&*record_values).into() =>
                {
                    let values = FlattenInterfaceValueIterator::new(&record_values);
                    for value in values {
                        runtime.stack.push(value.clone());
                    }
                    Ok(())
                }
                Some(value) => Err(InstructionError::new(
                    instruction,
                    InstructionErrorKind::InvalidValueOnTheStack {
                        expected_type: InterfaceType::Record(record_type.clone()),
                        received_type: (&value).into(),
                    },
                )),
                None => Err(InstructionError::new(
                    instruction,
                    InstructionErrorKind::StackIsTooSmall { needed: 1 },
                )),
            }
        }
    })
}
