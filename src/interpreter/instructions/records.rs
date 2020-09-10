mod utils;

use utils::read_from_instance_mem;
use utils::write_to_instance_mem;

use crate::interpreter::instructions::{is_record_fields_compatible_to_type, to_native};
use crate::{
    errors::{InstructionError, InstructionErrorKind},
    interpreter::Instruction,
    types::{InterfaceType, RecordType},
    values::InterfaceValue,
    vec1::Vec1,
};

use std::collections::VecDeque;
use std::convert::TryInto;

/*
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
 */

fn record_lift_memory_<'instance, Instance, Export, LocalImport, Memory, MemoryView>(
    instance: &'instance Instance,
    record_type: &RecordType,
    offset: usize,
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
    fn record_size(record_type: &RecordType) -> usize {
        let mut record_size = 0;

        for field_type in record_type.fields.iter() {
            let params_count = match field_type.ty {
                InterfaceType::String | InterfaceType::ByteArray => 2,
                _ => 1,
            };

            record_size += std::mem::size_of::<u64>() * params_count;
        }

        record_size
    }

    let length = record_type.fields.len();
    let mut values = VecDeque::with_capacity(length);
    let size = record_size(record_type);
    let data = read_from_instance_mem(instance, instruction, offset, size)?;
    // TODO: add error handling
    let data =
        safe_transmute::transmute_many::<u64, safe_transmute::SingleManyGuard>(&data).unwrap();

    let mut field_id = 0;
    for field in (*record_type.fields).iter() {
        let value = data[field_id];
        match &field.ty {
            InterfaceType::S8 => {
                values.push_back(InterfaceValue::S8(value as _));
            }
            InterfaceType::S16 => {
                values.push_back(InterfaceValue::S16(value as _));
            }
            InterfaceType::S32 => {
                values.push_back(InterfaceValue::S32(value as _));
            }
            InterfaceType::S64 => {
                values.push_back(InterfaceValue::S64(value as _));
            }
            InterfaceType::I32 => {
                values.push_back(InterfaceValue::I32(value as _));
            }
            InterfaceType::I64 => {
                values.push_back(InterfaceValue::I64(value as _));
            }
            InterfaceType::U8 => {
                values.push_back(InterfaceValue::U8(value as _));
            }
            InterfaceType::U16 => {
                values.push_back(InterfaceValue::U16(value as _));
            }
            InterfaceType::U32 => {
                values.push_back(InterfaceValue::U32(value as _));
            }
            InterfaceType::U64 => {
                values.push_back(InterfaceValue::U64(value as _));
            }
            InterfaceType::F32 => {
                values.push_back(InterfaceValue::F32(value as _));
            }
            InterfaceType::F64 => values.push_back(InterfaceValue::F64(f64::from_bits(value))),
            InterfaceType::Anyref => {}
            InterfaceType::String => {
                let string_offset = value;
                field_id += 1;
                let string_size = data[field_id];

                if string_size != 0 {
                    let string_mem = read_from_instance_mem(
                        instance,
                        instruction,
                        string_offset as _,
                        string_size as _,
                    )?;

                    // TODO: check
                    let string = String::from_utf8(string_mem).unwrap();
                    values.push_back(InterfaceValue::String(string));
                } else {
                    values.push_back(InterfaceValue::String(String::new()));
                }
            }
            InterfaceType::ByteArray => {
                let array_offset = value;
                field_id += 1;
                let array_size = data[field_id];

                if array_size != 0 {
                    let byte_array = read_from_instance_mem(
                        instance,
                        instruction,
                        array_offset as _,
                        array_size as _,
                    )?;

                    values.push_back(InterfaceValue::ByteArray(byte_array));
                } else {
                    values.push_back(InterfaceValue::ByteArray(vec![]));
                }
            }
            InterfaceType::Record(record_type_name) => {
                let offset = value;

                let record_type =
                    instance
                        .wit_record_by_name(&record_type_name)
                        .ok_or_else(|| {
                            InstructionError::new(
                                instruction,
                                InstructionErrorKind::RecordTypeByNameIsMissing {
                                    type_name: record_type_name.to_owned(),
                                },
                            )
                        })?;

                values.push_back(record_lift_memory_(
                    instance,
                    record_type,
                    offset as _,
                    instruction,
                )?)
            }
        }
        field_id += 1;
    }

    utils::deallocate(instance, instruction, offset as _, size as _)?;

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
            let inputs = runtime.stack.pop(1).ok_or_else(|| {
                InstructionError::new(
                    instruction,
                    InstructionErrorKind::StackIsTooSmall { needed: 1 },
                )
            })?;

            let offset: usize = to_native::<i32>(&inputs[0], instruction)?
                .try_into()
                .map_err(|e| (e, "offset").into())
                .map_err(|k| InstructionError::new(instruction, k))?;

            // TODO: size = 0
            let instance = &runtime.wasm_instance;
            let record_type = instance.wit_record_by_id(type_index).ok_or_else(|| {
                InstructionError::new(
                    instruction,
                    InstructionErrorKind::TypeIsMissing { type_index },
                )
            })?;

            let record = record_lift_memory_(&**instance, record_type, offset, instruction)?;
            runtime.stack.push(record);

            Ok(())
        }
    })
}

fn record_lower_memory_<Instance, Export, LocalImport, Memory, MemoryView>(
    instance: &mut Instance,
    instruction: Instruction,
    values: Vec1<InterfaceValue>,
) -> Result<i32, InstructionError>
where
    Export: crate::interpreter::wasm::structures::Export,
    LocalImport: crate::interpreter::wasm::structures::LocalImport,
    Memory: crate::interpreter::wasm::structures::Memory<MemoryView>,
    MemoryView: crate::interpreter::wasm::structures::MemoryView,
    Instance:
        crate::interpreter::wasm::structures::Instance<Export, LocalImport, Memory, MemoryView>,
{
    let mut result: Vec<u64> = Vec::with_capacity(values.len());

    for value in values.into_vec() {
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
            InterfaceValue::F64(value) => result.push(value.to_bits()),
            InterfaceValue::String(value) => {
                let string_pointer = if !value.is_empty() {
                    write_to_instance_mem(instance, instruction, value.as_bytes())?
                } else {
                    0i32
                };

                result.push(string_pointer as _);
                result.push(value.len() as _);
            }

            InterfaceValue::ByteArray(value) => {
                let byte_array_pointer = if !value.is_empty() {
                    write_to_instance_mem(instance, instruction, &value)?
                } else {
                    0i32
                };

                result.push(byte_array_pointer as _);
                result.push(value.len() as _);
            }

            InterfaceValue::Record(values) => {
                let record_ptr = record_lower_memory_(instance, instruction, values)?;

                result.push(record_ptr as _);
            }
        }
    }

    let result = safe_transmute::transmute_to_bytes::<u64>(&result);
    let result_pointer = write_to_instance_mem(instance, instruction, &result)?;

    Ok(result_pointer)
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
            let record_type = instance.wit_record_by_id(type_index).ok_or_else(|| {
                InstructionError::new(
                    instruction,
                    InstructionErrorKind::TypeIsMissing { type_index },
                )
            })?;

            match runtime.stack.pop1() {
                Some(InterfaceValue::Record(record_fields)) => {
                    is_record_fields_compatible_to_type(
                        &**instance,
                        record_type,
                        &record_fields,
                        instruction,
                    )?;
                    let offset = record_lower_memory_(*instance, instruction, record_fields)?;
                    runtime.stack.push(InterfaceValue::I32(offset));

                    Ok(())
                }
                Some(value) => Err(InstructionError::new(
                    instruction,
                    InstructionErrorKind::InvalidValueOnTheStack {
                        expected_type: InterfaceType::Record(record_type.name.clone()),
                        received_value: value,
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

/*
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
 */
