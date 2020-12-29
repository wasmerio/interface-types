use super::read_from_instance_mem;
use super::write_to_instance_mem;

use crate::interpreter::instructions::{is_record_fields_compatible_to_type, to_native};
use crate::IRecordType;
use crate::IType;
use crate::IValue;
use crate::NEVec;
use crate::{
    errors::{InstructionError, InstructionErrorKind},
    interpreter::Instruction,
};

use std::convert::TryInto;
/*

struct Record1 {
field1: String,
field2: i32,
}

// export
fn foo(t: Record1) {

// import
 */

/*
/// Build an `IValue::Record` based on values on the stack.
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
    stack: &mut Stack<IValue>,
    record_type: &RecordType,
) -> Result<IValue, InstructionErrorKind> {
    let length = record_type.fields.len();
    let mut values = VecDeque::with_capacity(length);
    for field in record_type.fields.iter().rev() {
        match field {
            IType::Record(record_type) => {
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
    Ok(IValue::Record(
        NEVec::new(values.into_iter().collect())
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
                    instruction.clone(),
                    InstructionErrorKind::TypeIsMissing { type_index },
                )
            })? {
                Type::Record(record_type) => record_type,
                Type::Function { .. } => {
                    return Err(InstructionError::new(
                        instruction.clone(),
                        InstructionErrorKind::InvalidTypeKind {
                            expected_kind: TypeKind::Record,
                            received_kind: TypeKind::Function,
                        },
                    ))
                }
            };
            let record = record_lift_(&mut runtime.stack, &record_type)
                .map_err(|k| InstructionError::new(instruction.clone(), k))?;
            runtime.stack.push(record);
            Ok(())
        }
    })
}
 */

pub(super) fn record_lift_memory_<'instance, Instance, Export, LocalImport, Memory, MemoryView>(
    instance: &'instance Instance,
    record_type: &IRecordType,
    offset: usize,
    instruction: Instruction,
) -> Result<IValue, InstructionError>
where
    Export: crate::interpreter::wasm::structures::Export,
    LocalImport: crate::interpreter::wasm::structures::LocalImport,
    Memory: crate::interpreter::wasm::structures::Memory<MemoryView>,
    MemoryView: crate::interpreter::wasm::structures::MemoryView,
    Instance: crate::interpreter::wasm::structures::Instance<Export, LocalImport, Memory, MemoryView>
        + 'instance,
{
    fn record_size(record_type: &IRecordType) -> usize {
        let mut record_size = 0;

        for field_type in record_type.fields.iter() {
            let params_count = match field_type.ty {
                IType::String | IType::Array(_) => 2,
                _ => 1,
            };

            record_size += std::mem::size_of::<u64>() * params_count;
        }

        record_size
    }

    let length = record_type.fields.len();
    let mut values = Vec::with_capacity(length);
    let size = record_size(record_type);
    let data = read_from_instance_mem(instance, instruction.clone(), offset, size)?;
    // TODO: add error handling
    let data =
        safe_transmute::transmute_many::<u64, safe_transmute::SingleManyGuard>(&data).unwrap();

    let mut field_id = 0;
    for field in (*record_type.fields).iter() {
        let value = data[field_id];
        match &field.ty {
            IType::S8 => {
                values.push(IValue::S8(value as _));
            }
            IType::S16 => {
                values.push(IValue::S16(value as _));
            }
            IType::S32 => {
                values.push(IValue::S32(value as _));
            }
            IType::S64 => {
                values.push(IValue::S64(value as _));
            }
            IType::I32 => {
                values.push(IValue::I32(value as _));
            }
            IType::I64 => {
                values.push(IValue::I64(value as _));
            }
            IType::U8 => {
                values.push(IValue::U8(value as _));
            }
            IType::U16 => {
                values.push(IValue::U16(value as _));
            }
            IType::U32 => {
                values.push(IValue::U32(value as _));
            }
            IType::U64 => {
                values.push(IValue::U64(value as _));
            }
            IType::F32 => {
                values.push(IValue::F32(value as _));
            }
            IType::F64 => values.push(IValue::F64(f64::from_bits(value))),
            IType::Anyref => {}
            IType::String => {
                let string_offset = value;
                field_id += 1;
                let string_size = data[field_id];

                if string_size != 0 {
                    let string_mem = read_from_instance_mem(
                        instance,
                        instruction.clone(),
                        string_offset as _,
                        string_size as _,
                    )?;

                    // TODO: check
                    let string = String::from_utf8(string_mem).unwrap();
                    values.push(IValue::String(string));
                } else {
                    values.push(IValue::String(String::new()));
                }
            }
            IType::Array(ty) => {
                let array_offset = value;
                field_id += 1;
                let array_size = data[field_id];

                if array_size != 0 {
                    let array = super::array_lift_memory_(
                        instance,
                        &**ty,
                        array_offset as _,
                        array_size as _,
                        instruction.clone(),
                    )?;
                    values.push(IValue::Array(array));
                } else {
                    values.push(IValue::Array(vec![]));
                }
            }
            IType::Record(record_type_id) => {
                let offset = value;

                let record_type = instance.wit_record_by_id(*record_type_id).ok_or_else(|| {
                    InstructionError::new(
                        instruction.clone(),
                        InstructionErrorKind::RecordTypeByNameIsMissing {
                            record_type_id: *record_type_id,
                        },
                    )
                })?;

                values.push(record_lift_memory_(
                    instance,
                    record_type,
                    offset as _,
                    instruction.clone(),
                )?)
            }
        }
        field_id += 1;
    }

    super::deallocate(instance, instruction, offset as _, size as _)?;

    Ok(IValue::Record(
        NEVec::new(values.into_iter().collect())
            .expect("Record must have at least one field, zero given"),
    ))
}

pub(crate) fn record_lift_memory<Instance, Export, LocalImport, Memory, MemoryView>(
    record_type_id: u64,
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
                    instruction.clone(),
                    InstructionErrorKind::StackIsTooSmall { needed: 1 },
                )
            })?;

            let offset: usize = to_native::<i32>(&inputs[0], instruction.clone())?
                .try_into()
                .map_err(|e| (e, "offset").into())
                .map_err(|k| InstructionError::new(instruction.clone(), k))?;

            // TODO: size = 0
            let instance = &runtime.wasm_instance;
            let record_type = instance.wit_record_by_id(record_type_id).ok_or_else(|| {
                InstructionError::new(
                    instruction.clone(),
                    InstructionErrorKind::RecordTypeByNameIsMissing { record_type_id },
                )
            })?;

            log::trace!(
                "record.lift_memory: record {:?} resolved for type id {}",
                record_type,
                record_type_id
            );

            let record =
                record_lift_memory_(&**instance, record_type, offset, instruction.clone())?;

            log::debug!("record.lift_memory: pushing {:?} on the stack", record);
            runtime.stack.push(record);

            Ok(())
        }
    })
}

pub(super) fn record_lower_memory_<Instance, Export, LocalImport, Memory, MemoryView>(
    instance: &mut Instance,
    instruction: Instruction,
    values: NEVec<IValue>,
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
            IValue::S8(value) => result.push(value as _),
            IValue::S16(value) => result.push(value as _),
            IValue::S32(value) => result.push(value as _),
            IValue::S64(value) => result.push(value as _),
            IValue::U8(value) => result.push(value as _),
            IValue::U16(value) => result.push(value as _),
            IValue::U32(value) => result.push(value as _),
            IValue::U64(value) => result.push(value as _),
            IValue::I32(value) => result.push(value as _),
            IValue::I64(value) => result.push(value as _),
            IValue::F32(value) => result.push(value as _),
            IValue::F64(value) => result.push(value.to_bits()),
            IValue::String(value) => {
                let string_pointer = if !value.is_empty() {
                    write_to_instance_mem(instance, instruction.clone(), value.as_bytes())?
                } else {
                    0
                };

                result.push(string_pointer as _);
                result.push(value.len() as _);
            }

            IValue::Array(values) => {
                let (offset, size) = if !values.is_empty() {
                    super::array_lower_memory_(instance, instruction.clone(), values)?
                } else {
                    (0, 0)
                };

                result.push(offset as _);
                result.push(size as _);
            }

            IValue::Record(values) => {
                let record_ptr = record_lower_memory_(instance, instruction.clone(), values)?;

                result.push(record_ptr as _);
            }
        }
    }

    let result = safe_transmute::transmute_to_bytes::<u64>(&result);
    let result_pointer = write_to_instance_mem(instance, instruction, &result)?;

    Ok(result_pointer as _)
}

pub(crate) fn record_lower_memory<Instance, Export, LocalImport, Memory, MemoryView>(
    record_type_id: u64,
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

            match runtime.stack.pop1() {
                Some(IValue::Record(record_fields)) => {
                    is_record_fields_compatible_to_type(
                        &**instance,
                        record_type_id,
                        &record_fields,
                        instruction.clone(),
                    )?;

                    log::debug!("record.lower_memory: obtained {:?} values on the stack for record type = {}", record_fields, record_type_id);

                    let offset =
                        record_lower_memory_(*instance, instruction.clone(), record_fields)?;

                    log::debug!("record.lower_memory: pushing {} on the stack", offset);
                    runtime.stack.push(IValue::I32(offset));

                    Ok(())
                }
                Some(value) => Err(InstructionError::new(
                    instruction.clone(),
                    InstructionErrorKind::InvalidValueOnTheStack {
                        expected_type: IType::Record(record_type_id),
                        received_value: value,
                    },
                )),
                None => Err(InstructionError::new(
                    instruction.clone(),
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
                    instruction.clone(),
                    InstructionErrorKind::TypeIsMissing { type_index },
                )
            })? {
                Type::Record(record_type) => record_type,
                Type::Function { .. } => {
                    return Err(InstructionError::new(
                        instruction.clone(),
                        InstructionErrorKind::InvalidTypeKind {
                            expected_kind: TypeKind::Record,
                            received_kind: TypeKind::Function,
                        },
                    ))
                }
            };
            match runtime.stack.pop1() {
                Some(IValue::Record(record_values))
                    if record_type == &(&*record_values).into() =>
                {
                    let values = FlattenIValueIterator::new(&record_values);
                    for value in values {
                        runtime.stack.push(value.clone());
                    }
                    Ok(())
                }
                Some(value) => Err(InstructionError::new(
                    instruction.clone(),
                    InstructionErrorKind::InvalidValueOnTheStack {
                        expected_type: IType::Record(record_type.clone()),
                        received_type: (&value).into(),
                    },
                )),
                None => Err(InstructionError::new(
                    instruction.clone(),
                    InstructionErrorKind::StackIsTooSmall { needed: 1 },
                )),
            }
        }
    })
}
 */
