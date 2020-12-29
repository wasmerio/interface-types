use super::deallocate;
use super::read_from_instance_mem;
use super::write_to_instance_mem;

use crate::interpreter::instructions::to_native;
use crate::{
    errors::{InstructionError, InstructionErrorKind},
    interpreter::Instruction,
    IType, IValue,
};

use std::convert::TryInto;

pub(super) fn array_lift_memory_<'instance, Instance, Export, LocalImport, Memory, MemoryView>(
    instance: &'instance Instance,
    value_type: &IType,
    offset: usize,
    size: usize,
    instruction: Instruction,
) -> Result<Vec<IValue>, InstructionError>
where
    Export: crate::interpreter::wasm::structures::Export,
    LocalImport: crate::interpreter::wasm::structures::LocalImport,
    Memory: crate::interpreter::wasm::structures::Memory<MemoryView>,
    MemoryView: crate::interpreter::wasm::structures::MemoryView,
    Instance: crate::interpreter::wasm::structures::Instance<Export, LocalImport, Memory, MemoryView>
        + 'instance,
{
    use safe_transmute::guard::AllOrNothingGuard;
    use safe_transmute::transmute_many;
    use safe_transmute::transmute_vec;

    if size == 0 {
        return Ok(vec![]);
    }

    let data = read_from_instance_mem(instance, instruction.clone(), offset, size)?;

    let result_array = match value_type {
        IType::S8 => {
            let data = transmute_vec::<u8, i8>(data).unwrap();
            data.into_iter().map(IValue::S8).collect::<Vec<_>>()
        }
        IType::S16 => {
            let data = transmute_many::<i16, AllOrNothingGuard>(&data).unwrap();

            data.iter().map(|v| IValue::S16(*v)).collect::<Vec<_>>()
        }
        IType::S32 => {
            let data = transmute_many::<i32, AllOrNothingGuard>(&data).unwrap();
            data.iter().map(|v| IValue::S32(*v)).collect::<Vec<_>>()
        }
        IType::S64 => {
            let data = transmute_many::<i64, AllOrNothingGuard>(&data).unwrap();
            data.iter().map(|v| IValue::S64(*v)).collect::<Vec<_>>()
        }
        IType::I32 => {
            let data = transmute_many::<i32, AllOrNothingGuard>(&data).unwrap();
            data.iter().map(|v| IValue::I32(*v)).collect::<Vec<_>>()
        }
        IType::I64 => {
            let data = transmute_many::<i64, AllOrNothingGuard>(&data).unwrap();
            data.iter().map(|v| IValue::S64(*v)).collect::<Vec<_>>()
        }
        IType::U8 => data.into_iter().map(IValue::U8).collect::<Vec<_>>(),
        IType::U16 => {
            let data = transmute_many::<u16, AllOrNothingGuard>(&data).unwrap();
            data.iter().map(|v| IValue::U16(*v)).collect::<Vec<_>>()
        }
        IType::U32 => {
            let data = transmute_many::<u32, AllOrNothingGuard>(&data).unwrap();
            data.iter().map(|v| IValue::U32(*v)).collect::<Vec<_>>()
        }
        IType::U64 => {
            let data = transmute_many::<u64, AllOrNothingGuard>(&data).unwrap();
            data.iter().map(|v| IValue::U64(*v)).collect::<Vec<_>>()
        }
        IType::F32 => {
            let data = transmute_many::<u32, AllOrNothingGuard>(&data).unwrap();
            data.iter()
                .map(|v| IValue::F32(f32::from_bits(*v)))
                .collect::<Vec<_>>()
        }
        IType::F64 => {
            let data = transmute_many::<u64, AllOrNothingGuard>(&data).unwrap();
            data.iter()
                .map(|v| IValue::F64(f64::from_bits(*v)))
                .collect::<Vec<_>>()
        }
        IType::Anyref => unimplemented!(),
        IType::String => {
            let data = transmute_many::<u32, AllOrNothingGuard>(&data).unwrap();

            if data.is_empty() {
                return Ok(vec![]);
            }

            let mut result = Vec::with_capacity(data.len() / 2);
            let mut data = data.iter();

            while let Some(string_offset) = data.next() {
                let string_size = data.next().ok_or_else(|| {
                    InstructionError::new(
                        instruction.clone(),
                        InstructionErrorKind::CorruptedArray(String::from(
                            "serialized array must contain even count of elements",
                        )),
                    )
                })?;

                let string_mem = read_from_instance_mem(
                    instance,
                    instruction.clone(),
                    *string_offset as _,
                    *string_size as _,
                )?;

                // TODO: check
                let string = String::from_utf8(string_mem).unwrap();
                result.push(IValue::String(string));
            }

            result
        }
        IType::Array(ty) => {
            let data = transmute_many::<u32, AllOrNothingGuard>(&data).unwrap();

            if data.is_empty() {
                return Ok(vec![]);
            }

            let mut result = Vec::with_capacity(data.len() / 2);
            let mut data = data.iter();

            while let Some(array_offset) = data.next() {
                let array_size = data.next().ok_or_else(|| {
                    InstructionError::new(
                        instruction.clone(),
                        InstructionErrorKind::CorruptedArray(String::from(
                            "serialized array must contain even count of elements",
                        )),
                    )
                })?;

                let value = array_lift_memory_(
                    instance,
                    &*ty,
                    *array_offset as _,
                    *array_size as _,
                    instruction.clone(),
                )?;

                result.push(IValue::Array(value));
            }

            result
        }
        IType::Record(record_type_id) => {
            let record_type = instance.wit_record_by_id(*record_type_id).ok_or_else(|| {
                InstructionError::new(
                    instruction.clone(),
                    InstructionErrorKind::RecordTypeByNameIsMissing {
                        record_type_id: *record_type_id,
                    },
                )
            })?;

            let data = transmute_many::<u32, AllOrNothingGuard>(&data).unwrap();

            let mut result = Vec::with_capacity(data.len());

            for record_offset in data {
                result.push(super::record_lift_memory_(
                    instance,
                    record_type,
                    *record_offset as _,
                    instruction.clone(),
                )?);
            }
            result
        }
    };

    deallocate(instance, instruction, offset as _, size as _)?;

    Ok(result_array)
}

pub(crate) fn array_lift_memory<Instance, Export, LocalImport, Memory, MemoryView>(
    instruction: Instruction,
    value_type: IType,
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
                    instruction.clone(),
                    InstructionErrorKind::StackIsTooSmall { needed: 1 },
                )
            })?;

            let offset: usize = to_native::<i32>(&inputs[0], instruction.clone())?
                .try_into()
                .map_err(|e| (e, "offset").into())
                .map_err(|k| InstructionError::new(instruction.clone(), k))?;

            let size: usize = to_native::<i32>(&inputs[1], instruction.clone())?
                .try_into()
                .map_err(|e| (e, "size").into())
                .map_err(|k| InstructionError::new(instruction.clone(), k))?;

            log::trace!(
                "array.lift_memory: lifting memory for value type: {:?}, popped offset {}, size {}",
                value_type,
                offset,
                size
            );

            let instance = &mut runtime.wasm_instance;
            let array = array_lift_memory_(
                *instance,
                &value_type,
                offset as _,
                size as _,
                instruction.clone(),
            )?;

            log::trace!("array.lift_memory: pushing {:?} on the stack", array);
            runtime.stack.push(IValue::Array(array));

            Ok(())
        }
    })
}

pub(super) fn array_lower_memory_<Instance, Export, LocalImport, Memory, MemoryView>(
    instance: &mut Instance,
    instruction: Instruction,
    array_values: Vec<IValue>,
) -> Result<(usize, usize), InstructionError>
where
    Export: crate::interpreter::wasm::structures::Export,
    LocalImport: crate::interpreter::wasm::structures::LocalImport,
    Memory: crate::interpreter::wasm::structures::Memory<MemoryView>,
    MemoryView: crate::interpreter::wasm::structures::MemoryView,
    Instance:
        crate::interpreter::wasm::structures::Instance<Export, LocalImport, Memory, MemoryView>,
{
    let mut result: Vec<u64> = Vec::with_capacity(array_values.len());

    // here it's known that all interface values have the same type
    for value in array_values {
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
                let (array_offset, array_size) = if !values.is_empty() {
                    array_lower_memory_(instance, instruction.clone(), values)?
                } else {
                    (0, 0)
                };

                result.push(array_offset as _);
                result.push(array_size as _);
            }

            IValue::Record(values) => {
                let record_offset =
                    super::record_lower_memory_(instance, instruction.clone(), values)?;
                result.push(record_offset as _);
            }
        }
    }

    let result = safe_transmute::transmute_to_bytes::<u64>(&result);
    let result_pointer = write_to_instance_mem(instance, instruction, &result)?;

    Ok((result_pointer as _, result.len() as _))
}

pub(crate) fn array_lower_memory<Instance, Export, LocalImport, Memory, MemoryView>(
    instruction: Instruction,
    value_type: IType,
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
            let stack_value = runtime.stack.pop1().ok_or_else(|| {
                InstructionError::new(
                    instruction.clone(),
                    InstructionErrorKind::StackIsTooSmall { needed: 1 },
                )
            })?;

            match stack_value {
                IValue::Array(values) => {
                    log::trace!("array.lower_memory: obtained {:?} values on the stack for interface type {:?}", values, value_type);

                    for value in values.iter() {
                        super::is_value_compatible_to_type(
                            &**instance,
                            &value_type,
                            &value,
                            instruction.clone(),
                        )?;
                    }

                    let (offset, size) =
                        array_lower_memory_(*instance, instruction.clone(), values)?;

                    log::trace!(
                        "array.lower_memory: pushing {}, {} on the stack",
                        offset,
                        size
                    );
                    runtime.stack.push(IValue::I32(offset as _));
                    runtime.stack.push(IValue::I32(size as _));

                    Ok(())
                }
                _ => Err(InstructionError::new(
                    instruction.clone(),
                    InstructionErrorKind::InvalidValueOnTheStack {
                        expected_type: IType::Array(Box::new(value_type.clone())),
                        received_value: stack_value.clone(),
                    },
                )),
            }
        }
    })
}
