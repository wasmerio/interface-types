use super::deallocate;
use super::read_from_instance_mem;
use super::write_to_instance_mem;

use crate::interpreter::instructions::to_native;
use crate::{
    errors::{InstructionError, InstructionErrorKind},
    interpreter::Instruction,
    types::InterfaceType,
    values::InterfaceValue,
};

use std::convert::TryInto;

pub(super) fn array_lift_memory_<'instance, Instance, Export, LocalImport, Memory, MemoryView>(
    instance: &'instance Instance,
    value_type: &InterfaceType,
    offset: usize,
    size: usize,
    instruction: Instruction,
) -> Result<Vec<InterfaceValue>, InstructionError>
where
    Export: crate::interpreter::wasm::structures::Export,
    LocalImport: crate::interpreter::wasm::structures::LocalImport,
    Memory: crate::interpreter::wasm::structures::Memory<MemoryView>,
    MemoryView: crate::interpreter::wasm::structures::MemoryView,
    Instance: crate::interpreter::wasm::structures::Instance<Export, LocalImport, Memory, MemoryView>
        + 'instance,
{
    if size == 0 {
        return Ok(vec![]);
    }

    let data = read_from_instance_mem(instance, instruction.clone(), offset, size)?;

    let result_array = match value_type {
        InterfaceType::S8 => {
            let data = safe_transmute::transmute_vec::<u8, i8>(data).unwrap();
            data.into_iter().map(InterfaceValue::S8).collect::<Vec<_>>()
        }
        InterfaceType::S16 => {
            let data = safe_transmute::transmute_vec::<u8, i16>(data).unwrap();
            data.into_iter()
                .map(InterfaceValue::S16)
                .collect::<Vec<_>>()
        }
        InterfaceType::S32 => {
            let data = safe_transmute::transmute_vec::<u8, i32>(data).unwrap();
            data.into_iter()
                .map(InterfaceValue::S32)
                .collect::<Vec<_>>()
        }
        InterfaceType::S64 => {
            let data = safe_transmute::transmute_vec::<u8, i64>(data).unwrap();
            data.into_iter()
                .map(InterfaceValue::S64)
                .collect::<Vec<_>>()
        }
        InterfaceType::I32 => {
            let data = safe_transmute::transmute_vec::<u8, i32>(data).unwrap();
            data.into_iter()
                .map(InterfaceValue::I32)
                .collect::<Vec<_>>()
        }
        InterfaceType::I64 => {
            let data = safe_transmute::transmute_vec::<u8, i64>(data).unwrap();
            data.into_iter()
                .map(InterfaceValue::I64)
                .collect::<Vec<_>>()
        }
        InterfaceType::U8 => data.into_iter().map(InterfaceValue::U8).collect::<Vec<_>>(),
        InterfaceType::U16 => {
            let data = safe_transmute::transmute_vec::<u8, u16>(data).unwrap();
            data.into_iter()
                .map(InterfaceValue::U16)
                .collect::<Vec<_>>()
        }
        InterfaceType::U32 => {
            let data = safe_transmute::transmute_vec::<u8, u32>(data).unwrap();
            data.into_iter()
                .map(InterfaceValue::U32)
                .collect::<Vec<_>>()
        }
        InterfaceType::U64 => {
            let data = safe_transmute::transmute_vec::<u8, u64>(data).unwrap();
            data.into_iter()
                .map(InterfaceValue::U64)
                .collect::<Vec<_>>()
        }
        InterfaceType::F32 => {
            let data = safe_transmute::transmute_vec::<u8, u32>(data).unwrap();
            data.into_iter()
                .map(|v| InterfaceValue::F32(v as _))
                .collect::<Vec<_>>()
        }
        InterfaceType::F64 => {
            let data = safe_transmute::transmute_vec::<u8, u64>(data).unwrap();
            data.into_iter()
                .map(|v| InterfaceValue::F64(f64::from_bits(v)))
                .collect::<Vec<_>>()
        }
        InterfaceType::Anyref => unimplemented!(),
        InterfaceType::String => {
            let data = safe_transmute::transmute_vec::<u8, u32>(data).unwrap();

            if data.is_empty() {
                return Ok(vec![]);
            }

            let mut result = Vec::with_capacity(data.len() / 2);
            let mut data = data.into_iter();

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
                    string_offset as _,
                    string_size as _,
                )?;

                // TODO: check
                let string = String::from_utf8(string_mem).unwrap();
                result.push(InterfaceValue::String(string));
            }

            result
        }
        InterfaceType::Array(ty) => {
            let data = safe_transmute::transmute_vec::<u8, u32>(data).unwrap();

            if data.is_empty() {
                return Ok(vec![]);
            }

            let mut result = Vec::with_capacity(data.len() / 2);
            let mut data = data.into_iter();

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
                    array_offset as _,
                    array_size as _,
                    instruction.clone(),
                )?;

                result.push(InterfaceValue::Array(value));
            }

            result
        }
        InterfaceType::Record(record_type_id) => {
            let record_type = instance.wit_record_by_id(*record_type_id).ok_or_else(|| {
                InstructionError::new(
                    instruction.clone(),
                    InstructionErrorKind::RecordTypeByNameIsMissing {
                        record_type_id: *record_type_id,
                    },
                )
            })?;

            let data = safe_transmute::transmute_vec::<u8, u32>(data).unwrap();

            let mut result = Vec::with_capacity(data.len());

            for record_offset in data.into_iter() {
                result.push(super::record_lift_memory_(
                    instance,
                    record_type,
                    record_offset as _,
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
    value_type: InterfaceType,
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
                .map_err(|e| (e, "offset").into())
                .map_err(|k| InstructionError::new(instruction.clone(), k))?;

            log::trace!(
                "array.lift_memory: lifting memory for value type: {:?}",
                value_type
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
            runtime.stack.push(InterfaceValue::Array(array));

            Ok(())
        }
    })
}

pub(super) fn array_lower_memory_<Instance, Export, LocalImport, Memory, MemoryView>(
    instance: &mut Instance,
    instruction: Instruction,
    array_values: Vec<InterfaceValue>,
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
                    write_to_instance_mem(instance, instruction.clone(), value.as_bytes())?
                } else {
                    0
                };

                result.push(string_pointer as _);
                result.push(value.len() as _);
            }

            InterfaceValue::Array(values) => {
                let (array_offset, array_size) = if !values.is_empty() {
                    array_lower_memory_(instance, instruction.clone(), values)?
                } else {
                    (0, 0)
                };

                result.push(array_offset as _);
                result.push(array_size as _);
            }

            InterfaceValue::Record(values) => {
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
    value_type: InterfaceType,
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

            super::is_value_compatible_to_type(
                &**instance,
                &value_type,
                &stack_value,
                instruction.clone(),
            )?;

            match stack_value {
                InterfaceValue::Array(values) => {
                    log::trace!("array.lower_memory: obtained {:?} values on the stack for interface type = {:?}", values, value_type);

                    let (offset, size) =
                        array_lower_memory_(*instance, instruction.clone(), values)?;

                    log::trace!(
                        "array.lower_memory: pushing {}, {} on the stack",
                        offset,
                        size
                    );
                    runtime.stack.push(InterfaceValue::I32(offset as _));
                    runtime.stack.push(InterfaceValue::I32(size as _));

                    Ok(())
                }
                _ => panic!("is_value_compatible_to_type should invoked previously"),
            }
        }
    })
}
