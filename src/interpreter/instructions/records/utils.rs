use crate::interpreter::instructions::ALLOCATE_FUNC_INDEX;
use crate::interpreter::instructions::DEALLOCATE_FUNC_INDEX;
use crate::interpreter::wasm;
use crate::interpreter::wasm::structures::{FunctionIndex, TypedIndex};

use crate::interpreter::instructions::to_native;
use crate::{
    errors::{InstructionError, InstructionErrorKind},
    interpreter::Instruction,
    types::InterfaceType,
    values::InterfaceValue,
};

pub(super) fn read_from_instance_mem<'instance, Instance, Export, LocalImport, Memory, MemoryView>(
    instance: &'instance Instance,
    instruction: Instruction,
    offset: usize,
    size: usize,
) -> Result<Vec<u8>, InstructionError>
where
    Export: wasm::structures::Export + 'instance,
    LocalImport: wasm::structures::LocalImport + 'instance,
    Memory: wasm::structures::Memory<MemoryView> + 'instance,
    MemoryView: wasm::structures::MemoryView,
    Instance: wasm::structures::Instance<Export, LocalImport, Memory, MemoryView>,
{
    let memory_index: u32 = 0;
    let memory_view = instance
        .memory(memory_index as usize)
        .ok_or_else(|| {
            InstructionError::new(
                instruction,
                InstructionErrorKind::MemoryIsMissing { memory_index },
            )
        })?
        .view();

    Ok((&memory_view[offset..offset + size])
        .iter()
        .map(std::cell::Cell::get)
        .collect::<Vec<u8>>())
}

pub(super) fn write_to_instance_mem<'instance, Instance, Export, LocalImport, Memory, MemoryView>(
    instance: &'instance Instance,
    instruction: Instruction,
    bytes: &[u8],
) -> Result<i32, InstructionError>
where
    Export: wasm::structures::Export + 'instance,
    LocalImport: wasm::structures::LocalImport + 'instance,
    Memory: wasm::structures::Memory<MemoryView> + 'instance,
    MemoryView: wasm::structures::MemoryView,
    Instance: wasm::structures::Instance<Export, LocalImport, Memory, MemoryView>,
{
    let mem_pointer = allocate(instance, instruction, bytes.len() as _)?;

    let memory_index: u32 = 0;
    let memory_view = instance
        .memory(memory_index as usize)
        .ok_or_else(|| {
            InstructionError::new(
                instruction,
                InstructionErrorKind::MemoryIsMissing { memory_index },
            )
        })?
        .view();

    for (byte_id, byte) in bytes.iter().enumerate() {
        memory_view[mem_pointer as usize + byte_id].set(*byte);
    }

    Ok(mem_pointer)
}

pub(super) fn allocate<'instance, Instance, Export, LocalImport, Memory, MemoryView>(
    instance: &'instance Instance,
    instruction: Instruction,
    size: i32,
) -> Result<i32, InstructionError>
where
    Export: wasm::structures::Export + 'instance,
    LocalImport: wasm::structures::LocalImport + 'instance,
    Memory: wasm::structures::Memory<MemoryView> + 'instance,
    MemoryView: wasm::structures::MemoryView,
    Instance: wasm::structures::Instance<Export, LocalImport, Memory, MemoryView>,
{
    let values = call_core(
        instance,
        ALLOCATE_FUNC_INDEX,
        instruction,
        vec![InterfaceValue::I32(size)],
    )?;
    if values.len() != 1 {
        return Err(InstructionError::new(
            instruction,
            InstructionErrorKind::LocalOrImportSignatureMismatch {
                function_index: ALLOCATE_FUNC_INDEX,
                expected: (vec![InterfaceType::I32], vec![]),
                received: (vec![], vec![]),
            },
        ));
    }
    to_native::<i32>(&values[0], instruction)
}

pub(super) fn deallocate<'instance, Instance, Export, LocalImport, Memory, MemoryView>(
    instance: &'instance Instance,
    instruction: Instruction,
    mem_ptr: i32,
    size: i32,
) -> Result<(), InstructionError>
where
    Export: wasm::structures::Export + 'instance,
    LocalImport: wasm::structures::LocalImport + 'instance,
    Memory: wasm::structures::Memory<MemoryView> + 'instance,
    MemoryView: wasm::structures::MemoryView,
    Instance: wasm::structures::Instance<Export, LocalImport, Memory, MemoryView>,
{
    let _ = call_core(
        instance,
        DEALLOCATE_FUNC_INDEX,
        instruction,
        vec![InterfaceValue::I32(mem_ptr), InterfaceValue::I32(size)],
    )?;

    Ok(())
}

fn call_core<'instance, Instance, Export, LocalImport, Memory, MemoryView>(
    instance: &'instance Instance,
    function_index: u32,
    instruction: Instruction,
    inputs: Vec<InterfaceValue>,
) -> Result<Vec<InterfaceValue>, InstructionError>
where
    Export: wasm::structures::Export + 'instance,
    LocalImport: wasm::structures::LocalImport + 'instance,
    Memory: wasm::structures::Memory<MemoryView> + 'instance,
    MemoryView: wasm::structures::MemoryView,
    Instance: wasm::structures::Instance<Export, LocalImport, Memory, MemoryView>,
{
    let index = FunctionIndex::new(function_index as usize);
    let local_or_import = instance.local_or_import(index).ok_or_else(|| {
        InstructionError::new(
            instruction,
            InstructionErrorKind::LocalOrImportIsMissing { function_index },
        )
    })?;

    crate::interpreter::instructions::check_function_signature(
        instance,
        local_or_import,
        &inputs,
        instruction,
    )?;

    let outputs = local_or_import.call(&inputs).map_err(|_| {
        InstructionError::new(
            instruction,
            InstructionErrorKind::LocalOrImportCall { function_index },
        )
    })?;

    Ok(outputs)
}
