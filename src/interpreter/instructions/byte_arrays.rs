use super::to_native;
use crate::{
    errors::{InstructionError, InstructionErrorKind},
    interpreter::Instruction,
    types::InterfaceType,
    values::InterfaceValue,
};
use std::{cell::Cell, convert::TryInto};

executable_instruction!(
    byte_array_lift_memory(instruction: Instruction) -> _ {
        move |runtime| -> _ {
            let inputs = runtime.stack.pop(2).ok_or_else(|| {
                InstructionError::new(
                    instruction,
                    InstructionErrorKind::StackIsTooSmall { needed: 2 },
                )
            })?;

            let memory_index: u32 = 0;
            let memory = runtime
                .wasm_instance
                .memory(memory_index as usize)
                .ok_or_else(|| {
                    InstructionError::new(
                        instruction,
                        InstructionErrorKind::MemoryIsMissing { memory_index },
                    )
                })?;

            let pointer: usize = to_native::<i32>(&inputs[0], instruction)?
                .try_into()
                .map_err(|e| (e, "pointer").into())
                .map_err(|k| InstructionError::new(instruction, k))?;
            let length: usize = to_native::<i32>(&inputs[1], instruction)?
                .try_into()
                .map_err(|e| (e, "length").into())
                .map_err(|k| InstructionError::new(instruction, k))?;
            let memory_view = memory.view();

            if length == 0 {
                runtime.stack.push(InterfaceValue::ByteArray(vec![]));

                return Ok(())
            }

            if memory_view.len() < pointer + length {
                return Err(InstructionError::new(
                    instruction,
                    InstructionErrorKind::MemoryOutOfBoundsAccess {
                        index: pointer + length,
                        length: memory_view.len(),
                    },
                ));
            }

            let data: Vec<u8> = (&memory_view[pointer..pointer + length])
                .iter()
                .map(Cell::get)
                .collect();

            runtime.stack.push(InterfaceValue::ByteArray(data));

            Ok(())
        }
    }
);

executable_instruction!(
    byte_array_lower_memory(instruction: Instruction) -> _ {
        move |runtime| -> _ {
            let inputs = runtime.stack.pop(2).ok_or_else(|| {
                InstructionError::new(
                    instruction,
                    InstructionErrorKind::StackIsTooSmall { needed: 2 },
                )
            })?;

            let byte_array_pointer: usize = to_native::<i32>(&inputs[0], instruction)?
                .try_into()
                .map_err(|e| (e, "pointer").into())
                .map_err(|k| InstructionError::new(instruction, k))?;
            let byte_array: Vec<u8> = to_native(&inputs[1], instruction)?;
            let byte_array_length: i32 = byte_array.len().try_into().map_err(|_| {
                InstructionError::new(
                    instruction,
                    InstructionErrorKind::NegativeValue { subject: "string_length" },
                )
            })?;

            let instance = &mut runtime.wasm_instance;
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

            for (nth, byte) in byte_array.iter().enumerate() {
                memory_view[byte_array_pointer as usize + nth].set(*byte);
            }

            runtime.stack.push(InterfaceValue::I32(byte_array_pointer as i32));
            runtime.stack.push(InterfaceValue::I32(byte_array_length));

            Ok(())
        }
    }
);

executable_instruction!(
    byte_array_size(instruction: Instruction) -> _ {
        move |runtime| -> _ {
            match runtime.stack.pop1() {
                Some(InterfaceValue::ByteArray(byte_array)) => {
                    let length = byte_array.len() as i32;
                    runtime.stack.push(InterfaceValue::I32(length));

                    Ok(())
                },

                Some(value) => Err(InstructionError::new(
                    instruction,
                    InstructionErrorKind::InvalidValueOnTheStack {
                        expected_type: InterfaceType::ByteArray,
                        received_type: (&value).into(),
                    },
                )),

                None => Err(InstructionError::new(
                    instruction,
                    InstructionErrorKind::StackIsTooSmall { needed: 1 },
                )),
            }
        }
    }
);
