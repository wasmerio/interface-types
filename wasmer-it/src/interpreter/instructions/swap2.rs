use crate::{
    errors::{InstructionError, InstructionErrorKind},
    interpreter::Instruction,
};

executable_instruction!(
    swap2(instruction: Instruction) -> _ {
        move |runtime| -> _ {
            let mut values = runtime.stack.pop(2).ok_or_else(|| {
                InstructionError::new(
                    instruction.clone(),
                    InstructionErrorKind::StackIsTooSmall { needed: 1 },
                )
            })?;

            log::trace!("swap2: swapping {:?}, {:?} values on the stack", values[0], values[1]);
            runtime.stack.push(values.remove(1));
            runtime.stack.push(values.remove(0));

            Ok(())
        }
    }
);
