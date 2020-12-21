use crate::{
    errors::{InstructionError, InstructionErrorKind},
    interpreter::Instruction,
};

executable_instruction!(
    dup(instruction: Instruction) -> _ {
        move |runtime| -> _ {
            let value = runtime.stack.peek1().ok_or_else(|| {
                InstructionError::new(
                    instruction.clone(),
                    InstructionErrorKind::StackIsTooSmall { needed: 1 },
                )
            })?;

            let value = value.clone();
            log::trace!("dup: duplication {:?} value on the stack", value);
            runtime.stack.push(value);

            Ok(())
        }
    }
);
