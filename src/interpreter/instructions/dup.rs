use crate::{
    errors::{InstructionError, InstructionErrorKind},
    interpreter::Instruction,
};

executable_instruction!(
    dup(instruction: Instruction) -> _ {
        move |runtime| -> _ {
            let value = runtime.stack.peek1().ok_or_else(|| {
                InstructionError::new(
                    instruction,
                    InstructionErrorKind::StackIsTooSmall { needed: 1 },
                )
            })?;

            let value = value.clone();
            runtime.stack.push(value);

            Ok(())
        }
    }
);
