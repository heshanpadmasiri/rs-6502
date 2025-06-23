Add new instruction of `instruction.rs` file.

Ask for addressing modes if not provided.
    - Some instructions like `BRK` don't have addressing modes. Such instruction have a constant number of ticks.
    - If they have addressing modes (like `STA`) depending on the addressing mode number of ticks needed will be different.

Ask for op code (opc) if not provided.
    - Each different addressing mode have a different value for opc.

Fallowing the fallowing step by step process.
1. Create a struct for the instruction. This will hold the addressing mode if it has any.
2. Then implement `Instruction` trait for that instruction. If the instruction has addressing modes you must validate that addressing mode is a valid one.
3. Then update `init_op_table` with new instructions. At this point make sure to run `cargo test` to make sure your change haven't broken anything.
4. Add unit tests. You must validate all addressing modes to be working. Also if user has specified special status flag changes they should be tested as well.
5. Then create a rom containing you instruction as well as existing ones and validate it is working as indented. See main method for available features.
