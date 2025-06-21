use std::env;
use std::fs;

mod cpu;
mod instruction;
use cpu::{CPU, StatusFlags};
use instruction::init_op_table;

pub fn execute_rom(cpu: &mut CPU, rom: Vec<u8>) {
    cpu.insert_rom(rom);
    let op_code_table = init_op_table();
    let mut current_tick = 0;
    while !cpu.is_flag_set(StatusFlags::Break) {
        let opcode = cpu.read_byte_from_rom(cpu.program_counter);
        if let Some(instruction) = op_code_table[opcode as usize].as_ref() {
            let pc_before = cpu.program_counter;
            cpu.program_counter += 1;
            let done = instruction.execute(cpu, current_tick);
            if done {
                current_tick = 0;
            } else {
                cpu.program_counter = pc_before;
                current_tick += 1;
            }
        } else {
            panic!(
                "Unknown opcode: {:#04X} at PC: {:#04X}",
                opcode, cpu.program_counter
            );
        }
    }
}

pub fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 || args.len() > 3 {
        eprintln!("Usage: {} <rom_file> [--heap-dump]", args[0]);
        eprintln!("  <rom_file>     Path to the ROM file to execute");
        eprintln!("  --heap-dump    Optional: Print memory state in hex pages");
        std::process::exit(1);
    }

    let rom_path = &args[1];
    let heap_dump = args.len() == 3 && args[2] == "--heap-dump";

    // Read ROM file as binary
    let rom_data = match fs::read(rom_path) {
        Ok(data) => data,
        Err(err) => {
            eprintln!("Error reading ROM file '{}': {}", rom_path, err);
            std::process::exit(1);
        }
    };

    println!("6502 CPU Emulator");
    println!("Loading ROM: {} ({} bytes)", rom_path, rom_data.len());

    // Create CPU and execute ROM
    let mut cpu = CPU::new();
    execute_rom(&mut cpu, rom_data);

    println!("Execution completed.");
    println!();

    // Display final register states
    cpu.print_status();

    // Display memory dump if requested
    if heap_dump {
        println!();
        cpu.print_memory_dump();
    }
}
