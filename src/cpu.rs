pub type Address = u16;

#[derive(Clone, Copy)]
pub enum StatusFlags {
    Negative = 0b1000_0000,         // N
    Overflow = 0b0100_0000,         // V
    Unused = 0b0010_0000,           // U
    Break = 0b0001_0000,            // B
    Decimal = 0b0000_1000,          // D
    InterruptDisable = 0b0000_0100, // I
    Zero = 0b0000_0010,             // Z
    Carry = 0b0000_0001,            // C
}

pub struct CPU {
    pub program_counter: u16, // pc
    pub accumulator: u8,      // ac
    pub x: u8,
    pub y: u8,
    pub stack_pointer: Address, // sp
    pub status: u8,             // sr
    pub ram: [u8; 0x10000],     // 64KB of RAM
    pub rom: Vec<u8>,           // ROM data (variable size)
}

impl CPU {
    pub fn new() -> Self {
        CPU {
            program_counter: 0x0000,
            accumulator: 0x00,
            x: 0x00,
            y: 0x00,
            stack_pointer: 0xFF, // Stack starts at 0x0100
            status: 0x00,        // All flags cleared
            ram: [0; 0x10000],   // Initialize RAM to zero
            rom: Vec::new(),     // Initialize empty ROM
        }
    }

    pub fn push_to_stack(&mut self, value: u8) {
        if self.stack_pointer > 0x01FF {
            panic!("Stack underflow");
        }
        if self.stack_pointer == 0x0100 {
            panic!("Stack overflow");
        }
        self.ram[self.stack_pointer as usize] = value;
        self.stack_pointer = self.stack_pointer.wrapping_sub(1);
    }

    pub fn insert_rom(&mut self, rom_data: Vec<u8>) {
        self.rom = rom_data;
        self.reset();
    }

    pub fn reset(&mut self) {
        self.accumulator = 0x00;
        self.x = 0x00;
        self.y = 0x00;
        self.stack_pointer = 0xFF;
        self.status = 0x00;

        assert!(
            self.rom.len() >= 0xFFFD,
            "ROM must be at least 64KB to read reset vector"
        );
        let low_byte = self.read_byte_from_rom(0xFFFC) as u16;
        let high_byte = self.read_byte_from_rom(0xFFFD) as u16;
        self.program_counter = (high_byte << 8) | low_byte;
    }

    pub fn set_flag(&mut self, flag: StatusFlags) {
        self.status |= flag as u8;
    }

    pub fn reset_flag(&mut self, flag: StatusFlags) {
        self.status &= !(flag as u8);
    }

    pub fn is_flag_set(&self, flag: StatusFlags) -> bool {
        (self.status & flag as u8) != 0
    }

    pub fn get_status(&self) -> u8 {
        self.status
    }

    pub fn read_byte(&self, address: Address) -> u8 {
        self.ram[address as usize]
    }

    pub fn write_byte(&mut self, address: Address, value: u8) {
        self.ram[address as usize] = value;
    }

    pub fn read_byte_from_rom(&self, address: Address) -> u8 {
        if address as usize >= self.rom.len() {
            panic!(
                "Attempted to read from ROM out of bounds at address: {:#04X}",
                address
            );
        }
        self.rom[address as usize]
    }

    pub fn read_u16_from_rom(&self, address: Address) -> u16 {
        let low = self.read_byte_from_rom(address) as u16;
        let high = self.read_byte_from_rom(address + 1) as u16;
        (high << 8) | low
    }

    pub fn print_status(&self) {
        println!("=== CPU Register Status ===");
        println!(
            "Program Counter (PC): ${:04X} ({:5})",
            self.program_counter, self.program_counter
        );
        println!(
            "Accumulator     (A):  ${:02X} ({:3})",
            self.accumulator, self.accumulator
        );
        println!("X Register      (X):  ${:02X} ({:3})", self.x, self.x);
        println!("Y Register      (Y):  ${:02X} ({:3})", self.y, self.y);
        println!(
            "Stack Pointer  (SP):  ${:02X} ({:3})",
            self.stack_pointer, self.stack_pointer
        );

        println!(
            "Status Register (P):  ${:02X} ({})",
            self.status, self.status
        );
        println!(
            "  Flags: {} {} {} {} {} {} {} {}",
            if self.is_flag_set(StatusFlags::Negative) {
                "N"
            } else {
                "-"
            },
            if self.is_flag_set(StatusFlags::Overflow) {
                "V"
            } else {
                "-"
            },
            if self.is_flag_set(StatusFlags::Unused) {
                "U"
            } else {
                "-"
            },
            if self.is_flag_set(StatusFlags::Break) {
                "B"
            } else {
                "-"
            },
            if self.is_flag_set(StatusFlags::Decimal) {
                "D"
            } else {
                "-"
            },
            if self.is_flag_set(StatusFlags::InterruptDisable) {
                "I"
            } else {
                "-"
            },
            if self.is_flag_set(StatusFlags::Zero) {
                "Z"
            } else {
                "-"
            },
            if self.is_flag_set(StatusFlags::Carry) {
                "C"
            } else {
                "-"
            }
        );
    }

    pub fn print_memory_dump(&self) {
        println!("=== Memory Dump (64KB RAM) ===");

        for page in 0..256 {
            let page_start = page * 256;
            let mut has_data = false;

            // Check if this page has any non-zero data
            for i in 0..256 {
                if self.ram[page_start + i] != 0 {
                    has_data = true;
                    break;
                }
            }

            // Only print pages that have data
            if has_data {
                println!();
                println!(
                    "Page ${:02X} (${:04X}-${:04X}):",
                    page,
                    page_start,
                    page_start + 255
                );

                for row in 0..16 {
                    let row_start = page_start + (row * 16);
                    print!("  ${:04X}:", row_start);

                    // Print hex values
                    for col in 0..16 {
                        let addr = row_start + col;
                        print!(" {:02X}", self.ram[addr]);
                    }

                    print!("  ");

                    // Print ASCII representation
                    for col in 0..16 {
                        let addr = row_start + col;
                        let byte = self.ram[addr];
                        if byte >= 32 && byte <= 126 {
                            print!("{}", byte as char);
                        } else {
                            print!(".");
                        }
                    }

                    println!();
                }
            }
        }

        // Also show ROM data summary
        println!();
        println!("=== ROM Summary ===");
        println!("ROM Size: {} bytes", self.rom.len());
        if !self.rom.is_empty() {
            println!(
                "Reset Vector: ${:04X}",
                (self.rom.get(0xFFFD).unwrap_or(&0).clone() as u16) << 8
                    | (self.rom.get(0xFFFC).unwrap_or(&0).clone() as u16)
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_reset_functionality() {
        let mut cpu = CPU::new();

        // Create a ROM with reset vector pointing to 0x8000
        let mut rom = vec![0; 0xFFFE];
        rom[0xFFFC] = 0x00; // Low byte of reset vector
        rom[0xFFFD] = 0x80; // High byte of reset vector (0x8000)

        // Modify CPU state to non-default values
        cpu.accumulator = 0x42;
        cpu.x = 0x33;
        cpu.y = 0x44;
        cpu.stack_pointer = 0x50;
        cpu.status = 0xFF;
        cpu.program_counter = 0x1234;

        // Insert ROM (this will call reset internally)
        cpu.insert_rom(rom);

        // Verify all registers are reset to default values
        assert_eq!(cpu.accumulator, 0x00, "Accumulator should be reset to 0x00");
        assert_eq!(cpu.x, 0x00, "X register should be reset to 0x00");
        assert_eq!(cpu.y, 0x00, "Y register should be reset to 0x00");
        assert_eq!(
            cpu.stack_pointer, 0xFF,
            "Stack pointer should be reset to 0xFF"
        );
        assert_eq!(cpu.status, 0x00, "Status register should be reset to 0x00");

        // Verify program counter is set from reset vector
        assert_eq!(
            cpu.program_counter, 0x8000,
            "Program counter should be set from reset vector"
        );
    }

    #[test]
    fn test_reset_with_different_vector() {
        let mut cpu = CPU::new();

        // Create a ROM with reset vector pointing to 0xC000
        let mut rom = vec![0; 0xFFFE];
        rom[0xFFFC] = 0x00; // Low byte of reset vector
        rom[0xFFFD] = 0xC0; // High byte of reset vector (0xC000)

        cpu.insert_rom(rom);

        assert_eq!(
            cpu.program_counter, 0xC000,
            "Program counter should be set to 0xC000"
        );
    }

    #[test]
    fn test_reset_with_full_address() {
        let mut cpu = CPU::new();

        // Create a ROM with reset vector pointing to 0x1234
        let mut rom = vec![0; 0xFFFE];
        rom[0xFFFC] = 0x34; // Low byte of reset vector
        rom[0xFFFD] = 0x12; // High byte of reset vector (0x1234)

        cpu.insert_rom(rom);

        assert_eq!(
            cpu.program_counter, 0x1234,
            "Program counter should be set to 0x1234"
        );
    }

    #[test]
    fn test_manual_reset_after_state_change() {
        let mut cpu = CPU::new();

        // Create a ROM with reset vector
        let mut rom = vec![0; 0xFFFE];
        rom[0xFFFC] = 0x00; // Low byte
        rom[0xFFFD] = 0x80; // High byte (0x8000)

        cpu.insert_rom(rom);

        // Change CPU state after initial reset
        cpu.accumulator = 0xAA;
        cpu.x = 0xBB;
        cpu.y = 0xCC;
        cpu.stack_pointer = 0x80;
        cpu.status = 0x0F;
        cpu.program_counter = 0x5000;

        // Call reset manually
        cpu.reset();

        // Verify all registers are reset again
        assert_eq!(cpu.accumulator, 0x00);
        assert_eq!(cpu.x, 0x00);
        assert_eq!(cpu.y, 0x00);
        assert_eq!(cpu.stack_pointer, 0xFF);
        assert_eq!(cpu.status, 0x00);
        assert_eq!(cpu.program_counter, 0x8000);
    }

    #[test]
    #[should_panic(expected = "ROM must be at least 64KB to read reset vector")]
    fn test_reset_with_insufficient_rom_size() {
        let mut cpu = CPU::new();

        // Create a ROM that's too small (less than 0xFFFD bytes)
        let rom = vec![0; 100];

        // This should panic because ROM is too small
        cpu.insert_rom(rom);
    }
}
