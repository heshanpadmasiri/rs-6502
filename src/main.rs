struct CPU {
    program_counter: u16, // pc
    accumulator: u8,      // ac
    x: u8,
    y: u8,
    stack_pointer: u8,  // sp
    status: u8,         // sr
    ram: [u8; 0x10000], // 64KB of RAM
    rom: Vec<u8>,       // ROM data (variable size)
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

    fn set_flag(&mut self, flag: StatusFlags) {
        self.status |= flag as u8;
    }

    fn reset_flag(&mut self, flag: StatusFlags) {
        self.status &= !(flag as u8);
    }

    fn set_flags(&mut self, flags: &[StatusFlags]) {
        for flag in flags {
            self.status |= *flag as u8;
        }
    }

    fn reset_flags(&mut self, flags: &[StatusFlags]) {
        for flag in flags {
            self.status &= !(*flag as u8);
        }
    }

    fn is_flag_set(&self, flag: StatusFlags) -> bool {
        (self.status & flag as u8) != 0
    }

    fn get_status(&self) -> u8 {
        self.status
    }

    fn set_status(&mut self, status: u8) {
        self.status = status;
    }

    fn read_byte(&self, address: u16) -> u8 {
        self.ram[address as usize]
    }

    fn write_byte(&mut self, address: u16, value: u8) {
        self.ram[address as usize] = value;
    }

    fn read_byte_from_rom(&self, address: u16) -> u8 {
        if address as usize >= self.rom.len() {
            panic!(
                "Attempted to read from ROM out of bounds at address: {:#04X}",
                address
            );
        }
        self.rom[address as usize]
    }
}

#[derive(Clone, Copy)]
enum StatusFlags {
    Negative = 0b1000_0000,         // N
    Overflow = 0b0100_0000,         // V
    Unused = 0b0010_0000,           // U
    Break = 0b0001_0000,            // B
    Decimal = 0b0000_1000,          // D
    InterruptDisable = 0b0000_0100, // I
    Zero = 0b0000_0010,             // Z
    Carry = 0b0000_0001,            // C
}

enum AddressingMode {
    Immediate,
    Absolute(u16),
    ZeroPage(u8),
    ZeroPageX(u8),
    ZeroPageY(u8),
    AbsoluteX(u16),
    AbsoluteY(u16),
}

pub fn main() {
    println!("6502 CPU Emulator");
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
