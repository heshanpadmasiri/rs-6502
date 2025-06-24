use crate::cpu::{Address, CPU, StatusFlags};

fn get_indirect_address(cpu: &CPU, indirect_addr: Address) -> Address {
    let low = cpu.read_byte(indirect_addr);
    let high = cpu.read_byte(indirect_addr.wrapping_add(1));
    (high as u16) << 8 | low as u16
}

const SIGN_MASK: u8 = 0x80;

#[derive(Debug)]
pub enum AddressingMode {
    Immediate,
    Absolute,
    ZeroPage,
    ZeroPageX,
    ZeroPageY,
    AbsoluteX,
    AbsoluteY,
    Indirect,
    PreIndexedIndirect,
    PostIndexedIndirect,
    Relative,
}

impl AddressingMode {
    pub fn target_address(&self, cpu: &CPU) -> Address {
        match self {
            AddressingMode::ZeroPage => cpu.read_byte_from_rom(cpu.program_counter) as u16,
            AddressingMode::ZeroPageX => {
                let addr = cpu.read_byte_from_rom(cpu.program_counter);
                addr.wrapping_add(cpu.x) as u16
            }
            AddressingMode::ZeroPageY => {
                let addr = cpu.read_byte_from_rom(cpu.program_counter);
                addr.wrapping_add(cpu.y) as u16
            }
            AddressingMode::Absolute => cpu.read_u16_from_rom(cpu.program_counter),
            AddressingMode::AbsoluteX => {
                let addr = cpu.read_u16_from_rom(cpu.program_counter);
                addr.wrapping_add(cpu.x as u16)
            }
            AddressingMode::AbsoluteY => {
                let addr = cpu.read_u16_from_rom(cpu.program_counter);
                addr.wrapping_add(cpu.y as u16)
            }
            AddressingMode::PreIndexedIndirect => {
                let base = cpu.read_byte_from_rom(cpu.program_counter);
                let addr = base.wrapping_add(cpu.x) as u16;
                let low = cpu.read_byte(addr);
                let high = cpu.read_byte(addr.wrapping_add(1));
                (high as u16) << 8 | low as u16
            }
            AddressingMode::PostIndexedIndirect => {
                let addr = cpu.read_byte_from_rom(cpu.program_counter) as u16;
                let low = cpu.read_byte(addr);
                let high = cpu.read_byte(addr.wrapping_add(1));
                let addr = (high as u16) << 8 | low as u16;
                addr.wrapping_add(cpu.y as u16)
            }
            AddressingMode::Indirect => {
                let indirect_addr = cpu.read_u16_from_rom(cpu.program_counter);
                get_indirect_address(cpu, indirect_addr)
            }
            _ => panic!("Unsupported addressing mode for target_address: {:?}", self),
        }
    }

    pub fn load_value(&self, cpu: &CPU) -> u8 {
        match self {
            AddressingMode::Immediate => cpu.read_byte_from_rom(cpu.program_counter),
            AddressingMode::Absolute => {
                let addr = cpu.read_u16_from_rom(cpu.program_counter);
                cpu.read_byte(addr)
            }
            AddressingMode::ZeroPage => {
                let addr = cpu.read_byte_from_rom(cpu.program_counter) as u16;
                cpu.read_byte(addr)
            }
            AddressingMode::AbsoluteX => {
                let addr = cpu.read_u16_from_rom(cpu.program_counter);
                let addr = addr.wrapping_add(cpu.x as u16);
                cpu.read_byte(addr)
            }
            AddressingMode::AbsoluteY => {
                let addr = cpu.read_u16_from_rom(cpu.program_counter);
                let addr = addr.wrapping_add(cpu.y as u16);
                cpu.read_byte(addr)
            }
            AddressingMode::ZeroPageX => {
                let addr = cpu.read_byte_from_rom(cpu.program_counter);
                let addr = addr.wrapping_add(cpu.x) as u16;
                cpu.read_byte(addr)
            }
            AddressingMode::ZeroPageY => {
                let addr = cpu.read_byte_from_rom(cpu.program_counter);
                let addr = addr.wrapping_add(cpu.y) as u16;
                cpu.read_byte(addr)
            }
            AddressingMode::Indirect => {
                let indirect_addr = cpu.read_u16_from_rom(cpu.program_counter);
                let effective_addr = get_indirect_address(cpu, indirect_addr);
                cpu.read_byte(effective_addr)
            }
            AddressingMode::PreIndexedIndirect => {
                let base = cpu.read_byte_from_rom(cpu.program_counter);
                let addr = base.wrapping_add(cpu.x) as u16;
                let low = cpu.read_byte(addr);
                let high = cpu.read_byte(addr.wrapping_add(1));
                let effective_addr = (high as u16) << 8 | low as u16;
                cpu.read_byte(effective_addr)
            }
            AddressingMode::PostIndexedIndirect => {
                let addr = cpu.read_byte_from_rom(cpu.program_counter) as u16;
                let low = cpu.read_byte(addr);
                let high = cpu.read_byte(addr.wrapping_add(1));
                let addr = (high as u16) << 8 | low as u16;
                let addr = addr.wrapping_add(cpu.y as u16);
                cpu.read_byte(addr)
            }
            AddressingMode::Relative => {
                panic!("Relative addressing mode should not be used for loading values directly");
            }
        }
    }

    pub fn is_crossing_page_boundary(&self, cpu: &CPU) -> bool {
        fn is_crossing_page_boundary_inner(base: Address, offset: u8) -> bool {
            (base & 0xFF00) != ((base.wrapping_add(offset as u16)) & 0xFF00)
        }
        match self {
            AddressingMode::AbsoluteX => {
                is_crossing_page_boundary_inner(cpu.read_u16_from_rom(cpu.program_counter), cpu.x)
            }
            AddressingMode::AbsoluteY => {
                is_crossing_page_boundary_inner(cpu.read_u16_from_rom(cpu.program_counter), cpu.y)
            }
            AddressingMode::PostIndexedIndirect => {
                let addr = cpu.read_byte_from_rom(cpu.program_counter) as u16;
                let low = cpu.read_byte(addr);
                let high = cpu.read_byte(addr.wrapping_add(1));
                let base_addr = (high as u16) << 8 | low as u16;
                is_crossing_page_boundary_inner(base_addr, cpu.y)
            }
            _ => false,
        }
    }

    pub fn program_counter_increment(&self) -> Address {
        match self {
            AddressingMode::Immediate => 1,
            AddressingMode::ZeroPage => 1,
            AddressingMode::ZeroPageX => 1,
            AddressingMode::ZeroPageY => 1,
            AddressingMode::Absolute => 2,
            AddressingMode::AbsoluteX => 2,
            AddressingMode::AbsoluteY => 2,
            AddressingMode::Indirect => 2,
            AddressingMode::PreIndexedIndirect => 1,
            AddressingMode::PostIndexedIndirect => 1,
            AddressingMode::Relative => 1,
        }
    }
}

pub trait Instruction {
    fn execute(&self, cpu: &mut CPU, current_tick: u8) -> bool;
}

pub struct LDA {
    pub addressing_mode: AddressingMode,
}

impl Instruction for LDA {
    fn execute(&self, cpu: &mut CPU, current_tick: u8) -> bool {
        let ticks = match self.addressing_mode {
            AddressingMode::Immediate => 2,
            AddressingMode::ZeroPage => 3,
            AddressingMode::ZeroPageX => 4,
            AddressingMode::Absolute => 4,
            AddressingMode::AbsoluteX if self.addressing_mode.is_crossing_page_boundary(cpu) => 5,
            AddressingMode::AbsoluteX => 4,
            AddressingMode::AbsoluteY if self.addressing_mode.is_crossing_page_boundary(cpu) => 5,
            AddressingMode::AbsoluteY => 4,
            AddressingMode::PreIndexedIndirect => 6,
            AddressingMode::PostIndexedIndirect => 5, // 5 cycles base, +1 if page boundary crossed
            _ => panic!(
                "Unsupported addressing mode for LDA: {:?}",
                self.addressing_mode
            ),
        };
        if current_tick < ticks {
            return false;
        }
        let value = self.addressing_mode.load_value(cpu);
        let pc_increment = self.addressing_mode.program_counter_increment();
        cpu.program_counter += pc_increment;
        cpu.accumulator = value;
        if (value as i8) < 0 {
            cpu.set_flag(StatusFlags::Negative);
        } else {
            cpu.reset_flag(StatusFlags::Negative);
        }
        if value == 0 {
            cpu.set_flag(StatusFlags::Zero);
        } else {
            cpu.reset_flag(StatusFlags::Zero);
        }
        return true;
    }
}

pub struct STA {
    pub addressing_mode: AddressingMode,
}

impl Instruction for STA {
    fn execute(&self, cpu: &mut CPU, current_tick: u8) -> bool {
        let ticks = match self.addressing_mode {
            AddressingMode::ZeroPage => 3,
            AddressingMode::ZeroPageX => 4,
            AddressingMode::Absolute => 4,
            AddressingMode::AbsoluteX => 5,
            AddressingMode::AbsoluteY => 5,
            AddressingMode::PreIndexedIndirect => 6,
            AddressingMode::PostIndexedIndirect => 6,
            _ => panic!(
                "Unsupported addressing mode for STA: {:?}",
                self.addressing_mode
            ),
        };
        if current_tick < ticks {
            return false;
        };
        let target_address = self.addressing_mode.target_address(cpu);
        let pc_increment = self.addressing_mode.program_counter_increment();
        cpu.program_counter += pc_increment;
        cpu.write_byte(target_address, cpu.accumulator);
        return true;
    }
}

pub struct BRK {}

impl Instruction for BRK {
    fn execute(&self, cpu: &mut CPU, current_tick: u8) -> bool {
        if current_tick < 7 {
            return false;
        }
        let pc = cpu.program_counter.wrapping_add(2);
        cpu.push_to_stack((pc >> 8) as u8);
        cpu.push_to_stack((pc & 0xFF) as u8);
        cpu.set_flag(StatusFlags::Break);

        let status = cpu.get_status();
        cpu.push_to_stack(status);
        cpu.program_counter += 1;
        true
    }
}

pub struct NOP {}

impl Instruction for NOP {
    fn execute(&self, _cpu: &mut CPU, current_tick: u8) -> bool {
        if current_tick < 2 {
            return false;
        }
        true
    }
}

pub struct CLC {}

impl Instruction for CLC {
    fn execute(&self, cpu: &mut CPU, current_tick: u8) -> bool {
        if current_tick < 2 {
            return false;
        }
        cpu.reset_flag(StatusFlags::Carry);
        true
    }
}

pub struct JMP {
    pub addressing_mode: AddressingMode,
}

impl Instruction for JMP {
    fn execute(&self, cpu: &mut CPU, current_tick: u8) -> bool {
        let ticks = match self.addressing_mode {
            AddressingMode::Absolute => 3,
            AddressingMode::Indirect => 5,
            _ => panic!(
                "Unsupported addressing mode for JMP: {:?}",
                self.addressing_mode
            ),
        };
        if current_tick < ticks {
            return false;
        }
        let target_address = self.addressing_mode.target_address(cpu);
        cpu.program_counter = target_address;
        true
    }
}

pub struct ADC {
    pub addressing_mode: AddressingMode,
}

impl Instruction for ADC {
    fn execute(&self, cpu: &mut CPU, current_tick: u8) -> bool {
        let ticks = match self.addressing_mode {
            AddressingMode::Immediate => 2,
            AddressingMode::ZeroPage => 3,
            AddressingMode::ZeroPageX => 4,
            AddressingMode::Absolute => 4,
            AddressingMode::AbsoluteX if self.addressing_mode.is_crossing_page_boundary(cpu) => 5,
            AddressingMode::AbsoluteX => 4,
            AddressingMode::AbsoluteY if self.addressing_mode.is_crossing_page_boundary(cpu) => 5,
            AddressingMode::AbsoluteY => 4,
            AddressingMode::PreIndexedIndirect => 6,
            AddressingMode::PostIndexedIndirect => {
                if self.addressing_mode.is_crossing_page_boundary(cpu) {
                    6
                } else {
                    5
                }
            }
            _ => panic!(
                "Unsupported addressing mode for ADC: {:?}",
                self.addressing_mode
            ),
        };

        if current_tick < ticks {
            return false;
        }

        let value = self.addressing_mode.load_value(cpu);
        let pc_increment = self.addressing_mode.program_counter_increment();
        cpu.program_counter += pc_increment;

        let carry_bit = if cpu.is_flag_set(StatusFlags::Carry) {
            1
        } else {
            0
        };
        let result = cpu.accumulator as u16 + value as u16 + carry_bit;

        if result > 255 {
            cpu.set_flag(StatusFlags::Carry);
        } else {
            cpu.reset_flag(StatusFlags::Carry);
        }

        if is_overflowing_addition(cpu.accumulator, value, result) {
            cpu.set_flag(StatusFlags::Overflow);
        } else {
            cpu.reset_flag(StatusFlags::Overflow);
        }

        cpu.accumulator = result as u8;

        update_zero_flag(cpu);
        update_neg_flag(cpu);

        true
    }
}

fn update_zero_flag(cpu: &mut CPU) {
    if cpu.accumulator == 0 {
        cpu.set_flag(StatusFlags::Zero);
    } else {
        cpu.reset_flag(StatusFlags::Zero);
    }
}

fn update_neg_flag(cpu: &mut CPU) {
    if cpu.accumulator & SIGN_MASK != 0 {
        cpu.set_flag(StatusFlags::Negative);
    } else {
        cpu.reset_flag(StatusFlags::Negative);
    }
}

fn is_overflowing_addition(operand1: u8, operand2: u8, result: u16) -> bool {
    let operand1_sign = (operand1 & SIGN_MASK) != 0;
    let operand2_sign = (operand2 & SIGN_MASK) != 0;
    let result_sign = (result & (SIGN_MASK as u16)) != 0;

    // Overflow occurs when adding two positive numbers gives negative result,
    // or adding two negative numbers gives positive result
    (operand1_sign == operand2_sign) && (operand1_sign != result_sign)
}

pub fn init_op_table() -> [Option<Box<dyn Instruction>>; 256] {
    struct InstructionData {
        instruction: Box<dyn Instruction>,
        opc: u16,
    }
    let instructions = vec![
        InstructionData {
            instruction: Box::new(LDA {
                addressing_mode: AddressingMode::Immediate,
            }),
            opc: 0xA9,
        },
        InstructionData {
            instruction: Box::new(LDA {
                addressing_mode: AddressingMode::ZeroPage,
            }),
            opc: 0xA5,
        },
        InstructionData {
            instruction: Box::new(LDA {
                addressing_mode: AddressingMode::ZeroPageX,
            }),
            opc: 0xB5,
        },
        InstructionData {
            instruction: Box::new(LDA {
                addressing_mode: AddressingMode::Absolute,
            }),
            opc: 0xAD,
        },
        InstructionData {
            instruction: Box::new(LDA {
                addressing_mode: AddressingMode::AbsoluteX,
            }),
            opc: 0xBD,
        },
        InstructionData {
            instruction: Box::new(LDA {
                addressing_mode: AddressingMode::AbsoluteY,
            }),
            opc: 0xB9,
        },
        InstructionData {
            instruction: Box::new(LDA {
                addressing_mode: AddressingMode::PreIndexedIndirect,
            }),
            opc: 0xA1,
        },
        InstructionData {
            instruction: Box::new(LDA {
                addressing_mode: AddressingMode::PostIndexedIndirect,
            }),
            opc: 0xB1,
        },
        InstructionData {
            instruction: Box::new(BRK {}),
            opc: 0x00,
        },
        InstructionData {
            instruction: Box::new(NOP {}),
            opc: 0xEA,
        },
        InstructionData {
            instruction: Box::new(CLC {}),
            opc: 0x18,
        },
        InstructionData {
            instruction: Box::new(STA {
                addressing_mode: AddressingMode::ZeroPage,
            }),
            opc: 0x85,
        },
        InstructionData {
            instruction: Box::new(STA {
                addressing_mode: AddressingMode::ZeroPageX,
            }),
            opc: 0x95,
        },
        InstructionData {
            instruction: Box::new(STA {
                addressing_mode: AddressingMode::Absolute,
            }),
            opc: 0x8D,
        },
        InstructionData {
            instruction: Box::new(STA {
                addressing_mode: AddressingMode::AbsoluteX,
            }),
            opc: 0x9D,
        },
        InstructionData {
            instruction: Box::new(STA {
                addressing_mode: AddressingMode::AbsoluteY,
            }),
            opc: 0x99,
        },
        InstructionData {
            instruction: Box::new(STA {
                addressing_mode: AddressingMode::PreIndexedIndirect,
            }),
            opc: 0x81,
        },
        InstructionData {
            instruction: Box::new(STA {
                addressing_mode: AddressingMode::PostIndexedIndirect,
            }),
            opc: 0x91,
        },
        InstructionData {
            instruction: Box::new(JMP {
                addressing_mode: AddressingMode::Absolute,
            }),
            opc: 0x4C,
        },
        InstructionData {
            instruction: Box::new(JMP {
                addressing_mode: AddressingMode::Indirect,
            }),
            opc: 0x6C,
        },
        InstructionData {
            instruction: Box::new(ADC {
                addressing_mode: AddressingMode::Immediate,
            }),
            opc: 0x69,
        },
        InstructionData {
            instruction: Box::new(ADC {
                addressing_mode: AddressingMode::ZeroPage,
            }),
            opc: 0x65,
        },
        InstructionData {
            instruction: Box::new(ADC {
                addressing_mode: AddressingMode::ZeroPageX,
            }),
            opc: 0x75,
        },
        InstructionData {
            instruction: Box::new(ADC {
                addressing_mode: AddressingMode::Absolute,
            }),
            opc: 0x6D,
        },
        InstructionData {
            instruction: Box::new(ADC {
                addressing_mode: AddressingMode::AbsoluteX,
            }),
            opc: 0x7D,
        },
        InstructionData {
            instruction: Box::new(ADC {
                addressing_mode: AddressingMode::AbsoluteY,
            }),
            opc: 0x79,
        },
        InstructionData {
            instruction: Box::new(ADC {
                addressing_mode: AddressingMode::PreIndexedIndirect,
            }),
            opc: 0x61,
        },
        InstructionData {
            instruction: Box::new(ADC {
                addressing_mode: AddressingMode::PostIndexedIndirect,
            }),
            opc: 0x71,
        },
    ];
    let mut op_table: [Option<Box<dyn Instruction>>; 256] = core::array::from_fn(|_| None);
    for inst in instructions {
        let index = inst.opc as usize;
        op_table[index] = Some(inst.instruction);
    }
    op_table
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lda_immediate_positive_value() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        // Set reset vector to 0x8000
        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // LDA #$42 at address 0x8000
        rom[0x8000] = 0x42; // Immediate value

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000; // Set PC to start of our test

        let lda = LDA {
            addressing_mode: AddressingMode::Immediate,
        };

        lda.execute(&mut cpu, 2); // Execute with sufficient ticks

        assert_eq!(
            cpu.accumulator, 0x42,
            "Accumulator should contain loaded value"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Zero),
            "Zero flag should not be set"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Negative),
            "Negative flag should not be set"
        );
        assert_eq!(cpu.program_counter, 0x8001, "PC should increment by 1");
    }

    #[test]
    fn test_lda_immediate_zero_value() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // LDA #$00 at address 0x8000
        rom[0x8000] = 0x00; // Zero value

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;

        let lda = LDA {
            addressing_mode: AddressingMode::Immediate,
        };

        lda.execute(&mut cpu, 2);

        assert_eq!(cpu.accumulator, 0x00, "Accumulator should contain zero");
        assert!(
            cpu.is_flag_set(StatusFlags::Zero),
            "Zero flag should be set"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Negative),
            "Negative flag should not be set"
        );
    }

    #[test]
    fn test_lda_immediate_negative_value() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // LDA #$80 at address 0x8000 (0x80 = -128 in signed 8-bit)
        rom[0x8000] = 0x80; // Negative value

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;

        let lda = LDA {
            addressing_mode: AddressingMode::Immediate,
        };

        lda.execute(&mut cpu, 2);

        assert_eq!(cpu.accumulator, 0x80, "Accumulator should contain 0x80");
        assert!(
            !cpu.is_flag_set(StatusFlags::Zero),
            "Zero flag should not be set"
        );
        assert!(
            cpu.is_flag_set(StatusFlags::Negative),
            "Negative flag should be set"
        );
    }

    #[test]
    fn test_lda_zero_page() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // LDA $50 at address 0x8000
        rom[0x8000] = 0x50; // Zero page address

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;

        // Set value at zero page address 0x50
        cpu.write_byte(0x0050, 0x33);

        let lda = LDA {
            addressing_mode: AddressingMode::ZeroPage,
        };

        lda.execute(&mut cpu, 3);

        assert_eq!(
            cpu.accumulator, 0x33,
            "Accumulator should contain value from zero page"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Zero),
            "Zero flag should not be set"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Negative),
            "Negative flag should not be set"
        );
        assert_eq!(cpu.program_counter, 0x8001, "PC should increment by 1");
    }

    #[test]
    fn test_lda_zero_page_x() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // LDA $50,X at address 0x8000
        rom[0x8000] = 0x50; // Base zero page address

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.x = 0x05; // X register offset

        // Set value at effective address 0x50 + 0x05 = 0x55
        cpu.write_byte(0x0055, 0x77);

        let lda = LDA {
            addressing_mode: AddressingMode::ZeroPageX,
        };

        lda.execute(&mut cpu, 4);

        assert_eq!(
            cpu.accumulator, 0x77,
            "Accumulator should contain value from zero page,X"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Zero),
            "Zero flag should not be set"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Negative),
            "Negative flag should not be set"
        );
    }

    #[test]
    fn test_lda_zero_page_x_wraparound() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // LDA $FF,X at address 0x8000
        rom[0x8000] = 0xFF; // Base address near end of zero page

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.x = 0x05; // This should wrap around within zero page

        // Set value at wrapped address 0xFF + 0x05 = 0x04 (within zero page)
        cpu.write_byte(0x0004, 0x99);

        let lda = LDA {
            addressing_mode: AddressingMode::ZeroPageX,
        };

        lda.execute(&mut cpu, 4);

        assert_eq!(
            cpu.accumulator, 0x99,
            "Accumulator should contain value from wrapped zero page address"
        );
    }

    #[test]
    fn test_lda_absolute() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // LDA $1234 at address 0x8000
        rom[0x8000] = 0x34; // Low byte of absolute address
        rom[0x8001] = 0x12; // High byte of absolute address

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;

        // Set value at absolute address 0x1234
        cpu.write_byte(0x1234, 0xAB);

        let lda = LDA {
            addressing_mode: AddressingMode::Absolute,
        };

        lda.execute(&mut cpu, 4);

        assert_eq!(
            cpu.accumulator, 0xAB,
            "Accumulator should contain value from absolute address"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Zero),
            "Zero flag should not be set"
        );
        assert!(
            cpu.is_flag_set(StatusFlags::Negative),
            "Negative flag should be set for 0xAB"
        );
        assert_eq!(cpu.program_counter, 0x8002, "PC should increment by 2");
    }

    #[test]
    fn test_lda_absolute_x_no_page_boundary() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // LDA $1200,X at address 0x8000
        rom[0x8000] = 0x00; // Low byte
        rom[0x8001] = 0x12; // High byte

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.x = 0x10; // X register offset (no page boundary crossing)

        // Set value at effective address 0x1200 + 0x10 = 0x1210
        cpu.write_byte(0x1210, 0x55);

        let lda = LDA {
            addressing_mode: AddressingMode::AbsoluteX,
        };

        lda.execute(&mut cpu, 4); // 4 cycles when no page boundary crossed

        assert_eq!(
            cpu.accumulator, 0x55,
            "Accumulator should contain value from absolute,X"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Zero),
            "Zero flag should not be set"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Negative),
            "Negative flag should not be set"
        );
    }

    #[test]
    fn test_lda_absolute_x_page_boundary_crossing() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // LDA $12FF,X at address 0x8000
        rom[0x8000] = 0xFF; // Low byte
        rom[0x8001] = 0x12; // High byte

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.x = 0x05; // This will cross page boundary: 0x12FF + 0x05 = 0x1304

        // Set value at effective address 0x12FF + 0x05 = 0x1304
        cpu.write_byte(0x1304, 0x88);

        let lda = LDA {
            addressing_mode: AddressingMode::AbsoluteX,
        };

        lda.execute(&mut cpu, 5); // 5 cycles when page boundary crossed

        assert_eq!(
            cpu.accumulator, 0x88,
            "Accumulator should contain value from absolute,X with page crossing"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Zero),
            "Zero flag should not be set"
        );
        assert!(
            cpu.is_flag_set(StatusFlags::Negative),
            "Negative flag should be set for 0x88"
        );
    }

    #[test]
    fn test_lda_absolute_y() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // LDA $1200,Y at address 0x8000
        rom[0x8000] = 0x00; // Low byte
        rom[0x8001] = 0x12; // High byte

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.y = 0x20; // Y register offset

        // Set value at effective address 0x1200 + 0x20 = 0x1220
        cpu.write_byte(0x1220, 0x66);

        let lda = LDA {
            addressing_mode: AddressingMode::AbsoluteY,
        };

        lda.execute(&mut cpu, 4);

        assert_eq!(
            cpu.accumulator, 0x66,
            "Accumulator should contain value from absolute,Y"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Zero),
            "Zero flag should not be set"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Negative),
            "Negative flag should not be set"
        );
    }

    #[test]
    fn test_lda_flags_cleared_before_setting() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // LDA #$01 at address 0x8000
        rom[0x8000] = 0x01; // Positive, non-zero value

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;

        // Pre-set flags that should be cleared
        cpu.set_flag(StatusFlags::Zero);
        cpu.set_flag(StatusFlags::Negative);

        let lda = LDA {
            addressing_mode: AddressingMode::Immediate,
        };

        lda.execute(&mut cpu, 2);

        assert_eq!(cpu.accumulator, 0x01, "Accumulator should contain 0x01");
        assert!(
            !cpu.is_flag_set(StatusFlags::Zero),
            "Zero flag should be cleared"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Negative),
            "Negative flag should be cleared"
        );
    }

    #[test]
    fn test_lda_execution_timing() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;
        rom[0x8000] = 0x42;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0xFF; // Set to different value to verify no change occurs

        let lda = LDA {
            addressing_mode: AddressingMode::Immediate,
        };

        // Execute with insufficient ticks - should not complete
        lda.execute(&mut cpu, 1); // Immediate mode needs 2 ticks

        assert_eq!(
            cpu.accumulator, 0xFF,
            "Accumulator should not change with insufficient ticks"
        );
        assert_eq!(
            cpu.program_counter, 0x8000,
            "PC should not change with insufficient ticks"
        );

        // Execute with sufficient ticks - should complete
        lda.execute(&mut cpu, 2);

        assert_eq!(
            cpu.accumulator, 0x42,
            "Accumulator should change with sufficient ticks"
        );
        assert_eq!(
            cpu.program_counter, 0x8001,
            "PC should advance with sufficient ticks"
        );
    }

    #[test]
    fn test_lda_zero_page_timing() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;
        rom[0x8000] = 0x50;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.write_byte(0x0050, 0x33);

        let lda = LDA {
            addressing_mode: AddressingMode::ZeroPage,
        };

        // Test insufficient ticks
        lda.execute(&mut cpu, 2); // Zero page needs 3 ticks
        assert_eq!(
            cpu.accumulator, 0x00,
            "Should not execute with insufficient ticks"
        );

        // Test sufficient ticks
        lda.execute(&mut cpu, 3);
        assert_eq!(
            cpu.accumulator, 0x33,
            "Should execute with sufficient ticks"
        );
    }

    #[test]
    fn test_lda_absolute_timing() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;
        rom[0x8000] = 0x34;
        rom[0x8001] = 0x12;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.write_byte(0x1234, 0xAB);

        let lda = LDA {
            addressing_mode: AddressingMode::Absolute,
        };

        // Test insufficient ticks
        lda.execute(&mut cpu, 3); // Absolute needs 4 ticks
        assert_eq!(
            cpu.accumulator, 0x00,
            "Should not execute with insufficient ticks"
        );

        // Test sufficient ticks
        lda.execute(&mut cpu, 4);
        assert_eq!(
            cpu.accumulator, 0xAB,
            "Should execute with sufficient ticks"
        );
        assert_eq!(cpu.program_counter, 0x8002, "PC should advance by 2");
    }

    #[test]
    fn test_lda_boundary_values() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // Test with 0x7F (127, highest positive signed 8-bit)
        rom[0x8000] = 0x7F;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;

        let lda = LDA {
            addressing_mode: AddressingMode::Immediate,
        };

        lda.execute(&mut cpu, 2);

        assert_eq!(cpu.accumulator, 0x7F, "Should load 0x7F");
        assert!(
            !cpu.is_flag_set(StatusFlags::Zero),
            "Zero flag should not be set"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Negative),
            "Negative flag should not be set for 0x7F"
        );
    }

    #[test]
    fn test_lda_boundary_values_negative() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // Test with 0xFF (255, or -1 in signed 8-bit)
        rom[0x8000] = 0xFF;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;

        let lda = LDA {
            addressing_mode: AddressingMode::Immediate,
        };

        lda.execute(&mut cpu, 2);

        assert_eq!(cpu.accumulator, 0xFF, "Should load 0xFF");
        assert!(
            !cpu.is_flag_set(StatusFlags::Zero),
            "Zero flag should not be set"
        );
        assert!(
            cpu.is_flag_set(StatusFlags::Negative),
            "Negative flag should be set for 0xFF"
        );
    }

    #[test]
    fn test_lda_memory_addressing_edge_cases() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // Test zero page address 0x00
        rom[0x8000] = 0x00;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.write_byte(0x0000, 0x55);

        let lda = LDA {
            addressing_mode: AddressingMode::ZeroPage,
        };

        lda.execute(&mut cpu, 3);

        assert_eq!(
            cpu.accumulator, 0x55,
            "Should load from zero page address 0x00"
        );
    }

    #[test]
    fn test_lda_memory_addressing_edge_cases_high() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // Test zero page address 0xFF
        rom[0x8000] = 0xFF;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.write_byte(0x00FF, 0xAA);

        let lda = LDA {
            addressing_mode: AddressingMode::ZeroPage,
        };

        lda.execute(&mut cpu, 3);

        assert_eq!(
            cpu.accumulator, 0xAA,
            "Should load from zero page address 0xFF"
        );
    }

    #[test]
    fn test_lda_program_counter_advancement() {
        let mut cpu = CPU::new();

        // Test immediate mode PC advancement
        let mut rom = vec![0; 0xFFFE];
        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;
        rom[0x8000] = 0x42;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;

        let lda_immediate = LDA {
            addressing_mode: AddressingMode::Immediate,
        };
        lda_immediate.execute(&mut cpu, 2);
        assert_eq!(
            cpu.program_counter, 0x8001,
            "PC should advance by 1 for immediate mode"
        );

        // Test zero page mode PC advancement
        cpu.program_counter = 0x8000;
        let lda_zp = LDA {
            addressing_mode: AddressingMode::ZeroPage,
        };
        lda_zp.execute(&mut cpu, 3);
        assert_eq!(
            cpu.program_counter, 0x8001,
            "PC should advance by 1 for zero page mode"
        );
    }

    #[test]
    fn test_lda_absolute_pc_advancement() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;
        rom[0x8000] = 0x34;
        rom[0x8001] = 0x12;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.write_byte(0x1234, 0x99);

        let lda_abs = LDA {
            addressing_mode: AddressingMode::Absolute,
        };
        lda_abs.execute(&mut cpu, 4);
        assert_eq!(
            cpu.program_counter, 0x8002,
            "PC should advance by 2 for absolute mode"
        );
    }

    #[test]
    fn test_rom_lda_and_brk() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        // Set reset vector to 0x8000
        rom[0xFFFC] = 0x00; // Low byte of reset vector
        rom[0xFFFD] = 0x80; // High byte of reset vector (0x8000)

        // Program: LDA #$42, BRK
        rom[0x8000] = 0xA9; // LDA immediate opcode
        rom[0x8001] = 0x42; // Value to load into A register
        rom[0x8002] = 0x00; // BRK opcode

        // Execute the ROM
        crate::execute_rom(&mut cpu, rom);

        // Verify the A register contains the expected value
        assert_eq!(
            cpu.accumulator, 0x42,
            "A register should contain 0x42 after LDA #$42"
        );

        // Verify BRK was executed (Break flag should be set)
        assert!(
            cpu.is_flag_set(StatusFlags::Break),
            "Break flag should be set after BRK instruction"
        );

        // Verify flags set by LDA
        assert!(
            !cpu.is_flag_set(StatusFlags::Zero),
            "Zero flag should not be set for non-zero value"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Negative),
            "Negative flag should not be set for positive value"
        );
    }

    #[test]
    fn test_rom_lda_zero_and_brk() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        // Set reset vector to 0x8000
        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // Program: LDA #$00, BRK
        rom[0x8000] = 0xA9; // LDA immediate opcode
        rom[0x8001] = 0x00; // Zero value to load
        rom[0x8002] = 0x00; // BRK opcode

        crate::execute_rom(&mut cpu, rom);

        assert_eq!(
            cpu.accumulator, 0x00,
            "A register should contain 0x00 after LDA #$00"
        );

        assert!(
            cpu.is_flag_set(StatusFlags::Break),
            "Break flag should be set after BRK instruction"
        );

        assert!(
            cpu.is_flag_set(StatusFlags::Zero),
            "Zero flag should be set for zero value"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Negative),
            "Negative flag should not be set for zero value"
        );
    }

    #[test]
    fn test_rom_lda_negative_and_brk() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        // Set reset vector to 0x8000
        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // Program: LDA #$FF, BRK
        rom[0x8000] = 0xA9; // LDA immediate opcode
        rom[0x8001] = 0xFF; // Negative value (0xFF = -1 in signed 8-bit)
        rom[0x8002] = 0x00; // BRK opcode

        crate::execute_rom(&mut cpu, rom);

        assert_eq!(
            cpu.accumulator, 0xFF,
            "A register should contain 0xFF after LDA #$FF"
        );

        assert!(
            cpu.is_flag_set(StatusFlags::Break),
            "Break flag should be set after BRK instruction"
        );

        assert!(
            !cpu.is_flag_set(StatusFlags::Zero),
            "Zero flag should not be set for non-zero value"
        );
        assert!(
            cpu.is_flag_set(StatusFlags::Negative),
            "Negative flag should be set for negative value"
        );
    }

    #[test]
    fn test_nop_instruction() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        // Set reset vector to 0x8000
        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;

        // Set initial values to verify they don't change
        cpu.accumulator = 0x42;
        cpu.x = 0x33;
        cpu.y = 0x55;
        cpu.stack_pointer = 0xFD;
        cpu.set_flag(StatusFlags::Zero);

        let initial_status = cpu.get_status();

        let nop = NOP {};

        // Test insufficient ticks - should not complete
        let result = nop.execute(&mut cpu, 1);
        assert!(!result, "NOP should not complete with insufficient ticks");

        // Test sufficient ticks - should complete
        let result = nop.execute(&mut cpu, 2);
        assert!(result, "NOP should complete with sufficient ticks");

        // Verify no registers changed
        assert_eq!(cpu.accumulator, 0x42, "Accumulator should not change");
        assert_eq!(cpu.x, 0x33, "X register should not change");
        assert_eq!(cpu.y, 0x55, "Y register should not change");
        assert_eq!(cpu.stack_pointer, 0xFD, "Stack pointer should not change");
        assert_eq!(
            cpu.get_status(),
            initial_status,
            "Status flags should not change"
        );

        // PC should not change within the instruction (execute_rom handles PC increment)
        assert_eq!(
            cpu.program_counter, 0x8000,
            "PC should not change within instruction"
        );
    }

    #[test]
    fn test_rom_nop_execution() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        // Set reset vector to 0x8000
        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // Program: NOP, LDA #$42, BRK
        rom[0x8000] = 0xEA; // NOP opcode
        rom[0x8001] = 0xA9; // LDA immediate opcode
        rom[0x8002] = 0x42; // Value to load into A register
        rom[0x8003] = 0x00; // BRK opcode

        crate::execute_rom(&mut cpu, rom);

        // Verify the A register contains the expected value (NOP shouldn't affect this)
        assert_eq!(
            cpu.accumulator, 0x42,
            "A register should contain 0x42 after NOP and LDA #$42"
        );

        // Verify BRK was executed
        assert!(
            cpu.is_flag_set(StatusFlags::Break),
            "Break flag should be set after BRK instruction"
        );

        // Verify flags set by LDA (NOP shouldn't affect flags)
        assert!(
            !cpu.is_flag_set(StatusFlags::Zero),
            "Zero flag should not be set for non-zero value"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Negative),
            "Negative flag should not be set for positive value"
        );
    }

    #[test]
    fn test_sta_zero_page() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // STA $50 at address 0x8000
        rom[0x8000] = 0x50; // Zero page address

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0x42; // Value to store

        let sta = STA {
            addressing_mode: AddressingMode::ZeroPage,
        };

        sta.execute(&mut cpu, 3);

        assert_eq!(
            cpu.read_byte(0x0050),
            0x42,
            "Memory at zero page address should contain accumulator value"
        );
        assert_eq!(cpu.program_counter, 0x8001, "PC should increment by 1");
        assert_eq!(cpu.accumulator, 0x42, "Accumulator should not change");
    }

    #[test]
    fn test_sta_zero_page_x() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // STA $50,X at address 0x8000
        rom[0x8000] = 0x50; // Base zero page address

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0x77;
        cpu.x = 0x05; // X register offset

        let sta = STA {
            addressing_mode: AddressingMode::ZeroPageX,
        };

        sta.execute(&mut cpu, 4);

        // Effective address should be 0x50 + 0x05 = 0x55
        assert_eq!(
            cpu.read_byte(0x0055),
            0x77,
            "Memory at zero page,X address should contain accumulator value"
        );
        assert_eq!(cpu.program_counter, 0x8001, "PC should increment by 1");
        assert_eq!(cpu.accumulator, 0x77, "Accumulator should not change");
    }

    #[test]
    fn test_sta_zero_page_x_wraparound() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // STA $FF,X at address 0x8000
        rom[0x8000] = 0xFF; // Base address near end of zero page

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0x99;
        cpu.x = 0x05; // This should wrap around within zero page

        let sta = STA {
            addressing_mode: AddressingMode::ZeroPageX,
        };

        sta.execute(&mut cpu, 4);

        // Effective address should wrap: 0xFF + 0x05 = 0x04 (within zero page)
        assert_eq!(
            cpu.read_byte(0x0004),
            0x99,
            "Memory at wrapped zero page address should contain accumulator value"
        );
    }

    #[test]
    fn test_sta_absolute() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // STA $1234 at address 0x8000
        rom[0x8000] = 0x34; // Low byte of absolute address
        rom[0x8001] = 0x12; // High byte of absolute address

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0xAB;

        let sta = STA {
            addressing_mode: AddressingMode::Absolute,
        };

        sta.execute(&mut cpu, 4);

        assert_eq!(
            cpu.read_byte(0x1234),
            0xAB,
            "Memory at absolute address should contain accumulator value"
        );
        assert_eq!(cpu.program_counter, 0x8002, "PC should increment by 2");
        assert_eq!(cpu.accumulator, 0xAB, "Accumulator should not change");
    }

    #[test]
    fn test_sta_absolute_x() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // STA $1200,X at address 0x8000
        rom[0x8000] = 0x00; // Low byte
        rom[0x8001] = 0x12; // High byte

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0x55;
        cpu.x = 0x10; // X register offset

        let sta = STA {
            addressing_mode: AddressingMode::AbsoluteX,
        };

        sta.execute(&mut cpu, 5);

        // Effective address should be 0x1200 + 0x10 = 0x1210
        assert_eq!(
            cpu.read_byte(0x1210),
            0x55,
            "Memory at absolute,X address should contain accumulator value"
        );
        assert_eq!(cpu.program_counter, 0x8002, "PC should increment by 2");
    }

    #[test]
    fn test_sta_absolute_y() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // STA $1200,Y at address 0x8000
        rom[0x8000] = 0x00; // Low byte
        rom[0x8001] = 0x12; // High byte

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0x88;
        cpu.y = 0x20; // Y register offset

        let sta = STA {
            addressing_mode: AddressingMode::AbsoluteY,
        };

        sta.execute(&mut cpu, 5);

        // Effective address should be 0x1200 + 0x20 = 0x1220
        assert_eq!(
            cpu.read_byte(0x1220),
            0x88,
            "Memory at absolute,Y address should contain accumulator value"
        );
        assert_eq!(cpu.program_counter, 0x8002, "PC should increment by 2");
    }

    #[test]
    fn test_sta_pre_indexed_indirect() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // STA ($50,X) at address 0x8000
        rom[0x8000] = 0x50; // Base zero page address

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0xCC;
        cpu.x = 0x05; // X register offset

        // Set up indirect address at 0x50 + 0x05 = 0x55
        cpu.write_byte(0x0055, 0x34); // Low byte of target address
        cpu.write_byte(0x0056, 0x12); // High byte of target address

        let sta = STA {
            addressing_mode: AddressingMode::PreIndexedIndirect,
        };

        sta.execute(&mut cpu, 6);

        // Should store at address 0x1234
        assert_eq!(
            cpu.read_byte(0x1234),
            0xCC,
            "Memory at pre-indexed indirect address should contain accumulator value"
        );
        assert_eq!(cpu.program_counter, 0x8001, "PC should increment by 1");
    }

    #[test]
    fn test_sta_post_indexed_indirect() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // STA ($50),Y at address 0x8000
        rom[0x8000] = 0x50; // Zero page address for indirect lookup

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0xDD;
        cpu.y = 0x10; // Y register offset

        // Set up indirect address at 0x50
        cpu.write_byte(0x0050, 0x00); // Low byte of base address
        cpu.write_byte(0x0051, 0x12); // High byte of base address
        cpu.write_byte(0x1210, 0x66); // Value at address 0x1200 + 0x10 = 0x1210

        let sta = STA {
            addressing_mode: AddressingMode::PostIndexedIndirect,
        };

        sta.execute(&mut cpu, 6);

        assert_eq!(
            cpu.read_byte(0x1210),
            0xDD,
            "Memory at post-indexed indirect address should contain accumulator value"
        );
        assert_eq!(cpu.program_counter, 0x8001, "PC should increment by 1");
    }

    #[test]
    fn test_sta_timing() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;
        rom[0x8000] = 0x50; // Zero page address

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0x42;

        let sta = STA {
            addressing_mode: AddressingMode::ZeroPage,
        };

        // Should not complete with insufficient ticks
        let result = sta.execute(&mut cpu, 2);
        assert!(!result, "STA should not complete with insufficient ticks");
        assert_eq!(
            cpu.program_counter, 0x8000,
            "PC should not change when instruction doesn't complete"
        );

        // Should complete with sufficient ticks
        let result = sta.execute(&mut cpu, 3);
        assert!(result, "STA should complete with sufficient ticks");
        assert_eq!(
            cpu.read_byte(0x0050),
            0x42,
            "Memory should be updated after completion"
        );
    }

    #[test]
    fn test_sta_does_not_affect_flags() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;
        rom[0x8000] = 0x50; // Zero page address

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0x00; // Zero value

        // Set some flags before executing STA
        cpu.set_flag(StatusFlags::Zero);
        cpu.set_flag(StatusFlags::Negative);
        cpu.set_flag(StatusFlags::Carry);
        let initial_status = cpu.get_status();

        let sta = STA {
            addressing_mode: AddressingMode::ZeroPage,
        };

        sta.execute(&mut cpu, 3);

        // STA should not affect any status flags
        assert_eq!(
            cpu.get_status(),
            initial_status,
            "STA should not modify any status flags"
        );
        assert_eq!(
            cpu.read_byte(0x0050),
            0x00,
            "Memory should contain accumulator value"
        );
    }

    #[test]
    fn test_jmp_absolute() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // JMP $1234 at address 0x8000
        rom[0x8000] = 0x34; // Low byte of target address
        rom[0x8001] = 0x12; // High byte of target address

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;

        let jmp = JMP {
            addressing_mode: AddressingMode::Absolute,
        };

        jmp.execute(&mut cpu, 3);

        assert_eq!(
            cpu.program_counter, 0x1234,
            "PC should jump to absolute address 0x1234"
        );
    }

    #[test]
    fn test_jmp_absolute_timing() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;
        rom[0x8000] = 0x34;
        rom[0x8001] = 0x12;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;

        let jmp = JMP {
            addressing_mode: AddressingMode::Absolute,
        };

        // Should not complete with insufficient ticks
        let result = jmp.execute(&mut cpu, 2);
        assert!(!result, "JMP should not complete with insufficient ticks");
        assert_eq!(
            cpu.program_counter, 0x8000,
            "PC should not change when instruction doesn't complete"
        );

        // Should complete with sufficient ticks
        let result = jmp.execute(&mut cpu, 3);
        assert!(result, "JMP should complete with sufficient ticks");
        assert_eq!(
            cpu.program_counter, 0x1234,
            "PC should jump to target address after completion"
        );
    }

    #[test]
    fn test_jmp_indirect() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // JMP ($1000) at address 0x8000
        rom[0x8000] = 0x00; // Low byte of indirect address
        rom[0x8001] = 0x10; // High byte of indirect address

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;

        // Set up target address at indirect location 0x1000
        cpu.write_byte(0x1000, 0x78); // Low byte of target address
        cpu.write_byte(0x1001, 0x56); // High byte of target address

        let jmp = JMP {
            addressing_mode: AddressingMode::Indirect,
        };

        jmp.execute(&mut cpu, 5);

        // Should jump to address 0x5678 (little-endian)
        assert_eq!(
            cpu.program_counter, 0x5678,
            "PC should jump to indirect target address 0x5678"
        );
    }

    #[test]
    fn test_jmp_indirect_timing() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;
        rom[0x8000] = 0x00;
        rom[0x8001] = 0x10;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;

        // Set up target address
        cpu.write_byte(0x1000, 0x78);
        cpu.write_byte(0x1001, 0x56);

        let jmp = JMP {
            addressing_mode: AddressingMode::Indirect,
        };

        // Should not complete with insufficient ticks
        let result = jmp.execute(&mut cpu, 4);
        assert!(
            !result,
            "JMP indirect should not complete with insufficient ticks"
        );
        assert_eq!(
            cpu.program_counter, 0x8000,
            "PC should not change when instruction doesn't complete"
        );

        // Should complete with sufficient ticks
        let result = jmp.execute(&mut cpu, 5);
        assert!(result, "JMP indirect should complete with sufficient ticks");
        assert_eq!(
            cpu.program_counter, 0x5678,
            "PC should jump to indirect target address after completion"
        );
    }

    #[test]
    fn test_jmp_does_not_affect_flags() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;
        rom[0x8000] = 0x34;
        rom[0x8001] = 0x12;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;

        // Set some flags before executing JMP
        cpu.set_flag(StatusFlags::Zero);
        cpu.set_flag(StatusFlags::Negative);
        cpu.set_flag(StatusFlags::Carry);
        let initial_status = cpu.get_status();

        let jmp = JMP {
            addressing_mode: AddressingMode::Absolute,
        };

        jmp.execute(&mut cpu, 3);

        // JMP should not affect any status flags
        assert_eq!(
            cpu.get_status(),
            initial_status,
            "JMP should not modify any status flags"
        );
        assert_eq!(
            cpu.program_counter, 0x1234,
            "PC should jump to target address"
        );
    }

    #[test]
    fn test_jmp_does_not_affect_registers() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;
        rom[0x8000] = 0x34;
        rom[0x8001] = 0x12;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;

        // Set initial register values
        cpu.accumulator = 0x42;
        cpu.x = 0x33;
        cpu.y = 0x55;
        cpu.stack_pointer = 0xFD;

        let jmp = JMP {
            addressing_mode: AddressingMode::Absolute,
        };

        jmp.execute(&mut cpu, 3);

        // JMP should not affect any registers
        assert_eq!(cpu.accumulator, 0x42, "Accumulator should not change");
        assert_eq!(cpu.x, 0x33, "X register should not change");
        assert_eq!(cpu.y, 0x55, "Y register should not change");
        assert_eq!(cpu.stack_pointer, 0xFD, "Stack pointer should not change");
        assert_eq!(
            cpu.program_counter, 0x1234,
            "PC should jump to target address"
        );
    }

    #[test]
    fn test_jmp_absolute_edge_cases() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // Test jump to address 0x0000
        rom[0x8000] = 0x00;
        rom[0x8001] = 0x00;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;

        let jmp = JMP {
            addressing_mode: AddressingMode::Absolute,
        };

        jmp.execute(&mut cpu, 3);

        assert_eq!(
            cpu.program_counter, 0x0000,
            "PC should jump to address 0x0000"
        );
    }

    #[test]
    fn test_jmp_absolute_high_address() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // Test jump to address 0xFFFF
        rom[0x8000] = 0xFF;
        rom[0x8001] = 0xFF;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;

        let jmp = JMP {
            addressing_mode: AddressingMode::Absolute,
        };

        jmp.execute(&mut cpu, 3);

        assert_eq!(
            cpu.program_counter, 0xFFFF,
            "PC should jump to address 0xFFFF"
        );
    }

    #[test]
    fn test_jmp_indirect_edge_cases() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // JMP ($0000) - indirect from address 0x0000
        rom[0x8000] = 0x00;
        rom[0x8001] = 0x00;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;

        // Set up target address at 0x0000
        cpu.write_byte(0x0000, 0xAB);
        cpu.write_byte(0x0001, 0xCD);

        let jmp = JMP {
            addressing_mode: AddressingMode::Indirect,
        };

        jmp.execute(&mut cpu, 5);

        assert_eq!(
            cpu.program_counter, 0xCDAB,
            "PC should jump to indirect target address 0xCDAB"
        );
    }

    #[test]
    fn test_jmp_indirect_page_boundary() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // JMP ($10FF) - test page boundary behavior
        rom[0x8000] = 0xFF;
        rom[0x8001] = 0x10;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;

        // Set up target address at page boundary
        cpu.write_byte(0x10FF, 0x12); // Low byte
        cpu.write_byte(0x1100, 0x34); // High byte (crosses page boundary)

        let jmp = JMP {
            addressing_mode: AddressingMode::Indirect,
        };

        jmp.execute(&mut cpu, 5);

        assert_eq!(
            cpu.program_counter, 0x3412,
            "PC should jump to address 0x3412 even with page boundary crossing"
        );
    }

    #[test]
    fn test_jmp_self_loop() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // JMP $8000 - jump to itself (infinite loop)
        rom[0x8000] = 0x00;
        rom[0x8001] = 0x80;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;

        let jmp = JMP {
            addressing_mode: AddressingMode::Absolute,
        };

        jmp.execute(&mut cpu, 3);

        assert_eq!(
            cpu.program_counter, 0x8000,
            "PC should jump back to itself creating a loop"
        );
    }

    #[test]
    fn test_jmp_indirect_self_reference() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // JMP ($1000) where $1000 contains $8000
        rom[0x8000] = 0x00;
        rom[0x8001] = 0x10;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;

        // Set up indirect address to point back to 0x8000
        cpu.write_byte(0x1000, 0x00);
        cpu.write_byte(0x1001, 0x80);

        let jmp = JMP {
            addressing_mode: AddressingMode::Indirect,
        };

        jmp.execute(&mut cpu, 5);

        assert_eq!(
            cpu.program_counter, 0x8000,
            "PC should jump back to 0x8000 through indirect addressing"
        );
    }

    #[test]
    fn test_adc_immediate_basic() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // ADC #$30 at address 0x8000
        rom[0x8000] = 0x30; // Value to add

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0x10; // Initial accumulator value

        let adc = ADC {
            addressing_mode: AddressingMode::Immediate,
        };

        adc.execute(&mut cpu, 2);

        assert_eq!(
            cpu.accumulator, 0x40,
            "Accumulator should contain 0x10 + 0x30 = 0x40"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Carry),
            "Carry flag should not be set"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Zero),
            "Zero flag should not be set"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Negative),
            "Negative flag should not be set"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Overflow),
            "Overflow flag should not be set"
        );
        assert_eq!(cpu.program_counter, 0x8001, "PC should increment by 1");
    }

    #[test]
    fn test_adc_immediate_with_carry() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;
        rom[0x8000] = 0x30;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0x10;
        cpu.set_flag(StatusFlags::Carry); // Set carry flag

        let adc = ADC {
            addressing_mode: AddressingMode::Immediate,
        };

        adc.execute(&mut cpu, 2);

        assert_eq!(
            cpu.accumulator, 0x41,
            "Accumulator should contain 0x10 + 0x30 + 1 = 0x41"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Carry),
            "Carry flag should be cleared"
        );
    }

    #[test]
    fn test_adc_immediate_carry_out() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;
        rom[0x8000] = 0x01;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0xFF; // Will cause carry out

        let adc = ADC {
            addressing_mode: AddressingMode::Immediate,
        };

        adc.execute(&mut cpu, 2);

        assert_eq!(cpu.accumulator, 0x00, "Accumulator should wrap to 0x00");
        assert!(
            cpu.is_flag_set(StatusFlags::Carry),
            "Carry flag should be set"
        );
        assert!(
            cpu.is_flag_set(StatusFlags::Zero),
            "Zero flag should be set"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Negative),
            "Negative flag should not be set"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Overflow),
            "Overflow flag should not be set"
        );
    }

    #[test]
    fn test_adc_immediate_overflow_positive() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;
        rom[0x8000] = 0x01;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0x7F; // Adding 1 to 127 causes signed overflow

        let adc = ADC {
            addressing_mode: AddressingMode::Immediate,
        };

        adc.execute(&mut cpu, 2);

        assert_eq!(cpu.accumulator, 0x80, "Result should be 0x80");
        assert!(
            !cpu.is_flag_set(StatusFlags::Carry),
            "Carry flag should not be set"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Zero),
            "Zero flag should not be set"
        );
        assert!(
            cpu.is_flag_set(StatusFlags::Negative),
            "Negative flag should be set"
        );
        assert!(
            cpu.is_flag_set(StatusFlags::Overflow),
            "Overflow flag should be set"
        );
    }

    #[test]
    fn test_adc_immediate_overflow_negative() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;
        rom[0x8000] = 0xFF; // -1 in signed 8-bit

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0x80; // -128 in signed 8-bit

        let adc = ADC {
            addressing_mode: AddressingMode::Immediate,
        };

        adc.execute(&mut cpu, 2);

        assert_eq!(cpu.accumulator, 0x7F, "Result should be 0x7F");
        assert!(
            cpu.is_flag_set(StatusFlags::Carry),
            "Carry flag should be set"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Zero),
            "Zero flag should not be set"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Negative),
            "Negative flag should not be set"
        );
        assert!(
            cpu.is_flag_set(StatusFlags::Overflow),
            "Overflow flag should be set"
        );
    }

    #[test]
    fn test_adc_zero_page() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;
        rom[0x8000] = 0x50; // Zero page address

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0x20;
        cpu.write_byte(0x0050, 0x15); // Value at zero page address

        let adc = ADC {
            addressing_mode: AddressingMode::ZeroPage,
        };

        adc.execute(&mut cpu, 3);

        assert_eq!(
            cpu.accumulator, 0x35,
            "Accumulator should contain 0x20 + 0x15 = 0x35"
        );
        assert_eq!(cpu.program_counter, 0x8001, "PC should increment by 1");
    }

    #[test]
    fn test_adc_zero_page_x() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;
        rom[0x8000] = 0x50; // Base zero page address

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0x25;
        cpu.x = 0x05; // X register offset
        cpu.write_byte(0x0055, 0x1A); // Value at effective address 0x50 + 0x05 = 0x55

        let adc = ADC {
            addressing_mode: AddressingMode::ZeroPageX,
        };

        adc.execute(&mut cpu, 4);

        assert_eq!(
            cpu.accumulator, 0x3F,
            "Accumulator should contain 0x25 + 0x1A = 0x3F"
        );
    }

    #[test]
    fn test_adc_absolute() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;
        rom[0x8000] = 0x34; // Low byte of absolute address
        rom[0x8001] = 0x12; // High byte of absolute address

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0x40;
        cpu.write_byte(0x1234, 0x30); // Value at absolute address

        let adc = ADC {
            addressing_mode: AddressingMode::Absolute,
        };

        adc.execute(&mut cpu, 4);

        assert_eq!(
            cpu.accumulator, 0x70,
            "Accumulator should contain 0x40 + 0x30 = 0x70"
        );
        assert_eq!(cpu.program_counter, 0x8002, "PC should increment by 2");
    }

    #[test]
    fn test_adc_absolute_x_no_page_boundary() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;
        rom[0x8000] = 0x00; // Low byte
        rom[0x8001] = 0x12; // High byte

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0x11;
        cpu.x = 0x10; // X register offset (no page boundary crossing)
        cpu.write_byte(0x1210, 0x22); // Value at effective address 0x1200 + 0x10 = 0x1210

        let adc = ADC {
            addressing_mode: AddressingMode::AbsoluteX,
        };

        adc.execute(&mut cpu, 4); // 4 cycles when no page boundary crossed

        assert_eq!(
            cpu.accumulator, 0x33,
            "Accumulator should contain 0x11 + 0x22 = 0x33"
        );
    }

    #[test]
    fn test_adc_absolute_x_page_boundary_crossing() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;
        rom[0x8000] = 0xFF; // Low byte
        rom[0x8001] = 0x12; // High byte

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0x44;
        cpu.x = 0x05; // This will cross page boundary: 0x12FF + 0x05 = 0x1304
        cpu.write_byte(0x1304, 0x33); // Value at effective address

        let adc = ADC {
            addressing_mode: AddressingMode::AbsoluteX,
        };

        adc.execute(&mut cpu, 5); // 5 cycles when page boundary crossed

        assert_eq!(
            cpu.accumulator, 0x77,
            "Accumulator should contain 0x44 + 0x33 = 0x77"
        );
    }

    #[test]
    fn test_adc_absolute_y() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;
        rom[0x8000] = 0x00; // Low byte
        rom[0x8001] = 0x12; // High byte of absolute address

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0x55;
        cpu.y = 0x20; // Y register offset
        cpu.write_byte(0x1220, 0x11); // Value at effective address 0x1200 + 0x20 = 0x1220

        let adc = ADC {
            addressing_mode: AddressingMode::AbsoluteY,
        };

        adc.execute(&mut cpu, 4);

        assert_eq!(
            cpu.accumulator, 0x66,
            "Accumulator should contain 0x55 + 0x11 = 0x66"
        );
    }

    #[test]
    fn test_adc_pre_indexed_indirect() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;
        rom[0x8000] = 0x50; // Base zero page address

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0x88;
        cpu.x = 0x05; // X register offset

        // Set up indirect address at 0x50 + 0x05 = 0x55
        cpu.write_byte(0x0055, 0x34); // Low byte of target address
        cpu.write_byte(0x0056, 0x12); // High byte of target address
        cpu.write_byte(0x1234, 0x77); // Value at target address

        let adc = ADC {
            addressing_mode: AddressingMode::PreIndexedIndirect,
        };

        adc.execute(&mut cpu, 6);

        assert_eq!(
            cpu.accumulator, 0xFF,
            "Accumulator should contain 0x88 + 0x77 = 0xFF"
        );
        assert_eq!(cpu.program_counter, 0x8001, "PC should increment by 1");
    }

    #[test]
    fn test_adc_post_indexed_indirect() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;
        rom[0x8000] = 0x50; // Zero page address for indirect lookup

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0x99;
        cpu.y = 0x10; // Y register offset

        // Set up indirect address at 0x50
        cpu.write_byte(0x0050, 0x00); // Low byte of base address
        cpu.write_byte(0x0051, 0x12); // High byte of base address
        cpu.write_byte(0x1210, 0x66); // Value at address 0x1200 + 0x10 = 0x1210

        let adc = ADC {
            addressing_mode: AddressingMode::PostIndexedIndirect,
        };

        adc.execute(&mut cpu, 5);

        assert_eq!(
            cpu.accumulator, 0xFF,
            "Accumulator should contain 0x99 + 0x66 = 0xFF"
        );
        assert_eq!(cpu.program_counter, 0x8001, "PC should increment by 1");
    }

    #[test]
    fn test_adc_timing() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;
        rom[0x8000] = 0x42;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0x10;

        let adc = ADC {
            addressing_mode: AddressingMode::Immediate,
        };

        // Should not complete with insufficient ticks
        let result = adc.execute(&mut cpu, 1);
        assert!(!result, "ADC should not complete with insufficient ticks");
        assert_eq!(
            cpu.accumulator, 0x10,
            "Accumulator should not change with insufficient ticks"
        );

        // Should complete with sufficient ticks
        let result = adc.execute(&mut cpu, 2);
        assert!(result, "ADC should complete with sufficient ticks");
        assert_eq!(
            cpu.accumulator, 0x52,
            "Accumulator should change with sufficient ticks"
        );
    }

    #[test]
    fn test_adc_flag_combinations() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;
        rom[0x8000] = 0x00; // Adding zero

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0x00; // Zero accumulator
        cpu.set_flag(StatusFlags::Carry); // Set carry

        let adc = ADC {
            addressing_mode: AddressingMode::Immediate,
        };

        adc.execute(&mut cpu, 2);

        // 0x00 + 0x00 + 1 (carry) = 0x01
        assert_eq!(cpu.accumulator, 0x01, "Result should be 0x01");
        assert!(
            !cpu.is_flag_set(StatusFlags::Carry),
            "Carry flag should be cleared"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Zero),
            "Zero flag should not be set"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Negative),
            "Negative flag should not be set"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Overflow),
            "Overflow flag should not be set"
        );
    }

    #[test]
    fn test_adc_negative_flag() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;
        rom[0x8000] = 0x10; // Add positive number to negative accumulator

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0x80; // Start with negative number (-128)

        let adc = ADC {
            addressing_mode: AddressingMode::Immediate,
        };

        adc.execute(&mut cpu, 2);

        // 0x80 (-128) + 0x10 (16) = 0x90 (-112) - no overflow, just negative result
        assert_eq!(cpu.accumulator, 0x90, "Result should be 0x90");
        assert!(
            !cpu.is_flag_set(StatusFlags::Carry),
            "Carry flag should not be set"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Zero),
            "Zero flag should not be set"
        );
        assert!(
            cpu.is_flag_set(StatusFlags::Negative),
            "Negative flag should be set"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Overflow),
            "Overflow flag should not be set"
        );
    }

    #[test]
    fn test_adc_multiple_operations() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;
        rom[0x8000] = 0x20; // First ADC immediate value
        rom[0x8001] = 0xE0; // Second ADC immediate value

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.accumulator = 0x10;

        // First ADC with immediate value 0x20
        let adc1 = ADC {
            addressing_mode: AddressingMode::Immediate,
        };
        adc1.execute(&mut cpu, 2);

        assert_eq!(cpu.accumulator, 0x30, "First ADC: 0x10 + 0x20 = 0x30");
        assert!(
            !cpu.is_flag_set(StatusFlags::Carry),
            "No carry after first ADC"
        );

        // Second ADC with immediate value 0xE0 (should cause carry)
        cpu.program_counter = 0x8001;
        let adc2 = ADC {
            addressing_mode: AddressingMode::Immediate,
        };
        adc2.execute(&mut cpu, 2);

        assert_eq!(
            cpu.accumulator, 0x10,
            "Second ADC: 0x30 + 0xE0 = 0x10 (with carry)"
        );
        assert!(
            cpu.is_flag_set(StatusFlags::Carry),
            "Carry should be set after second ADC"
        );
    }

    #[test]
    fn test_clc_basic() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;

        // Set carry flag before executing CLC
        cpu.set_flag(StatusFlags::Carry);

        let clc = CLC {};

        clc.execute(&mut cpu, 2);

        assert!(
            !cpu.is_flag_set(StatusFlags::Carry),
            "Carry flag should be cleared after CLC"
        );
    }

    #[test]
    fn test_clc_timing() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;
        cpu.set_flag(StatusFlags::Carry);

        let clc = CLC {};

        // Should not complete with insufficient ticks
        let result = clc.execute(&mut cpu, 1);
        assert!(!result, "CLC should not complete with insufficient ticks");
        assert!(
            cpu.is_flag_set(StatusFlags::Carry),
            "Carry flag should not change with insufficient ticks"
        );

        // Should complete with sufficient ticks
        let result = clc.execute(&mut cpu, 2);
        assert!(result, "CLC should complete with sufficient ticks");
        assert!(
            !cpu.is_flag_set(StatusFlags::Carry),
            "Carry flag should be cleared with sufficient ticks"
        );
    }

    #[test]
    fn test_clc_does_not_affect_other_flags() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;

        // Set all flags before executing CLC
        cpu.set_flag(StatusFlags::Carry);
        cpu.set_flag(StatusFlags::Zero);
        cpu.set_flag(StatusFlags::Negative);
        cpu.set_flag(StatusFlags::Overflow);
        cpu.set_flag(StatusFlags::Break);
        cpu.set_flag(StatusFlags::Decimal);
        cpu.set_flag(StatusFlags::InterruptDisable);

        let clc = CLC {};

        clc.execute(&mut cpu, 2);

        // Only carry flag should be cleared
        assert!(
            !cpu.is_flag_set(StatusFlags::Carry),
            "Carry flag should be cleared"
        );
        assert!(
            cpu.is_flag_set(StatusFlags::Zero),
            "Zero flag should remain set"
        );
        assert!(
            cpu.is_flag_set(StatusFlags::Negative),
            "Negative flag should remain set"
        );
        assert!(
            cpu.is_flag_set(StatusFlags::Overflow),
            "Overflow flag should remain set"
        );
        assert!(
            cpu.is_flag_set(StatusFlags::Break),
            "Break flag should remain set"
        );
        assert!(
            cpu.is_flag_set(StatusFlags::Decimal),
            "Decimal flag should remain set"
        );
        assert!(
            cpu.is_flag_set(StatusFlags::InterruptDisable),
            "Interrupt disable flag should remain set"
        );
    }

    #[test]
    fn test_clc_does_not_affect_registers() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;

        // Set initial register values
        cpu.accumulator = 0x42;
        cpu.x = 0x33;
        cpu.y = 0x55;
        cpu.stack_pointer = 0xFD;
        cpu.set_flag(StatusFlags::Carry);

        let clc = CLC {};

        clc.execute(&mut cpu, 2);

        // CLC should not affect any registers
        assert_eq!(cpu.accumulator, 0x42, "Accumulator should not change");
        assert_eq!(cpu.x, 0x33, "X register should not change");
        assert_eq!(cpu.y, 0x55, "Y register should not change");
        assert_eq!(cpu.stack_pointer, 0xFD, "Stack pointer should not change");
        assert!(
            !cpu.is_flag_set(StatusFlags::Carry),
            "Only carry flag should be cleared"
        );
    }

    #[test]
    fn test_clc_when_carry_already_clear() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        cpu.insert_rom(rom);
        cpu.program_counter = 0x8000;

        // Ensure carry flag is already clear
        cpu.reset_flag(StatusFlags::Carry);

        let clc = CLC {};

        clc.execute(&mut cpu, 2);

        // Carry flag should remain clear
        assert!(
            !cpu.is_flag_set(StatusFlags::Carry),
            "Carry flag should remain clear"
        );
    }

    #[test]
    fn test_rom_clc_execution() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        // Set reset vector to 0x8000
        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // Program: CLC, BRK
        rom[0x8000] = 0x18; // CLC opcode
        rom[0x8001] = 0x00; // BRK opcode

        // Set carry flag before execution
        cpu.set_flag(StatusFlags::Carry);

        crate::execute_rom(&mut cpu, rom);

        // Verify carry flag was cleared
        assert!(
            !cpu.is_flag_set(StatusFlags::Carry),
            "Carry flag should be cleared after CLC"
        );

        // Verify BRK was executed
        assert!(
            cpu.is_flag_set(StatusFlags::Break),
            "Break flag should be set after BRK instruction"
        );
    }

    #[test]
    fn test_clc_followed_by_adc() {
        let mut cpu = CPU::new();
        let mut rom = vec![0; 0xFFFE];

        // Set reset vector to 0x8000
        rom[0xFFFC] = 0x00;
        rom[0xFFFD] = 0x80;

        // Program: CLC, ADC #$01, BRK
        rom[0x8000] = 0x18; // CLC opcode
        rom[0x8001] = 0x69; // ADC immediate opcode
        rom[0x8002] = 0x01; // Value to add
        rom[0x8003] = 0x00; // BRK opcode

        cpu.accumulator = 0x00;
        cpu.set_flag(StatusFlags::Carry); // Set carry flag

        crate::execute_rom(&mut cpu, rom);

        // Verify CLC cleared the carry flag, so ADC only adds 0x01
        assert_eq!(
            cpu.accumulator, 0x01,
            "Accumulator should contain 0x01 (0x00 + 0x01, no carry)"
        );
        assert!(
            !cpu.is_flag_set(StatusFlags::Carry),
            "Carry flag should not be set after adding 0x01 to 0x00"
        );
    }
}
