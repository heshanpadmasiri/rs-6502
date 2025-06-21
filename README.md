# RS-6502 - 6502 CPU Emulator

A 6502 microprocessor emulator written in Rust that can execute ROM files and provides cycle-accurate timing simulation.

## Setup

### Prerequisites

- [Rust](https://rustup.rs/) (latest stable version)

### Installation

1. Clone the repository:
```bash
git clone <repository-url>
cd rs-6502
```

2. Build the project:
```bash
cargo build --release
```

## Usage

### Running the Emulator

```bash
cargo run <rom_file> [--heap-dump]
```

**Arguments:**
- `<rom_file>`: Path to the ROM file to execute
- `--heap-dump`: Optional flag to print memory state in hex pages

**Example:**
```bash
cargo run test.rom
cargo run test.rom --heap-dump
```

### Creating ROM Files

The project includes Python scripts to create test ROM files:

#### Simple Test ROM
```bash
python3 create_test_rom.py
```
Creates `test.rom` with a simple program: `LDA #$42, BRK`

#### Complex Test ROM
```bash
python3 create_complex_rom.py
```
Creates `complex_test.rom` with multiple LDA instructions testing different values.

### Running Tests

```bash
cargo test
```

## ROM File Format

ROM files must be 64KB (65536 bytes) and follow the 6502 memory layout:

- **0x0000-0xFFFF**: Full 64KB address space
- **0xFFFC-0xFFFD**: Reset vector (little-endian format)
  - 0xFFFC: Low byte of start address
  - 0xFFFD: High byte of start address
- **Program code**: Located at the address specified by the reset vector

## Supported Instructions

- **LDA** - Load Accumulator
- **BRK** - Break

## Addressing Modes

The emulator supports the following addressing modes:

- **Immediate**: `#$value` - Use the value directly
- **Absolute**: `$address` - Use the value at the 16-bit address
- **Zero Page**: `$page` - Use the value at the 8-bit address in zero page (0x00-0xFF)
- **Zero Page,X**: `$page,X` - Zero page address + X register
- **Zero Page,Y**: `$page,Y` - Zero page address + Y register
- **Absolute,X**: `$address,X` - 16-bit address + X register
- **Absolute,Y**: `$address,Y` - 16-bit address + Y register
- **Indirect**: `($address)` - Jump to address stored at the given address
- **(Indirect,X)** / **PreIndexedIndirect**: `($page,X)` - Zero page address + X, then use that as pointer
- **(Indirect),Y** / **PostIndexedIndirect**: `($page),Y` - Use zero page as pointer, then add Y

## CPU Registers

- **PC** (Program Counter): 16-bit, points to the next instruction
- **A** (Accumulator): 8-bit, primary register for arithmetic operations
- **X** (X Register): 8-bit, index register
- **Y** (Y Register): 8-bit, index register  
- **SP** (Stack Pointer): 8-bit, points to next available stack location (0x0100-0x01FF)
- **P** (Processor Status): 8-bit, contains status flags

## Status Flags

- **N** (Negative): Set when result is negative (bit 7 set)
- **V** (Overflow): Set when signed arithmetic overflow occurs
- **U** (Unused): Always set to 1
- **B** (Break): Set when BRK instruction is executed
- **D** (Decimal): Decimal mode flag (not implemented in this emulator)
- **I** (Interrupt Disable): Interrupt disable flag
- **Z** (Zero): Set when result is zero
- **C** (Carry): Set when arithmetic carry/borrow occurs

## Examples

### Example 1: Simple Program
```assembly
LDA #$42    ; Load 0x42 into accumulator
BRK         ; Stop execution
```

### Example 2: Memory Operations
```assembly
LDA #$AA    ; Load 0xAA into accumulator
LDA $50     ; Load value from zero page address 0x50
LDA $1234,X ; Load value from absolute address 0x1234 + X register
BRK         ; Stop execution
```
