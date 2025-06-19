# Create a more complex test ROM that uses memory
import struct

# Create 64KB ROM filled with zeros
rom = bytearray(0x10000)

# Set reset vector to point to 0x8000
rom[0xFFFC] = 0x00  # Low byte
rom[0xFFFD] = 0x80  # High byte

# More complex program at 0x8000
addr = 0x8000

# LDA #$AA - Load 0xAA into A register
rom[addr] = 0xA9; addr += 1
rom[addr] = 0xAA; addr += 1

# LDA #$00 - Load 0 to test zero flag
rom[addr] = 0xA9; addr += 1 
rom[addr] = 0x00; addr += 1

# LDA #$FF - Load 0xFF to test negative flag
rom[addr] = 0xA9; addr += 1
rom[addr] = 0xFF; addr += 1

# BRK - Stop execution
rom[addr] = 0x00; addr += 1

# Write ROM to file
with open('complex_test.rom', 'wb') as f:
    f.write(rom)

print("Created complex_test.rom with multiple LDA instructions")
