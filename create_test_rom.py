# Create a simple test ROM with LDA and BRK
# ROM structure:
# - 64KB total (0x10000 bytes)
# - Reset vector at 0xFFFC-0xFFFD points to 0x8000
# - Program at 0x8000: LDA #$42, BRK

import struct

# Create 64KB ROM filled with zeros
rom = bytearray(0x10000)

# Set reset vector to point to 0x8000
rom[0xFFFC] = 0x00  # Low byte
rom[0xFFFD] = 0x80  # High byte

# Program at 0x8000
rom[0x8000] = 0xA9  # LDA immediate opcode
rom[0x8001] = 0x42  # Load value 0x42 into A register
rom[0x8002] = 0x00  # BRK opcode

# Write ROM to file
with open('test.rom', 'wb') as f:
    f.write(rom)

print("Created test.rom with LDA #$42, BRK program")
