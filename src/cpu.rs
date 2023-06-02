use bitflags::bitflags;

use crate::opcodes::OPCODES_MAP;

bitflags! {
    pub struct CpuFlag: u8 {
        const CARRY = 0b0000_0001;
        const ZERO = 0b0000_0010;
        const INTERRUPT_DISABLE = 0b0000_0100;
        const DECIMAL_MODE = 0b0000_1000;
        const BREAK = 0b0001_0000;
        const BREAK2 = 0b0010_0000;
        const OVERFLOW = 0b0100_0000;
        const NEGATIVE = 0b1000_0000;
    }
}

const STACK: u16 = 0x0100;
const STACK_REST: u8 = 0xFD;

pub struct CPU {
    pub register_a: u8,
    pub register_x: u8,
    pub register_y: u8,
    pub status: CpuFlag,
    pub program_counter: u16,
    pub stack_pointer: u8,
    pub memeory: [u8; 0xffff],
}

#[derive(Debug)]
#[allow(non_camel_case_types)]
pub enum AddressingMode {
    Immediate,
    // Accumulator,
    ZeroPage,
    ZeroPage_X,
    ZeroPage_Y,
    Absolute,
    Absolute_X,
    Absolute_Y,
    Indirect,
    Indirect_X,
    Indirect_Y,
    NoneAddressing,
}

impl CPU {
    pub fn new() -> Self {
        CPU {
            register_a: 0,
            register_x: 0,
            register_y: 0,
            status: CpuFlag::empty(),
            program_counter: 0,
            stack_pointer: STACK_REST,
            memeory: [0; 0xffff],
        }
    }

    fn mem_read(&self, addr: u16) -> u8 {
        self.memeory[addr as usize]
    }

    fn mem_write(&mut self, addr: u16, data: u8) {
        self.memeory[addr as usize] = data;
    }

    fn mem_read_u16(&self, addr: u16) -> u16 {
        u16::from_le_bytes([self.mem_read(addr), self.mem_read(addr + 1)])
    }

    fn mem_write_u16(&mut self, addr: u16, data: u16) {
        data.to_le_bytes().iter().enumerate().for_each(|(i, b)| {
            self.mem_write(addr + i as u16, *b);
        });
    }

    fn stack_push(&mut self, data: u8) {
        self.mem_write(STACK + self.stack_pointer as u16, data);
        self.stack_pointer = self.stack_pointer.wrapping_sub(1);
    }

    fn stack_pop(&mut self) -> u8 {
        self.stack_pointer = self.stack_pointer.wrapping_add(1);
        self.mem_read(STACK + self.stack_pointer as u16)
    }

    fn stack_push_u16(&mut self, data: u16) {
        self.stack_push((data >> 8) as u8);
        self.stack_push(data as u8);
    }

    fn stack_pop_u16(&mut self) -> u16 {
        u16::from_le_bytes([self.stack_pop(), self.stack_pop()])
    }

    // https://skilldrick.github.io/easy6502/#addressing
    fn get_operand_address(&self, mode: &AddressingMode) -> u16 {
        match mode {
            AddressingMode::Immediate => self.program_counter,
            AddressingMode::ZeroPage => self.mem_read(self.program_counter) as u16,
            AddressingMode::ZeroPage_X => self
                .mem_read(self.program_counter)
                .wrapping_add(self.register_x) as u16,
            AddressingMode::ZeroPage_Y => self
                .mem_read(self.program_counter)
                .wrapping_add(self.register_y) as u16,
            AddressingMode::Absolute => self.mem_read_u16(self.program_counter),
            AddressingMode::Absolute_X => self
                .mem_read_u16(self.program_counter)
                .wrapping_add(self.register_x as u16),
            AddressingMode::Absolute_Y => self
                .mem_read_u16(self.program_counter)
                .wrapping_add(self.register_y as u16),
            AddressingMode::Indirect => {
                let ptr = self.mem_read_u16(self.program_counter);

                //6502 bug mode with with page boundary:
                //  if address $3000 contains $40, $30FF contains $80, and $3100 contains $50,
                // the result of JMP ($30FF) will be a transfer of control to $4080 rather than $5080 as you intended
                // i.e. the 6502 took the low byte of the address from $30FF and the high byte from $3000
                if ptr & 0x00FF == 0x00FF {
                    let lo = self.mem_read(ptr);
                    let hi = self.mem_read(ptr & 0xFF00);
                    (hi as u16) << 8 | (lo as u16)
                } else {
                    self.mem_read_u16(ptr)
                }
            }
            AddressingMode::Indirect_X => {
                let base = self.mem_read(self.program_counter);
                let ptr: u8 = base.wrapping_add(self.register_x);
                u16::from_le_bytes([
                    self.mem_read(ptr as u16),
                    self.mem_read(ptr.wrapping_add(1) as u16),
                ])
            }
            AddressingMode::Indirect_Y => {
                let base = self.mem_read(self.program_counter);
                let ptr: u8 = base.wrapping_add(self.register_y);
                u16::from_le_bytes([
                    self.mem_read(ptr as u16),
                    self.mem_read(ptr.wrapping_add(1) as u16),
                ])
            }
            AddressingMode::NoneAddressing => {
                panic!("mode {:?} is not supported", mode);
            }
        }
    }

    pub fn reset(&mut self) {
        self.register_a = 0;
        self.register_x = 0;
        self.register_y = 0;
        self.status = CpuFlag::empty();

        // https://bugzmanov.github.io/nes_ebook/chapter_3_2.html
        self.program_counter = self.mem_read_u16(0xfffc);
    }

    pub fn load(&mut self, program: Vec<u8>) {
        self.memeory[0x8000..(0x8000 + program.len())].copy_from_slice(&program[..]);

        // Set program counter
        self.mem_write_u16(0xfffc, 0x8000);
    }

    pub fn load_and_run(&mut self, program: Vec<u8>) {
        self.load(program);
        self.reset();
        self.run()
    }

    ///
    /// The CPU works in a constant cycle:
    /// - Fetch next execution instruction from the instruction memory
    /// - Decode the instruction
    /// - Execute the Instruction
    /// - Repeat the cycle
    pub fn run(&mut self) {
        loop {
            // Fetch next execution instruction from the instruction memory
            let code = self.mem_read(self.program_counter);
            self.program_counter += 1;
            let program_counter_state = self.program_counter;

            let opcode = OPCODES_MAP
                .get(&code)
                .expect(&format!("Invalid opscode: {:?}", code));

            // Execute the Instruction
            match opcode.name {
                "ADC" => {
                    self.adc(&opcode.mode);
                }
                "AND" => {
                    self.and(&opcode.mode);
                }
                "ASL" => {
                    self.asl(&opcode.mode);
                }
                "BCC" => {
                    self.branch(!self.status.contains(CpuFlag::CARRY));
                }
                "BCS" => {
                    self.branch(self.status.contains(CpuFlag::CARRY));
                }
                "BEQ" => {
                    self.branch(self.status.contains(CpuFlag::ZERO));
                }
                "BIT" => {
                    self.bit(&opcode.mode);
                }
                "BMI" => {
                    self.branch(self.status.contains(CpuFlag::NEGATIVE));
                }
                "BNE" => {
                    self.branch(self.status.contains(CpuFlag::ZERO));
                }
                "BPL" => {
                    self.branch(!self.status.contains(CpuFlag::NEGATIVE));
                }
                "BRK" => {
                    return;
                }
                "BVC" => self.branch(!self.status.contains(CpuFlag::OVERFLOW)),
                "BVS" => {
                    self.branch(self.status.contains(CpuFlag::OVERFLOW));
                }
                "CLC" => {
                    self.status.set(CpuFlag::CARRY, false);
                }
                "CLD" => {
                    self.status.set(CpuFlag::DECIMAL_MODE, false);
                }
                "CLI" => {
                    self.status.set(CpuFlag::INTERRUPT_DISABLE, false);
                }
                "CLV" => {
                    self.status.set(CpuFlag::OVERFLOW, false);
                }
                "CMP" => {
                    self.compare(self.register_a, &opcode.mode);
                }
                "CPX" => {
                    self.compare(self.register_x, &opcode.mode);
                }
                "CPY" => {
                    self.compare(self.register_y, &opcode.mode);
                }
                "DEC" => {
                    self.dec(&opcode.mode);
                }
                "DEX" => {
                    self.dex();
                }
                "DEY" => {
                    self.dey();
                }
                "EOR" => {
                    self.eor(&opcode.mode);
                }
                "INC" => {
                    self.inc(&opcode.mode);
                }
                "INX" => {
                    self.inx();
                }
                "INY" => {
                    self.iny();
                }
                "JMP" => {
                    self.jmp(&opcode.mode);
                }
                "JSR" => {
                    self.jsr(&opcode.mode);
                }
                "LDA" => {
                    self.lda(&opcode.mode);
                }
                "LDX" => {
                    self.ldx(&opcode.mode);
                }
                "LDY" => {
                    self.ldy(&opcode.mode);
                }
                "LSR" => {
                    self.lsr(&opcode.mode);
                }
                "NOP" => {}
                "ORA" => {
                    self.ora(&opcode.mode);
                }
                "PHA" => {
                    self.pha();
                }
                "PHP" => {
                    self.php();
                }
                "PLA" => {
                    self.pla();
                }
                "PLP" => {
                    self.plp();
                }
                "ROL" => {
                    self.asl(&opcode.mode);
                }
                "ROR" => {
                    self.lsr(&opcode.mode);
                }
                "RTI" => {
                    self.rti();
                }
                "RTS" => {
                    self.rts();
                }
                "SBC" => {
                    self.sbc(&opcode.mode);
                }
                "SEC" => {
                    self.status.set(CpuFlag::CARRY, true);
                }
                "SED" => self.status.set(CpuFlag::DECIMAL_MODE, true),
                "SEI" => {
                    self.status.set(CpuFlag::INTERRUPT_DISABLE, true);
                }
                "STA" => {
                    self.sta(&opcode.mode);
                }
                "STX" => {
                    self.stx(&opcode.mode);
                }
                "STY" => {
                    self.sty(&opcode.mode);
                }
                "TAX" => {
                    self.tax();
                }
                "TAY" => {
                    self.tay();
                }
                "TSX" => {
                    self.tsx();
                }
                "TXA" => {
                    self.txa();
                }
                "TXS" => {
                    self.txs();
                }
                "TYA" => {
                    self.tya();
                }
                _ => todo!(""),
            }
            if program_counter_state == self.program_counter {
                self.program_counter += (opcode.bytes - 1) as u16;
            }
        }
    }

    fn adc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        let carry = self.status.contains(CpuFlag::CARRY);

        let (result, carry) = self.register_a.carrying_add(value, carry);

        self.register_a = result;

        self.update_carry_flag(carry);
        self.update_zero_and_negative_falgs(result);
    }

    fn and(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        self.register_a = self.register_a & value;
        self.update_zero_and_negative_falgs(self.register_a);
    }

    fn asl(&mut self, mode: &AddressingMode) {
        let (result, carry) = match mode {
            AddressingMode::NoneAddressing => {
                let (result, carry) = self.register_a.overflowing_shl(1);
                self.register_a = result;
                (result, carry)
            }
            _ => {
                let addr = self.get_operand_address(mode);
                let value = self.mem_read(addr);

                let (result, carry) = value.overflowing_shl(1);
                self.mem_write(addr, result);
                (result, carry)
            }
        };

        self.update_carry_flag(carry);
        self.update_zero_and_negative_falgs(result);
    }

    fn bit(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        let result = self.register_a & value;
        self.status.set(CpuFlag::OVERFLOW, value & (1 << 6) != 0);
        self.update_zero_and_negative_falgs(result);
    }

    fn dec(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        let result = value.wrapping_sub(1);
        self.mem_write(addr, result);
        self.update_zero_and_negative_falgs(result);
    }

    fn dex(&mut self) {
        self.register_x = self.register_x.wrapping_sub(1);
        self.update_zero_and_negative_falgs(self.register_x);
    }

    fn dey(&mut self) {
        self.register_y = self.register_y.wrapping_sub(1);
        self.update_zero_and_negative_falgs(self.register_y);
    }

    fn eor(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        self.register_a = self.register_a ^ value;
        self.update_zero_and_negative_falgs(self.register_a);
    }

    fn inc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        let result = value.wrapping_add(1);
        self.mem_write(addr, result);
        self.update_zero_and_negative_falgs(result);
    }

    fn inx(&mut self) {
        self.register_x = self.register_x.wrapping_add(1);
        self.update_zero_and_negative_falgs(self.register_x);
    }

    fn iny(&mut self) {
        self.register_y = self.register_y.wrapping_add(1);
        self.update_zero_and_negative_falgs(self.register_y);
    }

    fn jmp(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.program_counter = addr;
    }

    fn jsr(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read_u16(addr);
        self.stack_push_u16(self.program_counter - 1);

        self.program_counter = value;
    }

    // https://www.nesdev.org/obelisk-6502-guide/reference.html#LDA
    fn lda(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        self.register_a = value;
        self.update_zero_and_negative_falgs(self.register_a);
    }

    fn ldx(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        self.register_x = value;
        self.update_zero_and_negative_falgs(self.register_x);
    }

    fn ldy(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        self.register_y = value;
        self.update_zero_and_negative_falgs(self.register_y);
    }

    fn lsr(&mut self, mode: &AddressingMode) {
        let (result, carry) = match mode {
            AddressingMode::NoneAddressing => {
                let (result, carry) = self.register_a.overflowing_shr(1);
                self.register_a = result;
                (result, carry)
            }
            _ => {
                let addr = self.get_operand_address(mode);
                let value = self.mem_read(addr);

                let (result, carry) = value.overflowing_shr(1);
                self.mem_write(addr, result);
                (result, carry)
            }
        };

        self.update_carry_flag(carry);
        self.update_zero_and_negative_falgs(result);
    }

    fn ora(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        self.register_a = self.register_a | value;
        self.update_zero_and_negative_falgs(self.register_a);
    }

    fn pha(&mut self) {
        self.stack_push(self.register_a);
    }

    fn php(&mut self) {
        self.stack_push(self.status.bits());
    }

    fn pla(&mut self) {
        self.register_a = self.stack_pop();
        self.update_zero_and_negative_falgs(self.register_a);
    }

    fn plp(&mut self) {
        self.status = CpuFlag::from_bits(self.stack_pop()).unwrap();
    }

    fn rti(&mut self) {
        self.plp();
        self.program_counter = self.stack_pop_u16();
    }

    fn rts(&mut self) {
        self.program_counter = self.stack_pop_u16() - 1;
    }

    fn sbc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        let (result, overflow) = self.register_a.overflowing_sub(value);
        self.register_a = result;
        self.update_zero_and_negative_falgs(result);
        self.update_carry_flag(!overflow);
    }

    fn sta(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_a);
    }

    fn stx(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_x);
    }

    fn sty(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_y);
    }

    // https://www.nesdev.org/obelisk-6502-guide/reference.html#TAX
    fn tax(&mut self) {
        self.register_x = self.register_a;
        self.update_zero_and_negative_falgs(self.register_x);
    }

    fn tay(&mut self) {
        self.register_y = self.register_a;
        self.update_zero_and_negative_falgs(self.register_y);
    }

    fn tsx(&mut self) {
        self.register_x = self.stack_pointer;
        self.update_zero_and_negative_falgs(self.register_x);
    }

    fn txa(&mut self) {
        self.register_a = self.register_x;
        self.update_zero_and_negative_falgs(self.register_a);
    }

    fn txs(&mut self) {
        self.stack_pointer = self.register_x;
    }

    fn tya(&mut self) {
        self.register_a = self.register_y;
        self.update_zero_and_negative_falgs(self.register_a);
    }

    fn compare(&mut self, register: u8, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        let result = register.wrapping_sub(value);

        self.update_zero_and_negative_falgs(result);
        self.update_carry_flag(register >= value);
    }

    fn branch(&mut self, branch: bool) {
        if branch {
            let offset = self.mem_read(self.program_counter) as i8;
            self.program_counter = self
                .program_counter
                .wrapping_add(1)
                .wrapping_add(offset as u16);
        }
    }

    fn update_zero_and_negative_falgs(&mut self, result: u8) {
        // Set status
        if result == 0 {
            // Set Zero flag bit
            self.status.insert(CpuFlag::ZERO);
        } else {
            // Unset Zero flag bit
            self.status.remove(CpuFlag::ZERO);
        }

        // If first bit is set -> negative
        if result & 0b1000_0000 != 0 {
            // Set Negative flag
            self.status.insert(CpuFlag::NEGATIVE);
        } else {
            // Unset negative flag
            self.status.remove(CpuFlag::NEGATIVE);
        }
    }

    fn update_carry_flag(&mut self, carry: bool) {
        if carry {
            self.status.insert(CpuFlag::CARRY);
        } else {
            self.status.remove(CpuFlag::CARRY);
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_0xa9_lda_immediate_load_data() {
        let mut cpu = CPU::new();

        cpu.load_and_run(vec![0xa9, 0x05, 0x00]);
        assert_eq!(cpu.register_a, 0x05);
        assert!(!cpu.status.contains(CpuFlag::ZERO));
        assert!(!cpu.status.contains(CpuFlag::NEGATIVE));
    }

    #[test]
    fn test_lda_from_memory() {
        let mut cpu = CPU::new();

        cpu.mem_write(0x10, 0x55);
        cpu.load_and_run(vec![0xa5, 0x10, 0x00]);

        assert_eq!(cpu.register_a, 0x55);
    }

    #[test]
    fn test_0xa9_lda_zero_flag() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x00, 0x00]);
        assert!(cpu.status.contains(CpuFlag::ZERO));
    }

    #[test]
    fn test_5_ops_working_together() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xc0, 0xaa, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 0xc1)
    }

    #[test]
    fn test_adc() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x05, 0x69, 0x01, 0x00]);

        assert_eq!(cpu.register_a, 0x06);
        assert!(!cpu.status.contains(CpuFlag::ZERO));
        assert!(!cpu.status.contains(CpuFlag::CARRY));
    }
}
