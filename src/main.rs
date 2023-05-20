use std::collections::HashMap;

use lazy_static::lazy_static;

fn main() {
    println!("Hello, world!");
}

pub struct OpCode {
    pub code: u8,
    pub name: &'static str,
    pub bytes: u8,
    pub cycles: u8,
    pub mode: AddressingMode,
}

impl OpCode {
    pub fn new(code: u8, name: &'static str, bytes: u8, cycles: u8, mode: AddressingMode) -> Self {
        OpCode {
            code,
            name,
            bytes,
            cycles,
            mode,
        }
    }
}

lazy_static! {
    static ref CPU_OPS_CODES: Vec<OpCode> = vec![
        OpCode::new(0x00, "BRK", 1, 7, AddressingMode::NoneAddressing),
        OpCode::new(0xe8, "INX", 1, 2, AddressingMode::NoneAddressing),
        /* LDA */
        OpCode::new(0xa9, "LDA", 2, 2, AddressingMode::Immediate),
        OpCode::new(0xa5, "LDA", 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0xb5, "LDA", 2, 4, AddressingMode::ZeroPage_X),
        OpCode::new(0xad, "LDA", 3, 4, AddressingMode::Absolute),
        OpCode::new(0xbd, "LDA", 3, 4 /* +1 if page cross */, AddressingMode::Absolute_X),
        OpCode::new(0xb9, "LDA", 3, 4 /* +1 if page cross */, AddressingMode::Absolute_Y),
        OpCode::new(0xa1, "LDA", 2, 6, AddressingMode::Indirect_X),
        OpCode::new(0xb1, "LDA", 2, 5 /* +1 if page cross */, AddressingMode::Indirect_Y),
        /* STA */
        OpCode::new(0x85, "STA", 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0x95, "STA", 2, 4, AddressingMode::ZeroPage_X),
        OpCode::new(0x8d, "STA", 3, 4, AddressingMode::Absolute),
        OpCode::new(0x9d, "STA", 3, 5, AddressingMode::Absolute_X),
        OpCode::new(0x99, "STA", 3, 5, AddressingMode::Absolute_Y),
        OpCode::new(0x81, "STA", 2, 6, AddressingMode::Indirect_X),
        OpCode::new(0x91, "STA", 2, 6, AddressingMode::Indirect_Y),

        OpCode::new(0xaa, "TAX", 1, 2, AddressingMode::NoneAddressing),
    ];
    pub static ref OPCODES_MAP: HashMap<u8, &'static OpCode> = {
        let mut map = HashMap::new();
        for cpuop in &*CPU_OPS_CODES {
            map.insert(cpuop.code, cpuop);
        }
        map
    };
}

pub struct CPU {
    pub register_a: u8,
    pub register_x: u8,
    pub register_y: u8,
    pub status: u8,
    pub program_counter: u16,
    pub memeory: [u8; 0xffff],
}

#[derive(Debug)]
#[allow(non_camel_case_types)]
pub enum AddressingMode {
    Immediate,
    ZeroPage,
    ZeroPage_X,
    ZeroPage_Y,
    Absolute,
    Absolute_X,
    Absolute_Y,
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
            status: 0,
            program_counter: 0,
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
        self.status = 0;

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
                "LDA" => {
                    self.lda(&opcode.mode);
                }
                "STA" => {
                    self.sta(&opcode.mode);
                }
                "TAX" => {
                    self.tax();
                }
                "INX" => {
                    self.inx();
                }
                "BRK" => {
                    return;
                }
                _ => todo!(""),
            }
            if program_counter_state == self.program_counter {
                self.program_counter += (opcode.bytes - 1) as u16;
            }
        }
    }

    // https://www.nesdev.org/obelisk-6502-guide/reference.html#LDA
    fn lda(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        self.register_a = value;
        self.update_zero_and_negative_falgs(self.register_a);
    }

    fn sta(&mut self, mode: &AddressingMode) {
        todo!()
    }

    // https://www.nesdev.org/obelisk-6502-guide/reference.html#TAX
    fn tax(&mut self) {
        self.register_x = self.register_a;
        self.update_zero_and_negative_falgs(self.register_x);
    }

    fn inx(&mut self) {
        self.register_x = self.register_x.wrapping_add(1);

        self.update_zero_and_negative_falgs(self.register_x);
    }

    fn update_zero_and_negative_falgs(&mut self, result: u8) {
        // Set status
        if result == 0 {
            // Set Zero flag bit
            self.status = self.status | 0b0000_0010;
        } else {
            // Unset Zero flag bit
            self.status = self.status & 0b1111_1101
        }

        // If first bit is set -> negative
        if result & 0b1000_0000 != 0 {
            // Set Negative flag
            self.status = self.status | 0b1000_0000;
        } else {
            // Unset negative flag
            self.status = self.status & 0b0111_1111;
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
        assert!(cpu.status & 0b0000_00100 == 0b00);
        assert!(cpu.status & 0b1000_0000 == 0);
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
        assert!(cpu.status & 0b0000_0010 == 0b10);
    }

    #[test]
    fn test_5_ops_working_together() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xc0, 0xaa, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 0xc1)
    }
}
