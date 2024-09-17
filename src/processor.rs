// #![warn(missing_docs)]

use std::any::TypeId;

use isa::Instruction;
use log::debug;
use thiserror::Error;

use crate::{
    memory::{Memory, MemoryError, RAM},
    Components,
};

pub const NUMBER_REGISTERS: usize = 8;

#[derive(Error, Debug)]
pub enum ProcessorError {
    #[error("Registrador inválido: {0}")]
    InvalidRegister(usize),
    #[error("Erro de memória: {0}")]
    Memory(#[from] MemoryError),
    #[error("Instrução inválida: {0}")]
    InvalidInstruction(#[from] isa::InvalidInstruction),
}

/// Estrutura que representa um processador.
#[derive(Debug, Default, PartialEq)]
pub struct Processor {
    registers: [usize; NUMBER_REGISTERS],

    fr: usize,
    pc: usize,
    ir: usize,
    sp: usize,

    instruction: Instruction,
    rx: usize,
    ry: usize,
    rz: usize,
}

impl Processor {
    /// Cria um novo processador com os valores padrão.
    ///
    /// Todos os registradores são iniciados com o valor 0 (zero).
    pub fn new() -> Self {
        Self::default()
    }

    /// Retorna o valor do registrador `number`.
    ///
    /// # Erros
    ///
    /// Retorna o erro [`ProcessorError::InvalidRegister`] caso o registrador `number` seja
    /// inválido.
    ///
    /// # Exemplo
    ///
    /// ```
    /// use crate::components::processor::Processor;
    ///
    /// let mut p = Processor::default();
    /// assert_eq!(0x0, p.reg(0).unwrap());
    /// ```
    pub fn reg(&self, number: usize) -> Result<usize, ProcessorError> {
        match self.registers.get(number) {
            Some(r) => Ok(*r),
            None => Err(ProcessorError::InvalidRegister(number)),
        }
    }

    /// Retorna uma referência mutável do registrador `number`.
    ///
    /// # Erros
    ///
    /// Retorna o erro [`ProcessorError::InvalidRegister`] caso o registrador `number` seja
    /// inválido.
    ///
    /// # Exemplo
    ///
    /// ```
    /// use crate::components::processor::Processor;
    ///
    /// let mut p = Processor::default();
    /// assert_eq!(0x0, *p.mut_reg(0).unwrap());
    /// ```
    pub fn mut_reg(&mut self, number: usize) -> Result<&mut usize, ProcessorError> {
        match self.registers.get_mut(number) {
            Some(r) => Ok(r),
            None => Err(ProcessorError::InvalidRegister(number)),
        }
    }

    /// Esta função altera o conteúdo do registrar `number` para `value`.
    ///
    /// # Erros
    ///
    /// Retorna o erro [`ProcessorError::InvalidRegister`] caso o registrador `number` seja
    /// invalido.
    ///
    /// # Exemplo
    ///
    /// ```
    /// use crate::components::processor::Processor;
    ///
    /// let mut p = Processor::default();
    /// assert_eq!(0x0, p.reg(0).unwrap());
    /// p.set_reg(0, 0x1);
    /// assert_eq!(0x1, p.reg(0).unwrap());
    /// ```
    pub fn set_reg(&mut self, number: usize, value: usize) -> Result<(), ProcessorError> {
        match self.registers.get_mut(number) {
            Some(r) => {
                *r = value;
                Ok(())
            }
            None => Err(ProcessorError::InvalidRegister(number)),
        }
    }

    /// Realiza a etapa de busca do processador.
    ///
    /// # Erros
    ///
    /// Esta função retorna [`MemoryError`] caso não seja possível acessar a memória.
    fn fetch_stage(&mut self, memory: &impl Memory) -> Result<(), MemoryError> {
        self.ir = *memory.get(self.pc)?;
        debug!(
            "Fetch Stage [Instruction Register {:016b}] [Program Counter {}]",
            self.ir, self.pc
        );
        self.pc += 1;
        Ok(())
    }

    /// Realiza a etapa de decodificação do processador.
    ///
    /// # Erros
    ///
    /// Esta função retorna o erro [`ProcessorError::InvalidInstruction`] caso a instrução seja
    /// inválida.
    fn decode_stage(&mut self) -> Result<(), isa::InvalidInstruction> {
        self.rx = isa::bits(self.ir, 7..=9);
        self.ry = isa::bits(self.ir, 4..=6);
        self.rz = isa::bits(self.ir, 1..=3);
        self.instruction = isa::Instruction::get_instruction(self.ir)?;
        debug!(
            "Decode Stage: [I:{} RX:{} RY:{} RZ:{}]",
            self.instruction, self.rx, self.ry, self.rz
        );
        Ok(())
    }

    /// Realiza a etapa de execução do processador.
    ///
    /// # Erros
    ///
    /// Esta função pode retornar [`ProcessorError`].
    fn execution_stage(&mut self, components: &mut Components) -> Result<(), ProcessorError> {
        debug!("Execution Stage [{}]", self.instruction);

        let ram = {
            let typeid = TypeId::of::<RAM>();
            let any = components
                .get_mut(&typeid)
                .expect("Nenhuma RAM foi encontrada.");
            any.downcast_mut::<RAM>().unwrap()
        };

        match self.instruction {
            Instruction::LOAD => {
                self.set_reg(self.rx, *ram.get(*ram.get(self.pc)?)?)?;
                self.pc += 1;
            }

            Instruction::LOADN => {
                self.set_reg(self.rx, *ram.get(self.pc)?)?;
                self.pc += 1;
            }

            Instruction::LOADI => {
                self.set_reg(self.rx, *ram.get(self.reg(self.ry)?)?)?;
            }

            Instruction::STORE => {
                ram.set(*ram.get(self.pc)?, self.reg(self.rx)?)?;
                self.pc += 1;
            }

            Instruction::STOREN => {
                ram.set(*ram.get(self.pc)?, *ram.get(self.pc + 1)?)?;
                self.pc += 2;
            }

            Instruction::STOREI => {
                ram.set(self.reg(self.rx)?, self.reg(self.ry)?)?;
            }

            Instruction::MOV => todo!(),
            Instruction::INPUT => todo!(),
            Instruction::OUTPUT => todo!(),
            Instruction::OUTCHAR => todo!(),
            Instruction::INCHAR => todo!(),
            Instruction::SOUND => todo!(),
            Instruction::ADD => todo!(),
            Instruction::ADDC => todo!(),
            Instruction::SUB => todo!(),
            Instruction::SUBC => todo!(),
            Instruction::MUL => todo!(),
            Instruction::DIV => todo!(),
            Instruction::INC => todo!(),
            Instruction::DEC => todo!(),
            Instruction::MOD => todo!(),
            Instruction::AND => todo!(),
            Instruction::OR => todo!(),
            Instruction::XOR => todo!(),
            Instruction::NOT => todo!(),
            Instruction::SHIFTL0 => todo!(),
            Instruction::SHIFTL1 => todo!(),
            Instruction::SHIFTR0 => todo!(),
            Instruction::SHIFTR1 => todo!(),
            Instruction::ROTL => todo!(),
            Instruction::ROTR => todo!(),
            Instruction::CMP => todo!(),
            Instruction::JMP => todo!(),
            Instruction::JEQ => todo!(),
            Instruction::JNE => todo!(),
            Instruction::JZ => todo!(),
            Instruction::JNZ => todo!(),
            Instruction::JC => todo!(),
            Instruction::JNC => todo!(),
            Instruction::JGR => todo!(),
            Instruction::JLE => todo!(),
            Instruction::JEG => todo!(),
            Instruction::JEL => todo!(),
            Instruction::JOV => todo!(),
            Instruction::JNO => todo!(),
            Instruction::JDZ => todo!(),
            Instruction::JN => todo!(),
            Instruction::CALL => todo!(),
            Instruction::CEQ => todo!(),
            Instruction::CNE => todo!(),
            Instruction::CZ => todo!(),
            Instruction::CNZ => todo!(),
            Instruction::CC => todo!(),
            Instruction::CNC => todo!(),
            Instruction::CGR => todo!(),
            Instruction::CLE => todo!(),
            Instruction::CEG => todo!(),
            Instruction::CEL => todo!(),
            Instruction::COV => todo!(),
            Instruction::CNO => todo!(),
            Instruction::CDZ => todo!(),
            Instruction::CN => todo!(),
            Instruction::RTS => todo!(),
            Instruction::RTI => todo!(),
            Instruction::PUSH => todo!(),
            Instruction::POP => todo!(),
            Instruction::NOP => (),
            Instruction::HALT => todo!(),
            Instruction::CLEARC => todo!(),
            Instruction::SETC => todo!(),
            Instruction::BREAKP => todo!(),
        }

        Ok(())
    }

    pub fn instruction_cicle(
        &mut self,
        componentes: &mut Components,
    ) -> Result<(), ProcessorError> {
        let ram = componentes
            .get_mut(&TypeId::of::<RAM>())
            .expect("RAM não encontrada")
            .downcast_mut::<RAM>()
            .unwrap();

        self.fetch_stage(ram)?;
        self.decode_stage()?;
        self.execution_stage(componentes)
    }
}

#[cfg(test)]
mod tests {

    use std::usize;

    use isa::set_bits;

    // Rx: 7..=9
    // Ry: 4..=6
    // Rz: 1..=3

    use super::*;

    trait Regions {
        fn rx(&self, v: usize) -> usize;
        fn ry(&self, v: usize) -> usize;
        fn rz(&self, v: usize) -> usize;
    }

    impl Regions for usize {
        fn rx(&self, v: usize) -> usize {
            set_bits(*self, v, 7..=9)
        }

        fn ry(&self, v: usize) -> usize {
            set_bits(*self, v, 4..=6)
        }

        fn rz(&self, v: usize) -> usize {
            set_bits(*self, v, 1..=3)
        }
    }

    fn components() -> Components {
        let ram = RAM::with_capacity(10);
        let mut comp = Components::new();
        comp.insert(TypeId::of::<RAM>(), Box::new(ram));
        comp
    }

    fn ram(components: &mut Components) -> &mut RAM {
        let typeid = TypeId::of::<RAM>();
        let any = components
            .get_mut(&typeid)
            .expect("Nenhuma RAM foi encontrada.");
        any.downcast_mut::<RAM>().unwrap()
    }

    #[test]
    // LOAD R3, 1
    fn inst_load() {
        let mut comp = components();
        let ram = ram(&mut comp);
        let inst = isa::Instruction::LOAD.mask().rx(3);
        let _ = ram.set(0, inst);
        let _ = ram.set(1, 2);
        let _ = ram.set(2, 100);

        let mut default = Processor::new();
        default.instruction = isa::Instruction::get_instruction(inst).unwrap();
        default.ir = inst;
        default.pc = 2;
        default.rx = 3;
        default.registers[3] = 100;

        let mut proc = Processor::new();

        let _ = proc.instruction_cicle(&mut comp);

        assert_eq!(proc, default);
    }

    #[test]
    // LOAD R3, #100
    fn inst_loadn() {
        let mut comp = components();
        let ram = ram(&mut comp);
        let inst = isa::Instruction::LOADN.mask().rx(3);
        let _ = ram.set(0, inst);
        let _ = ram.set(1, 100);

        let mut default = Processor::new();
        default.instruction = isa::Instruction::get_instruction(inst).unwrap();
        default.ir = inst;
        default.pc = 2;
        default.rx = 3;
        default.registers[3] = 100;

        let mut proc = Processor::new();

        let _ = proc.instruction_cicle(&mut comp);

        assert_eq!(proc, default);
    }

    #[test]
    // LOADI R3, R1
    fn inst_loadi() {
        let mut comp = components();
        let ram = ram(&mut comp);
        let inst = isa::Instruction::LOADI.mask().rx(3).ry(1);
        let _ = ram.set(0, inst);
        let _ = ram.set(1, 100);

        let mut default = Processor::new();
        default.instruction = isa::Instruction::get_instruction(inst).unwrap();
        default.ir = inst;
        default.pc = 1;
        default.rx = 3;
        default.ry = 1;
        default.registers[3] = 100;
        default.registers[1] = 1;

        let mut proc = Processor::new();
        proc.registers[1] = 1;

        let _ = proc.instruction_cicle(&mut comp);

        assert_eq!(proc, default);
    }

    #[test]
    // STORE 2, R3
    fn inst_store() {
        let mut comp = components();
        let r = ram(&mut comp);
        let inst = isa::Instruction::STORE.mask().rx(3);
        let _ = r.set(0, inst);
        let _ = r.set(1, 2);

        let mut default = Processor::new();
        default.instruction = isa::Instruction::get_instruction(inst).unwrap();
        default.ir = inst;
        default.pc = 2;
        default.rx = 3;
        default.registers[3] = 100;

        let mut proc = Processor::new();
        proc.registers[3] = 100;

        let _ = proc.instruction_cicle(&mut comp);

        assert_eq!(proc, default);
        let r = ram(&mut comp);
        assert_eq!(*r.get(2).unwrap(), 100);
    }

    #[test]
    // STOREN 3, #100
    fn inst_storen() {
        let mut comp = components();
        let r = ram(&mut comp);
        let inst = isa::Instruction::STOREN.mask();
        let _ = r.set(0, inst);
        let _ = r.set(1, 3);
        let _ = r.set(2, 100);

        let mut default = Processor::new();
        default.instruction = isa::Instruction::get_instruction(inst).unwrap();
        default.ir = inst;
        default.pc = 3;

        let mut proc = Processor::new();

        let _ = proc.instruction_cicle(&mut comp);

        assert_eq!(proc, default);
        let r = ram(&mut comp);
        assert_eq!(*r.get(3).unwrap(), 100);
    }

    #[test]
    // STOREN R3, R2
    fn inst_storei() {
        let mut comp = components();
        let r = ram(&mut comp);
        let inst = isa::Instruction::STOREI.mask().rx(3).ry(2);
        let _ = r.set(0, inst);
        let _ = r.set(1, 100);

        let mut default = Processor::new();
        default.instruction = isa::Instruction::get_instruction(inst).unwrap();
        default.ir = inst;
        default.rx = 3;
        default.ry = 2;
        default.pc = 1;
        default.registers[3] = 1;
        default.registers[2] = 100;

        let mut proc = Processor::new();

        proc.registers[3] = 1;
        proc.registers[2] = 100;
        let _ = proc.instruction_cicle(&mut comp);

        assert_eq!(proc, default);
        let r = ram(&mut comp);
        assert_eq!(*r.get(1).unwrap(), 100);
    }
}
