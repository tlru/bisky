pub use decode::*;

use crate::rv32im::instruction::RType;
use crate::{
    b_imm, decode_func3, decode_func7, decode_i_imm, decode_j_imm, decode_opcode, decode_rd,
    decode_rs1, decode_rs2, decode_s_imm, decode_u_imm,
};

/// Decoding macros.
pub mod decode;
// pub mod exec;
pub mod instruction;
// mod exec;

pub const WORD_SIZE: usize = core::mem::size_of::<u32>();

pub const OPCODE_LUI: u8 = 0b0110111;
pub const OPCODE_AUIPC: u8 = 0b0010111;
pub const OPCODE_JAL: u8 = 0b1101111;
pub const OPCODE_JALR: u8 = 0b1100111;
pub const OPCODE_BRANCH: u8 = 0b1100011;
pub const OPCODE_LOAD: u8 = 0b0000011;
pub const OPCODE_STORE: u8 = 0b0100011;
pub const OPCODE_ARITHMETIC_IMM: u8 = 0b0010011;
pub const OPCODE_ARITHMETIC: u8 = 0b0110011;
pub const OPCODE_CUSTOM_0: u8 = 0b0001011;
pub const OPCODE_CUSTOM_1: u8 = 0b0101011;
pub const OPCODE_CUSTOM_2: u8 = 0b1011011;
pub const OPCODE_CUSTOM_3: u8 = 0b1111011;
pub const OPCODE_SYSTEM: u8 = 0b1110011;

/// BRANCH
pub const FUNC3_BEQ: u8 = 0b000;
pub const FUNC3_BNE: u8 = 0b001;
pub const FUNC3_BLT: u8 = 0b100;
pub const FUNC3_BGE: u8 = 0b101;
pub const FUNC3_BLTU: u8 = 0b110;
pub const FUNC3_BGEU: u8 = 0b111;

/// LOAD
pub const FUNC3_LB: u8 = 0b000;
pub const FUNC3_LH: u8 = 0b001;
pub const FUNC3_LW: u8 = 0b010;
pub const FUNC3_LBU: u8 = 0b100;
pub const FUNC3_LHU: u8 = 0b101;

/// STORE
pub const FUNC3_SB: u8 = 0b000;
pub const FUNC3_SH: u8 = 0b001;
pub const FUNC3_SW: u8 = 0b010;

/// ARITHMETIC
///

/// ADD, ADDI, SUB
pub const FUNC3_ADD_SUB: u8 = 0b000;
pub const FUNC3_ADD: u8 = 0b000;
pub const FUNC3_ADDI: u8 = 0b000;
pub const FUNC3_SUB: u8 = 0b000;
/// SLLI, SLL
pub const FUNC3_SLL: u8 = 0b001;
pub const FUNC3_SRL: u8 = 0b101;
pub const FUNC3_SLLI: u8 = 0b001;
/// SLT, SLTI
pub const FUNC3_SLT: u8 = 0b010;
pub const FUNC3_SLTI: u8 = 0b010;
pub const FUNC3_SLTU: u8 = 0b011;
pub const FUNC3_SLTIU: u8 = 0b011;
/// XOR, XORI
pub const FUNC3_XOR: u8 = 0b100;
pub const FUNC3_XORI: u8 = 0b100;
/// SRLI, SRAI
/// SR is 0x5 <> 0b101
pub const FUNC3_SRLI: u8 = 0b101;
pub const FUNC3_SR: u8 = 0b101;
pub const FUNC3_SRAI: u8 = 0b101;
pub const FUNC3_SRA: u8 = 0b101;
/// OR, ORI
pub const FUNC3_OR: u8 = 0b110;
pub const FUNC3_ORI: u8 = 0b110;
/// AND, ANDI
pub const FUNC3_AND: u8 = 0b111;
pub const FUNC3_ANDI: u8 = 0b111;

pub const FUNC3_MUL: u8 = 0b000;
pub const FUNC3_MULH: u8 = 0b001;
pub const FUNC3_MULHSU: u8 = 0b010;
pub const FUNC3_MULHU: u8 = 0b011;
pub const FUNC3_DIV: u8 = 0b100;
pub const FUNC3_DIVU: u8 = 0b101;
pub const FUNC3_REM: u8 = 0b110;
pub const FUNC3_REMU: u8 = 0b111;

/// ADD, ADDI
pub const FUNC7_ADD: u8 = 0b0000000;
/// SUB
pub const FUNC7_SUB: u8 = 0b0100000;
pub const FUNC7_SRA: u8 = 0b0100000;
pub const FUNC7_SRL: u8 = 0b0000000;
pub const FUNC7_SLL: u8 = 0b0000000;

/// https://riscv.org/wp-content/uploads/2016/06/riscv-spec-v2.1.pdf
pub const FUNC7_MULDIV: u8 = 0b0000001;
pub const FUNC7_SLT: u8 = 0b0000000;
pub const FUNC7_SLTU: u8 = 0b0000000;
pub const FUNC7_XOR: u8 = 0b0000000;
pub const FUNC7_AND: u8 = 0b0000000;
pub const FUNC7_OR: u8 = 0b0000000;

#[track_caller]
pub fn opcode_name(opcode: u8) -> &'static str {
    match opcode {
        OPCODE_LUI => "lui",
        OPCODE_AUIPC => "auipc",
        OPCODE_JAL => "jal",
        OPCODE_JALR => "jalr",
        OPCODE_BRANCH => "branch",
        OPCODE_LOAD => "load",
        OPCODE_STORE => "store",
        OPCODE_ARITHMETIC_IMM => "arithmetic_imm",
        OPCODE_ARITHMETIC => "arithmetic",
        OPCODE_SYSTEM => "system",
        _ => panic!("Unrecognized opcode: {opcode} {:#010b}", opcode),
    }
}

#[track_caller]
pub fn instruction_name(ir: u32) -> &'static str {
    let opcode = decode_opcode!(ir);
    match opcode {
        OPCODE_LUI => "lui",
        OPCODE_AUIPC => "auipc",
        OPCODE_JAL => "jal",
        OPCODE_JALR => "jalr",
        OPCODE_BRANCH => {
            let func3 = decode_func3!(ir);
            match func3 {
                FUNC3_BEQ => "beq",
                FUNC3_BNE => "bne",
                FUNC3_BLT => "blt",
                FUNC3_BGE => "bge",
                FUNC3_BLTU => "bltu",
                FUNC3_BGEU => "bgeu",
                _ => panic!("Unknown branch func3: {}", func3),
            }
        }
        OPCODE_LOAD => {
            let func3 = decode_func3!(ir);
            match func3 {
                FUNC3_LB => "lb",
                FUNC3_LH => "lh",
                FUNC3_LW => "lw",
                FUNC3_LBU => "lbu",
                FUNC3_LHU => "lhu",
                _ => panic!("Unknown load func3: {}", func3),
            }
        }
        OPCODE_STORE => {
            let func3 = decode_func3!(ir);
            match func3 {
                FUNC3_SB => "sb",
                FUNC3_SH => "sh",
                FUNC3_SW => "sw",
                _ => panic!("Unknown store func3: {}", func3),
            }
        }
        OPCODE_ARITHMETIC_IMM => {
            let func3 = decode_func3!(ir);
            let func7 = decode_func3!(ir);
            #[forbid(unused_variables)]
            match (func3, func7) {
                (FUNC3_ADDI, _) => "addi",
                (FUNC3_SLTI, _) => "slti",
                (FUNC3_SLTIU, _) => "sltiu",
                (FUNC3_SLLI, FUNC7_SLL) => "slli",
                (FUNC3_SR, FUNC7_SRL) => "srli",
                (FUNC3_SR, FUNC7_SRA) => "srai",
                (FUNC3_XORI, _) => "xori",
                (FUNC3_ANDI, _) => "andi",
                (FUNC3_ORI, _) => "ori",
                _ => panic!("Unknown arithmetic_imm func3: {}", func3),
            }
        }
        OPCODE_ARITHMETIC => {
            let func3 = decode_func3!(ir);
            let func7 = decode_func7!(ir);
            #[forbid(unused_variables)]
            match (func3, func7) {
                (FUNC3_ADD_SUB, FUNC7_ADD) => "add",
                (FUNC3_ADD_SUB, FUNC7_SUB) => "sub",
                (FUNC3_SLL, FUNC7_SLL) => "sll",
                (FUNC3_SR, FUNC7_SRL) => "srl",
                (FUNC3_SR, FUNC7_SRA) => "sra",
                (FUNC3_SLT, FUNC7_SLT) => "slt",
                (FUNC3_SLTU, FUNC7_SLTU) => "sltu",
                (FUNC3_XOR, FUNC7_XOR) => "xor",
                (FUNC3_AND, FUNC7_AND) => "and",
                (FUNC3_OR, FUNC7_OR) => "or",
                (FUNC3_MUL, FUNC7_MULDIV) => "mul",
                (FUNC3_MULH, FUNC7_MULDIV) => "mulh",
                (FUNC3_MULHSU, FUNC7_MULDIV) => "mulhsu",
                (FUNC3_MULHU, FUNC7_MULDIV) => "mulhu",
                (FUNC3_DIV, FUNC7_MULDIV) => "div",
                (FUNC3_DIVU, FUNC7_MULDIV) => "divu",
                (FUNC3_REM, FUNC7_MULDIV) => "rem",
                (FUNC3_REMU, FUNC7_MULDIV) => "remu",
                (_, _) => panic!("Unknown arithmetic func3: {:#05b} {:#09b}", func3, func7),
            }
        }
        OPCODE_CUSTOM_0 => "custom_0",
        OPCODE_SYSTEM => "system",
        _ => panic!("Unrecognized opcode: {:#034b} {:#010b}", ir, opcode),
    }
}

/// All immediate and offset values are already sign-extended and their underlying repr can be expected to be two's complement
// put in module for rustfmt::skip
#[rustfmt::skip]
mod ix {
    use super::*;
    #[derive(Copy, Clone, Debug)]
    pub enum Rv32ImInstruction {
        /// Special
        Lui(u8 /* rd */, u32 /* imm */),
        Auipc(u8 /* rd */, u32 /* imm */),
        /// Branching
        Jal(u8 /* rd */, u32 /* offset */),
        Jalr(u8 /* rd */, u8 /* rs1 */, u32 /* offset */),
        Beq(u8 /* rs1 */, u8 /* rs2 */, u32 /* offset */),
        Bne(u8 /* rs1 */, u8 /* rs2 */, u32 /* offset */),
        Blt(u8 /* rs1 */, u8 /* rs2 */, u32 /* offset */),
        Bge(u8 /* rs1 */, u8 /* rs2 */, u32 /* offset */),
        Bltu(u8 /* rs1 */, u8 /* rs2 */, u32 /* offset */),
        Bgeu(u8 /* rs1 */, u8 /* rs2 */, u32 /* offset */),
        /// Load/store
        Lb(u8 /* rd */, u8 /* rs1 */, u32 /* offset(rs1) */),
        Lh(u8 /* rd */, u8 /* rs1 */, u32 /* offset(rs1) */),
        Lw(u8 /* rd */, u8 /* rs1 */, u32 /* offset(rs1) */),
        Lbu(u8 /* rd */, u8 /* rs1 */, u32 /* offset(rs1) */),
        Lhu(u8 /* rd */, u8 /* rs1 */, u32 /* offset(rs1) */),
        /// Store
        Sb(u8 /* rs2 */, u8 /* rs1 */, u32 /* offset(rs1) */),
        Sh(u8 /* rs2 */, u8 /* rs1 */, u32 /* offset(rs1) */),
        Sw(u8 /* rs2 */, u8 /* rs1 */, u32 /* offset(rs1) */),
        /// Arithmetic
        Add(u8 /* rd */, u8 /* rs1 */, u8 /* rs2 */),
        Addi(u8 /* rd */, u8 /* rs1 */, u32 /* imm */),
        Sub(u8 /* rd */, u8 /* rs1 */, u8 /* rs2 */),
        /// Mul extension
        Mul(u8 /* rd */, u8 /* rs1 */, u8 /* rs2 */),
        Mulh(u8 /* rd */, u8 /* rs1 */, u8 /* rs2 */),
        Mulhsu(u8 /* rd */, u8 /* rs1 */, u8 /* rs2 */),
        Mulhu(u8 /* rd */, u8 /* rs1 */, u8 /* rs2 */),
        Div(u8 /* rd */, u8 /* rs1 */, u8 /* rs2 */),
        Divu(u8 /* rd */, u8 /* rs1 */, u8 /* rs2 */),
        Rem(u8 /* rd */, u8 /* rs1 */, u8 /* rs2 */),
        Remu(u8 /* rd */, u8 /* rs1 */, u8 /* rs2 */),
        /// Bitwise
        /// Where our canonical ordering is AND, OR, XOR
        And(u8 /* rd */, u8 /* rs1 */, u8 /* rs2 */),
        Andi(u8 /* rd */, u8 /* rs1 */, u32 /* imm */),
        Xor(u8 /* rd */, u8 /* rs1 */, u8 /* rs2 */),
        Xori(u8 /* rd */, u8 /* rs1 */, u32 /* imm */),
        Or(u8 /* rd */, u8 /* rs1 */, u8 /* rs2 */),
        Ori(u8 /* rd */, u8 /* rs1 */, u32 /* imm */),
        /// Set
        Slt(u8 /* rd */, u8 /* rs1 */, u8 /* rs2 */),
        Slti(u8 /* rd */, u8 /* rs1 */, u32 /* imm */),
        Sltu(u8 /* rd */, u8 /* rs1 */, u8 /* rs2 */),
        Sltiu(u8 /* rd */, u8 /* rs1 */, u32 /* imm */),
        /// Shift
        Sll(u8 /* rd */, u8 /* rs1 */, u8 /* rs2 */),
        Slli(u8 /* rd */, u8 /* rs1 */, u32 /* imm */),
        Srl(u8 /* rd */, u8 /* rs1 */, u8 /* rs2 */),
        Srli(u8 /* rd */, u8 /* rs1 */, u32 /* imm */),
        /// Arithmetic Shift
        Sra(u8 /* rd */, u8 /* rs1 */, u8 /* rs2 */),
        Srai(u8 /* rd */, u8 /* rs1 */, u32 /* imm */),

        Custom0(RType),

        /// System
        Syscall(u32 /* something */),
    }
}
pub use ix::*;

impl Rv32ImInstruction {
    pub fn operands(&self) -> Vec<i32> {
        match *self {
            Rv32ImInstruction::Lui(a, b) => vec![a as i32, b as i32],
            Rv32ImInstruction::Auipc(a, b) => vec![a as i32, b as i32],
            Rv32ImInstruction::Jal(a, b) => vec![a as i32, b as i32],
            Rv32ImInstruction::Jalr(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Beq(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Bne(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Blt(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Bge(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Bltu(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Bgeu(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Lb(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Lh(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Lw(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Lbu(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Lhu(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Sb(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Sh(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Sw(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Add(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Addi(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Sub(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Mul(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Mulh(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Mulhsu(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Mulhu(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Div(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Divu(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Rem(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Remu(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::And(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Andi(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Xor(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Xori(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Or(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Ori(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Slt(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Slti(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Sltu(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Sltiu(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Sll(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Slli(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Srl(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Srli(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Sra(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Srai(a, b, c) => vec![a as i32, b as i32, c as i32],
            // Rv32ImInstruction::BBMul(a, b, c) => vec![a as i32, b as i32, c as i32],
            // Rv32ImInstruction::BBDiv(a, b, c) => vec![a as i32, b as i32, c as i32],
            // Rv32ImInstruction::BBAdd(a, b, c) => vec![a as i32, b as i32, c as i32],
            // Rv32ImInstruction::BBSub(a, b, c) => vec![a as i32, b as i32, c as i32],
            Rv32ImInstruction::Custom0(r_type) => {
                vec![r_type.rd as i32, r_type.rs1 as i32, r_type.rs2 as i32]
            }
            Rv32ImInstruction::Syscall(a) => vec![a as i32],
        }
    }
}

#[track_caller]
pub fn rv32im_instruction(ir: u32) -> Rv32ImInstruction {
    let opcode = decode_opcode!(ir);
    #[forbid(unused_variables)]
    match opcode {
        OPCODE_LUI => {
            let rd = decode_rd!(ir);
            let imm = decode_u_imm!(ir);
            Rv32ImInstruction::Lui(rd, imm)
        }
        OPCODE_AUIPC => {
            let rd = decode_rd!(ir);
            let imm = decode_u_imm!(ir);
            Rv32ImInstruction::Auipc(rd, imm)
        }
        OPCODE_JAL => {
            let rd = decode_rd!(ir);
            let offset = decode_j_imm!(ir);
            Rv32ImInstruction::Jal(rd, offset)
        }
        OPCODE_JALR => {
            let rd = decode_rd!(ir);
            let rs1 = decode_rs1!(ir);
            let offset = decode_i_imm!(ir);
            Rv32ImInstruction::Jalr(rd, rs1, offset)
        }
        OPCODE_BRANCH => {
            let rs1 = decode_rs1!(ir);
            let rs2 = decode_rs2!(ir);
            let func3 = decode_func3!(ir);
            let offset = b_imm!(ir);
            match func3 {
                FUNC3_BEQ => Rv32ImInstruction::Beq(rs1, rs2, offset),
                FUNC3_BNE => Rv32ImInstruction::Bne(rs1, rs2, offset),
                FUNC3_BLT => Rv32ImInstruction::Blt(rs1, rs2, offset),
                FUNC3_BGE => Rv32ImInstruction::Bge(rs1, rs2, offset),
                FUNC3_BLTU => Rv32ImInstruction::Bltu(rs1, rs2, offset),
                FUNC3_BGEU => Rv32ImInstruction::Bgeu(rs1, rs2, offset),
                _ => panic!("Unknown branch func3: {}", func3),
            }
        }
        OPCODE_LOAD => {
            let rd = decode_rd!(ir);
            let rs1 = decode_rs1!(ir);
            let imm = decode_i_imm!(ir);
            let func3 = decode_func3!(ir);
            match func3 {
                FUNC3_LB => Rv32ImInstruction::Lb(rd, rs1, imm),
                FUNC3_LH => Rv32ImInstruction::Lh(rd, rs1, imm),
                FUNC3_LW => Rv32ImInstruction::Lw(rd, rs1, imm),
                FUNC3_LBU => Rv32ImInstruction::Lbu(rd, rs1, imm),
                FUNC3_LHU => Rv32ImInstruction::Lhu(rd, rs1, imm),
                _ => panic!("Unknown load func3: {}", func3),
            }
        }
        OPCODE_STORE => {
            let rs1 = decode_rs1!(ir);
            let rs2 = decode_rs2!(ir);
            let imm = decode_s_imm!(ir);
            let func3 = decode_func3!(ir);
            match func3 {
                FUNC3_SB => Rv32ImInstruction::Sb(rs1, rs2, imm),
                FUNC3_SH => Rv32ImInstruction::Sh(rs1, rs2, imm),
                FUNC3_SW => Rv32ImInstruction::Sw(rs1, rs2, imm),
                _ => panic!("Unknown store func3: {}", func3),
            }
        }

        OPCODE_ARITHMETIC_IMM => {
            let rd = decode_rd!(ir);
            let rs1 = decode_rs1!(ir);
            let imm = decode_i_imm!(ir);
            let func3 = decode_func3!(ir);
            let func7 = decode_func7!(ir);
            // println!("OPCODE_ARITHMETIC_IMM: rd: {rd}, rs1: {rs1}, imm: {imm}, func3: {func3}");

            // println!(
            //     "OPCODE_ARITHMETIC_IMM: rd: {:#05b}, rs1: {:#05b}, imm: {:#05b} {:#05b}, BITS: {:#034b}",
            //     rd, rs1, imm, func3, ir
            // );

            // 0100000 11111 010111010 10110010011
            // 31       21 20
            // A total of 9 immediates
            #[forbid(unused_variables)]
            match (func3, func7) {
                (FUNC3_ADDI, _) => Rv32ImInstruction::Addi(rd, rs1, imm),
                (FUNC3_SLTI, _) => Rv32ImInstruction::Slti(rd, rs1, imm),
                (FUNC3_SLTIU, _) => Rv32ImInstruction::Sltiu(rd, rs1, imm),
                // `imm` is the entire 12-bit immediate, but we only want the lower 5 bits
                (FUNC3_SLLI, _) => Rv32ImInstruction::Slli(rd, rs1, imm & 0b11111),
                (FUNC3_SRLI, FUNC7_SRL) => Rv32ImInstruction::Srli(rd, rs1, imm & 0b11111),
                (FUNC3_SR, FUNC7_SRA) => Rv32ImInstruction::Srai(rd, rs1, imm & 0b11111),
                (FUNC3_XORI, _) => Rv32ImInstruction::Xori(rd, rs1, imm),
                (FUNC3_ANDI, _) => Rv32ImInstruction::Andi(rd, rs1, imm),
                (FUNC3_ORI, _) => Rv32ImInstruction::Ori(rd, rs1, imm),
                _ => panic!("Unknown immediate arithmetic: {:#05b}", func3),
            }
        }
        OPCODE_ARITHMETIC => {
            let rd = decode_rd!(ir);
            let rs1 = decode_rs1!(ir);
            let rs2 = decode_rs2!(ir);
            let func3 = decode_func3!(ir);
            let func7 = decode_func7!(ir);
            match (func3, func7) {
                (FUNC3_ADD_SUB, FUNC7_ADD) => Rv32ImInstruction::Add(rd, rs1, rs2),
                (FUNC3_ADD_SUB, FUNC7_SUB) => Rv32ImInstruction::Sub(rd, rs1, rs2),
                (FUNC3_SLL, FUNC7_SLL) => Rv32ImInstruction::Sll(rd, rs1, rs2),
                (FUNC3_SRL, FUNC7_SRL) => Rv32ImInstruction::Srl(rd, rs1, rs2),
                (FUNC3_SRA, FUNC7_SRA) => Rv32ImInstruction::Sra(rd, rs1, rs2),
                (FUNC3_SLT, 0) => Rv32ImInstruction::Slt(rd, rs1, rs2),
                (FUNC3_SLTU, 0) => Rv32ImInstruction::Sltu(rd, rs1, rs2),
                (FUNC3_XOR, 0) => Rv32ImInstruction::Xor(rd, rs1, rs2),
                (FUNC3_AND, 0) => Rv32ImInstruction::And(rd, rs1, rs2),
                (FUNC3_OR, 0) => Rv32ImInstruction::Or(rd, rs1, rs2),
                (FUNC3_MUL, FUNC7_MULDIV) => Rv32ImInstruction::Mul(rd, rs1, rs2),
                (FUNC3_MULH, FUNC7_MULDIV) => Rv32ImInstruction::Mulh(rd, rs1, rs2),
                (FUNC3_MULHSU, FUNC7_MULDIV) => Rv32ImInstruction::Mulhsu(rd, rs1, rs2),
                (FUNC3_MULHU, FUNC7_MULDIV) => Rv32ImInstruction::Mulhu(rd, rs1, rs2),
                (FUNC3_DIV, FUNC7_MULDIV) => Rv32ImInstruction::Div(rd, rs1, rs2),
                (FUNC3_DIVU, FUNC7_MULDIV) => Rv32ImInstruction::Divu(rd, rs1, rs2),
                (FUNC3_REM, FUNC7_MULDIV) => Rv32ImInstruction::Rem(rd, rs1, rs2),
                (FUNC3_REMU, FUNC7_MULDIV) => Rv32ImInstruction::Remu(rd, rs1, rs2),
                (_, _) => panic!("Unknown arithmetic func3: {:#05b} {:#09b}", func3, func7),
            }
        }
        OPCODE_CUSTOM_0 => {
            let func3 = decode_func3!(ir);
            let func7 = decode_func7!(ir);
            let rd = decode_rd!(ir);
            let rs1 = decode_rs1!(ir);
            let rs2 = decode_rs2!(ir);
            // println!("OPCODE_CUSTOM: rd: {rd}, rs1: {rs1}, rs2: {rs2}, func3: {func3}");
            // match func3 {
            //     0 => Rv32ImInstruction::BBAdd(rd, rs1, rs2),
            //     1 => Rv32ImInstruction::BBSub(rd, rs1, rs2),
            //     2 => Rv32ImInstruction::BBMul(rd, rs1, rs2),
            //     3 => Rv32ImInstruction::BBDiv(rd, rs1, rs2),
            //     _ => panic!("Unknown custom func3: {}", func3),
            // }
            Rv32ImInstruction::Custom0(RType {
                func3,
                func7,
                rd,
                rs1,
                rs2,
            })
        }
        OPCODE_SYSTEM => {
            let rs2 = decode_rs2!(ir);
            // panic!("Unrecognized opcode: {opcode} {:#034b} {:#010b}", ir, opcode);
            Rv32ImInstruction::Syscall(rs2 as u32)
        }
        _ => panic!(
            "Unrecognized opcode: {opcode} {:#034b} {:#010b}",
            ir, opcode
        ),
    }
}
