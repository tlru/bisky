use crate::image::ProgramImage;

pub fn test_exec(program: &ProgramImage) {
    let mut pc: u32 = entry;
    let mut reg = [0u32; 32];
    loop {
        let ir = image.get(&pc).unwrap();
        debug_assert!(image.get(&(pc + 1)).is_none());

        let opcode = decode_opcode!(ir);

        // debug!("[pc = {}] [{:04x} = {}]  {:08x}", pc, pc, opcode_name(opcode), ir);

        #[forbid(unused_variables)]
        match opcode {
            OPCODE_LUI => {
                let rd = decode_rd!(ir);
                let imm = decode_u_imm!(ir);
                reg[rd as usize] = imm;
                debug!("LUI {:?}", (rd, imm));
                pc += 4;
            }
            OPCODE_AUIPC => {
                let rd = decode_rd!(*ir);
                let imm = decode_u_imm!(ir);
                debug!(rd, imm, "AUIPC");

                reg[rd as usize] = pc.wrapping_add(imm);

                pc += 4;
            }
            OPCODE_JAL => {
                let rd = decode_rd!(ir);
                let imm = decode_j_imm!(ir);

                reg[rd as usize] = pc + 4;
                debug!("JAL {:?}", (rd, imm));

                pc = pc.wrapping_add(imm);
            }
            OPCODE_JALR => {
                let rd = decode_rd!(ir);
                let rs1 = decode_rs1!(ir);
                let imm = decode_i_imm!(ir);

                let rs1_val = reg[rs1 as usize];
                reg[rd as usize] = pc + 4;

                debug!(rd, rs1, imm, "JALR");

                pc = rs1_val.wrapping_add(imm);
            }
            OPCODE_BRANCH => {
                let rs1 = decode_rs1!(ir);
                let rs2 = decode_rs2!(ir);
                let func3 = decode_func3!(ir);
                let imm = b_imm!(ir);
                assert!(imm % 4 == 0, "Unaligned immediate");

                let rs1_val = reg[rs1 as usize];
                let rs2_val = reg[rs2 as usize];

                let result = match func3 {
                    FUNC3_BEQ => rs1_val == rs2_val,
                    FUNC3_BNE => rs1_val != rs2_val,
                    FUNC3_BLT => rs1_val < rs2_val,
                    FUNC3_BGE => rs1_val >= rs2_val,
                    FUNC3_BLTU => rs1_val < rs2_val,
                    FUNC3_BGEU => rs1_val > rs2_val,
                    _ => panic!("Unknown func3: {}", func3),
                };

                debug!(rs1, rs2, func3, imm, rs1_val, rs2_val, result, "BRANCH");

                if result {
                    pc = pc.wrapping_add(imm);
                } else {
                    pc += 4;
                }
            }
            OPCODE_LOAD => {
                let rs1 = decode_rs1!(ir);
                let base = reg[rs1 as usize];
                let imm = decode_i_imm!(ir);
                let addr = base.wrapping_add(imm);
                let rd = decode_rd!(ir);
                let func3 = decode_func3!(ir);

                debug!(rs1, base, imm, addr, rd, func3, "LOAD");

                pc += 4;
            }
            OPCODE_STORE => {
                let rs1 = decode_rs1!(ir);
                let rs2 = decode_rs2!(ir);
                let imm = decode_s_imm!(ir);
                let func3 = decode_func3!(ir);

                debug!(rs1, rs2, imm, func3, "STORE");

                match func3 {
                    FUNC3_SB => {}
                    FUNC3_SH => {}
                    FUNC3_SW => {}
                    _ => panic!("Unknown STORE func3: {}", func3),
                }

                pc += 4;
            }
            OPCODE_ARITHMETIC_IMM | OPCODE_ARITHMETIC => {
                let rd = decode_rd!(ir);
                let rs1 = decode_rs1!(ir);
                let lhs = reg[rs1 as usize];
                debug!("ARITHMETIC | ARITHMETIC_IMM {:?}", (rd, rs1, lhs));
                pc += 4;
            }
            OPCODE_SYSTEM => {
                debug!("SYSTEM");
                pc += 4;
            }
            _ => panic!("Unknown opcode: {} {:#X}", pc, opcode),
        }
    }
}
