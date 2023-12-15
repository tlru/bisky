/// rd, rs1, rs2
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct RType {
    pub func3: u8,
    pub func7: u8,
    pub rd: u8,
    pub rs1: u8,
    pub rs2: u8,
}

/// rd, rs1, imm
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct IType {
    pub rd: u8,
    pub rs1: u8,
    pub imm: u32,
}

/// rs1, rs2, imm
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct BType {
    pub rs1: u8,
    pub rs2: u8,
    pub imm: u32,
}

/// rd, imm
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct UType {
    pub rd: u8,
    pub imm: u32,
}

/// rd, imm
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct JType {
    pub rd: u8,
    pub imm: u32,
}
