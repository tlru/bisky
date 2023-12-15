/// https://github.com/trmckay/lib-rv32/blob/main/isa-sim/src/decode.rs

// Example:
///
/// ```
/// use binary_format::bit_slice;
/// bit_slice!(0b1101, 3, 2) == 0b11;
/// bit_slice!(0b1101, 1) == 0b0;
/// ```
#[macro_export]
macro_rules! bit_slice {
    ($n:expr, $i:expr) => {
        ($n & (0b1 << $i)) >> $i
    };

    ($n:expr, $msb:expr, $lsb:expr) => {
        ($n & (((0b1 << ($msb - $lsb + 1)) - 1) << $lsb)) >> $lsb
    };
}

/// Concatenate the bits of integers.
///
/// Example:
///
/// ```
/// use binary_format::bit_concat;
/// bit_concat!(
///     (0b111, 3),
///     (0b01, 2)
/// ) == 0b11101;
/// ```
#[macro_export]
macro_rules! bit_concat {
    ($($x:expr),*) => {{
        let mut i = 0;
        let mut t = 0;
        for n in [$($x),*].iter().rev() {
            t += n.0 << i;
            i += n.1;
        }
        t
    }}
}

/// Extend a bit (useful for sign extension).
///
/// Example:
///
/// ```
/// use binary_format::bit_extend;
/// bit_extend!(0b1, 8) == 0b1111_1111;
/// ```
#[macro_export]
macro_rules! bit_extend {
    ($n:expr, $r:expr) => {
        match $n {
            0 => 0,
            _ => (0..$r).map(|i| 1 << i).sum(),
        }
    };
}

/// Like `bit_slice`, but outputs the result and its
/// size in a tuple.
#[macro_export]
macro_rules! sized_bit_slice {
    ($n: expr, $i:expr) => {
        ($crate::bit_slice!($n, $i), 1)
    };

    ($n: expr, $msb:expr, $lsb:expr) => {
        ($crate::bit_slice!($n, $msb, $lsb), $msb - $lsb + 1)
    };
}

/// Like `bit_extend`, but outputs the result and its
/// size in a tuple.
#[macro_export]
macro_rules! sized_bit_extend {
    ($n: expr, $r:expr) => {
        ($crate::bit_extend!($n, $r), $r)
    };
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_bit_slice() {
        let x = 0b1011;

        assert_eq!(0b1, bit_slice!(x, 3));
        assert_eq!(0b0, bit_slice!(x, 2));
        assert_eq!(0b1, bit_slice!(x, 1));
        assert_eq!(0b1, bit_slice!(x, 0));

        assert_eq!(0b10, bit_slice!(x, 3, 2));
        assert_eq!(0b101, bit_slice!(x, 3, 1));
        assert_eq!(0b1011, bit_slice!(x, 3, 0));
        assert_eq!(0b011, bit_slice!(x, 2, 0));
        assert_eq!(0b11, bit_slice!(x, 1, 0));
    }

    #[test]
    fn test_bit_concat() {
        assert_eq!(0b1101, bit_concat!((0b11, 2), (0b01, 2)));
    }

    #[test]
    fn test_bit_extend() {
        assert_eq!(0b1111, bit_extend!(1, 4));
        assert_eq!(0b0, bit_extend!(0, 32));
    }
}

/// Decode the J-type immediate from a `u32` formatted instruction.
#[macro_export]
macro_rules! decode_j_imm {
    ($ir:expr) => {
        $crate::bit_concat!(
            $crate::sized_bit_extend!($crate::bit_slice!($ir, 31), 12),
            $crate::sized_bit_slice!($ir, 19, 12),
            $crate::sized_bit_slice!($ir, 20),
            $crate::sized_bit_slice!($ir, 30, 21),
            $crate::sized_bit_extend!(0, 1)
        ) as u32
    };
}

/// Decode the U-type immediate from a `u32` formatted instruction.
#[macro_export]
macro_rules! decode_u_imm {
    ($ir:expr) => {
        $crate::bit_concat!(
            $crate::sized_bit_slice!($ir, 31, 12),
            $crate::sized_bit_extend!(0, 12)
        ) as u32
    };
}

/// Decode the B-type immediate from a `u32` formatted instruction.
#[macro_export]
macro_rules! b_imm {
    ($ir:expr) => {
        $crate::bit_concat!(
            $crate::sized_bit_extend!($crate::bit_slice!($ir, 31), 20),
            $crate::sized_bit_slice!($ir, 7),
            $crate::sized_bit_slice!($ir, 30, 25),
            $crate::sized_bit_slice!($ir, 11, 8),
            $crate::sized_bit_extend!(0, 1)
        ) as u32
    };
}

/// Decode the I-type immediate from a `u32` formatted instruction.
#[macro_export]
macro_rules! decode_i_imm {
    ($ir:expr) => {
        $crate::bit_concat!(
            $crate::sized_bit_extend!($crate::bit_slice!($ir, 31), 20),
            $crate::sized_bit_slice!($ir, 31, 20)
        ) as u32
    };
}

/// Decode the `shamt` immediate from a `u32` formatted instruction.
#[macro_export]
macro_rules! decode_shamt {
    ($ir:expr) => {
        $crate::bit_slice!($ir, 24, 20) as u8
    };
}

/// Decode the S-type immediate from a `u32` formatted instruction.
#[macro_export]
macro_rules! decode_s_imm {
    ($ir:expr) => {
        $crate::bit_concat!(
            $crate::sized_bit_extend!($crate::bit_slice!($ir, 31), 20),
            $crate::sized_bit_slice!($ir, 31, 25),
            $crate::sized_bit_slice!($ir, 11, 7)
        ) as u32
    };
}

/// Decode the FUNC3 field from a `u32` formatted instruction.
#[macro_export]
macro_rules! decode_func3 {
    ($ir:expr) => {
        $crate::bit_slice!($ir, 14, 12) as u8
    };
}

/// Decode the FUNC7 field from a `u32` formatted instruction.
#[macro_export]
macro_rules! decode_func7 {
    ($ir:expr) => {
        $crate::bit_slice!($ir, 31, 25) as u8
    };
}

/// Decode the destination register field from a `u32` formatted instruction.
#[macro_export]
macro_rules! decode_rd {
    ($ir:expr) => {
        $crate::bit_slice!($ir, 11, 7) as u8
    };
}

/// Decode the first operand register field from a `u32` formatted instruction.
#[macro_export]
macro_rules! decode_rs1 {
    ($ir:expr) => {
        $crate::bit_slice!($ir, 19, 15) as u8
    };
}

/// Decode the second operand register field from a `u32` formatted instruction.
#[macro_export]
macro_rules! decode_rs2 {
    ($ir:expr) => {
        $crate::bit_slice!($ir, 24, 20) as u8
    };
}

/// Decode the opcode field from a `u32` formatted instruction.
#[macro_export]
macro_rules! decode_opcode {
    ($ir:expr) => {
        $crate::bit_slice!($ir, 6, 0) as u8
    };
}
