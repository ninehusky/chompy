// This is a variable-width bitvector implementation for
// Chompy's representation of LLVM IR.
// We already have a bitvector implementation in `src/bv.rs`,
// but this one is more specialized for LLVM -- the variable
// bitwidths hopefully help capture the different types
// present in LLVM IR.

// byeah


use std::{fmt::Debug, ops::BitAnd};


#[derive(Copy, Clone, Hash, PartialOrd, Ord, PartialEq, Eq)]
pub struct LLVMBitvector {
    pub value: u64,
    pub width: u64,
}

impl LLVMBitvector {
    pub fn new(value: u64, width: u64) -> Self {
        assert!(width <= 64);
        assert!(value < (1 << width));

        LLVMBitvector {
            value,
            width,
        } & LLVMBitvector::all_ones(width)
    }

    pub fn all_ones(width: u64) -> Self {
        let width = width.into();
        let one: u64 = 1;
        LLVMBitvector {
            value: (one << width) - 1,
            width,
        }
    }

    pub fn wrapping_mul(self, rhs: Self) -> Self {
        assert_eq!(self.width, rhs.width);
        let width = self.width;
        // the following line looks suspicious.
        let value = (self.value as u128).wrapping_mul(rhs.value as u128) as u64;
        LLVMBitvector {
            value: value & ((1 << width) - 1),
            width,
        }
    }

}

impl Debug for LLVMBitvector {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(bv {:?} {})", self.value, self.width)
    }
}

impl BitAnd for LLVMBitvector {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        assert_eq!(self.width, rhs.width);
        LLVMBitvector {
            value: self.value & rhs.value,
            width: self.width,
        }
    }
}

pub mod tests {
    use super::*;

    #[test]
    fn test_widening_mul() {
        let a = LLVMBitvector::new(1, 2);
        let b = LLVMBitvector::new(2, 2);
        assert_eq!(a.wrapping_mul(b), LLVMBitvector::new(2, 2));
    }

    #[test]
    fn test_overflow_mul() {
        let a = LLVMBitvector::new(3, 2);
        let b = LLVMBitvector::new(2, 2);
        assert_eq!(a.wrapping_mul(b), LLVMBitvector::new(2, 2));
    }

    #[test]
    fn test_bitand() {
        let a = LLVMBitvector::new(3, 2);
        let b = LLVMBitvector::new(1, 2);
        assert_eq!(a & b, LLVMBitvector::new(1, 2));
    }
}