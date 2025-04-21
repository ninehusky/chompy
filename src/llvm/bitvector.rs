// This is a variable-width bitvector implementation for
// Chompy's representation of LLVM IR.
// We already have a bitvector implementation in `src/bv.rs`,
// but this one is more specialized for LLVM -- the variable
// bitwidths hopefully help capture the different types
// present in LLVM IR.

// byeah


use std::{f32::consts::E, fmt::{Debug, Display}, ops::{BitAnd, BitXor}, str::FromStr};

use symbolic_expressions::{parser::parse_str, Sexp};

#[derive(Copy, Clone, Hash, PartialOrd, Ord, PartialEq, Eq)]
pub struct LlvmBitvector {
    pub value: u64,
    pub width: u64,
}

impl LlvmBitvector {
    pub fn new(value: u64, width: u64) -> Self {
        assert!(width <= 64);
        assert!(value < (1 << width));

        LlvmBitvector {
            value,
            width,
        } & LlvmBitvector::all_ones(width)
    }

    pub fn all_ones(width: u64) -> Self {
        let width = width.into();
        let one: u64 = 1;
        LlvmBitvector {
            value: (one << width) - 1,
            width,
        }
    }

    pub fn wrapping_mul(self, rhs: Self) -> Self {
        assert_eq!(self.width, rhs.width);
        let width = self.width;
        // the following line looks suspicious.
        let value = (self.value as u128).wrapping_mul(rhs.value as u128) as u64;
        LlvmBitvector {
            value: value & ((1 << width) - 1),
            width,
        }
    }

}

impl Debug for LlvmBitvector {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(bv {:?} {})", self.value, self.width)
    }
}

impl Display for LlvmBitvector {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(bv {:?} {})", self.value, self.width)
    }
}

impl FromStr for LlvmBitvector {
    type Err = ();

    /// ```
    /// use ruler::llvm::bitvector::LlvmBitvector;
    /// let bv: LlvmBitvector = "(bv 1 2)".parse().unwrap();
    /// assert_eq!(bv.value, 1);
    /// assert_eq!(bv.width, 2);
    /// ```
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // match on `(bv value width)`
        match parse_str(s) {
            Ok(Sexp::List(l)) => {
                if l.len() != 3 || l[0] != Sexp::String("bv".to_string()) {
                    return Err(());
                }
                let value = match l[1] {
                    Sexp::String(ref s) => s.parse::<u64>().map_err(|_| ())?,
                    _ => return Err(()),
                };
                let width = match l[2] {
                    Sexp::String(ref s) => s.parse::<u64>().map_err(|_| ())?,
                    _ => return Err(()),
                };
                Ok(LlvmBitvector::new(value, width))
            }
            _ => return Err(())
        }
    }
}

impl BitAnd for LlvmBitvector {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        assert_eq!(self.width, rhs.width);
        LlvmBitvector {
            value: self.value & rhs.value,
            width: self.width,
        }
    }
}

impl BitXor for LlvmBitvector {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        assert_eq!(self.width, rhs.width);
        LlvmBitvector {
            value: self.value ^ rhs.value,
            width: self.width,
        }
    }
}

pub mod tests {
    use super::*;

    #[test]
    fn test_widening_mul() {
        let a = LlvmBitvector::new(1, 2);
        let b = LlvmBitvector::new(2, 2);
        assert_eq!(a.wrapping_mul(b), LlvmBitvector::new(2, 2));
    }

    #[test]
    fn test_overflow_mul() {
        let a = LlvmBitvector::new(3, 2);
        let b = LlvmBitvector::new(2, 2);
        assert_eq!(a.wrapping_mul(b), LlvmBitvector::new(2, 2));
    }

    #[test]
    fn test_bitand() {
        let a = LlvmBitvector::new(3, 2);
        let b = LlvmBitvector::new(1, 2);
        assert_eq!(a & b, LlvmBitvector::new(1, 2));
    }

    #[test]
    fn test_bitxor() {
        let a = LlvmBitvector::new(0b0011, 4);
        let b = LlvmBitvector::new(0b1010, 4);
        assert_eq!(a ^ b, LlvmBitvector::new(0b1001, 4));
        assert_eq!(a ^ a, LlvmBitvector::new(0b0000, 4));
    }
}