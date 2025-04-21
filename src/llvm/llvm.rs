// Chompy's representation of LLVM, for now, is more or less
// the bitvector language, but with some extra operators.

use crate::*;

use llvm::bitvector::LlvmBitvector;

egg::define_language! {
    pub enum LlvmIr {
        "mul" = Mul([Id; 2]),
        // icmp eq
        "eq"= Eq([Id; 2]),
        Const(LlvmBitvector),
        Var(Symbol),
    }
}

impl SynthLanguage for LlvmIr {
    type Constant = LlvmBitvector;

    fn eval<'a, F>(&'a self, cvec_len: usize, mut get_cvec: F) -> CVec<Self>
        where
            F: FnMut(&'a Id) -> &'a CVec<Self> {
        match self {
            LlvmIr::Mul([a, b]) => map!(get_cvec, a, b => Some(a.wrapping_mul(*b))),
            LlvmIr::Eq([a, b]) => map!(get_cvec, a, b => {
                assert_eq!(a.width, b.width);
                if a.value == b.value {
                    Some(LlvmBitvector::new(1, 1))
                } else {
                    Some(LlvmBitvector::new(0, 1))
                }
            }),
            LlvmIr::Const(c) => vec![Some(*c); cvec_len],
            LlvmIr::Var(_) => vec![],
        }
    }

    fn initialize_vars(egraph: &mut EGraph<Self, SynthAnalysis>, vars: &[String]) {
        todo!()
        // let mut consts = vec![];

        // for i in 0..2 {
        //     let i = BV::from(i);
        //     consts.push(Some(BV::MIN.wrapping_add(i)));
        //     consts.push(Some(BV::MAX.wrapping_sub(i)));
        //     consts.push(Some(i));
        //     consts.push(Some(i.wrapping_neg()));
        // }
        // consts.sort();
        // consts.dedup();

        // let mut cvecs = self_product(&consts, vars.len());

        // egraph.analysis.cvec_len = cvecs[0].len();

        // for (i, v) in vars.iter().enumerate() {
        //     let id = egraph.add(LlvmIr::Var(Symbol::from(v.clone())));
        //     egraph[id].data.cvec = cvecs[i].clone()
        // }
    }

    fn to_var(&self) -> Option<Symbol> {
        todo!()
    }

    fn mk_var(sym: Symbol) -> Self {
        todo!()
    }

    fn is_constant(&self) -> bool {
        todo!()
    }

    fn mk_constant(c: Self::Constant, egraph: &mut EGraph<Self, SynthAnalysis>) -> Self {
        todo!()
    }


    fn validate(lhs: &Pattern<Self>, rhs: &Pattern<Self>) -> ValidationResult {
        todo!()
    }

    fn validate_with_cond(
            _lhs: &Pattern<Self>,
            _rhs: &Pattern<Self>,
            _cond: &Pattern<Self>,
        ) -> ValidationResult {
        todo!()
    }
}


pub mod tests {
    use super::*;
    #[test]
    // corresponds to `souper_tests/1.opt` in the
    // alive-nj repo
    pub fn opt_1_test() {
        // if (>= (^ C1 1) C1) then (eq (bv 1 32) (mul C1 x)) ==> (bv 0 1)
    }

}