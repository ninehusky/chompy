// Chompy's representation of LLVM, for now, is more or less
// the bitvector language, but with some extra operators.

use crate::*;

egg::define_language! {
    pub enum LlvmIr {
        "mul" = Mul([Id; 2]),
        // icmp eq
        "eq"= Eq([Id; 2]),
        Var(Symbol),
        Lit(u128),
    }
}

impl SynthLanguage for LlvmIr {
    type Constant = BV<64>;

    fn eval<'a, F>(&'a self, cvec_len: usize, mut get_cvec: F) -> CVec<Self>
        where
            F: FnMut(&'a Id) -> &'a CVec<Self> {
        match self {
            LlvmIr::Mul([a, b]) => map!(get_cvec, a, b => Some(a.wrapping_mul(*b))),
            LlvmIr::Eq([a, b]) => map!(get_cvec, a, b => Some(if a == b { BV::from(1) } else { BV::from(0) })),
            LlvmIr::Lit(n) => vec![Some(BV::from(*n)); cvec_len],
            LlvmIr::Var(_) => vec![],
        }
    }

    fn initialize_vars(egraph: &mut EGraph<Self, SynthAnalysis>, vars: &[String]) {
        let mut consts = vec![];

        for i in 0..2 {
            let i = BV::from(i);
            consts.push(Some(BV::MIN.wrapping_add(i)));
            consts.push(Some(BV::MAX.wrapping_sub(i)));
            consts.push(Some(i));
            consts.push(Some(i.wrapping_neg()));
        }
        consts.sort();
        consts.dedup();

        let mut cvecs = self_product(&consts, vars.len());

        egraph.analysis.cvec_len = cvecs[0].len();

        for (i, v) in vars.iter().enumerate() {
            let id = egraph.add(LlvmIr::Var(Symbol::from(v.clone())));
            egraph[id].data.cvec = cvecs[i].clone()
        }
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
