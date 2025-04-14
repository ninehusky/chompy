// use crate::*;

// egg::define_language! {
//     pub enum LlvmIr {
//         "mul" = Mul([Id; 2]),
//         // icmp eq
//         "eq"= Eq([Id; 2]),
//         Var(Symbol),
//         Lit(i64),
//     }
// }

// impl SynthLanguage for LlvmIr {
//     type Constant = BV<32>;

//     fn eval(&self, _env: &mut egg::EGraph<Self, ()>, _id: Id) -> Self::Constant {
//         unimplemented!()
//     }
// }
