use easter_egg::*;

use crate::SynthAnalysis;

type Constant = i32;

easter_egg::define_language! {
  pub enum Pred {
    Lit(Constant),
    "abs" = Abs(Id),
    "<" = Lt([Id;2]),
    "<=" = Leq([Id;2]),
    ">" = Gt([Id;2]),
    ">=" = Geq([Id;2]),
    "==" = Eq([Id;2]),
    "!=" = Neq([Id;2]),
    "->" = Implies([Id; 2]),
    "!" = Not(Id),
    "-" = Neg(Id),
    "&&" = And([Id;2]),
    "||" = Or([Id;2]),
    "^" = Xor([Id;2]),
    "+" = Add([Id; 2]),
    "-" = Sub([Id; 2]),
    "*" = Mul([Id; 2]),
    "/" = Div([Id; 2]),
    "%" = Mod([Id; 2]),
    "min" = Min([Id; 2]),
    "max" = Max([Id; 2]),
    "select" = Select([Id; 3]),
    "istrue" = IsTrue(Id),
    Var(Symbol),
  }
}


pub fn seed_egraph(conditions: Vec<String>) {
    // we need to have one color per condition.
    let egraph = easter_egg::EGraph::new();
}
