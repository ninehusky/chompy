use egg::{Pattern, Rewrite};

use crate::conditions::implication::EqApplier;
use crate::halide::Pred;
use crate::SynthAnalysis;

pub mod assumption;
pub mod generate;
pub mod implication;
pub mod implication_set;
mod manager;

pub fn merge_eqs() -> Rewrite<Pred, SynthAnalysis> {
    let searcher: Pattern<Pred> = "(assume (== ?a ?b))".parse().unwrap();
    // union ?a and ?b.
    let applier = EqApplier {
        a: "?a".parse().unwrap(),
        b: "?b".parse().unwrap(),
    };

    Rewrite::new("assume-eqs", searcher, applier).unwrap()
}
