use egg::{Pattern, Rewrite};

use crate::conditions::implication::EqApplier;
use crate::{SynthAnalysis, SynthLanguage};

pub mod assumption;
pub mod generate;
pub mod implication;
pub mod implication_set;
mod manager;

pub fn merge_eqs<L: SynthLanguage>() -> Rewrite<L, SynthAnalysis> {
    let searcher: Pattern<L> = "(assume (== ?a ?b))".parse().unwrap();
    // union ?a and ?b.
    let applier = EqApplier {
        a: "?a".parse().unwrap(),
        b: "?b".parse().unwrap(),
    };

    Rewrite::new("assume-eqs", searcher, applier).unwrap()
}
