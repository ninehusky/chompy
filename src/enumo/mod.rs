use crate::{
    conditions::implication_set::{run_implication_workload, ImplicationSet},
    HashMap, IndexMap, PVec, SynthAnalysis, SynthLanguage,
};

use egg::{AstSize, Extractor, Rewrite};
pub use filter::*;
pub use metric::*;
pub use pattern::*;
pub use rule::*;
pub use ruleset::*;
pub use scheduler::*;
pub use sexp::*;
pub use workload::*;

mod filter;
mod metric;
mod pattern;
mod rule;
mod ruleset;
mod scheduler;
mod sexp;
mod workload;

/// Core state used during Chompy synthesis.
///
/// This state is created at the beginning of a synthesis session and evolves as
/// Chompy runs.
///
/// Fields:
/// - `term_egraph`: The e-graph of expressions over the language `L`.
/// - `chosen`: The current set of rewrite rules that have been selected.
/// - `predicates`: The current workload of predicates (conditions to consider).
/// - `implications`: Known, valid implications used to prune or derive rewrites.
pub struct ChompyState<L: SynthLanguage> {
    terms: Workload,
    chosen: Ruleset<L>,
    predicates: Workload,
    pvec_to_patterns: PredicateMap<L>,
    implications: ImplicationSet<L>,
}

impl<L: SynthLanguage> ChompyState<L> {
    pub fn terms(&self) -> &Workload {
        &self.terms
    }

    pub fn chosen(&self) -> &Ruleset<L> {
        &self.chosen
    }

    pub fn chosen_mut(&mut self) -> &mut Ruleset<L> {
        &mut self.chosen
    }

    pub fn predicates(&self) -> &Workload {
        &self.predicates
    }

    pub fn implications(&self) -> &ImplicationSet<L> {
        &self.implications
    }

    pub fn predicates_mut(&mut self) -> &mut Workload {
        &mut self.predicates
    }

    pub fn pvec_to_patterns(&self) -> PredicateMap<L> {
        build_pvec_to_patterns(self.predicates.clone())
    }

    pub fn new(terms: Workload, prior: Ruleset<L>, predicates: Workload) -> Self {
        let pvec_to_patterns = if predicates.is_empty() {
            Default::default()
        } else {
            build_pvec_to_patterns(predicates.clone())
        };

        let implications = if predicates.is_empty() {
            ImplicationSet::default()
        } else {
            run_implication_workload(&predicates, &ImplicationSet::default(), &prior)
        };

        Self {
            terms,
            chosen: prior,
            pvec_to_patterns,
            predicates,
            implications,
        }
    }
}

// Given a conditional workload, returns a map from boolean vectors (pvecs)
// to the patterns in the e-graph with that fuzzed pvec. This is needed for finding conditional
// candidates.
// This is going to be really bad if the variables that are in the workload are not the same as
// the variables in the "main egraph" that's inside the corresponding `ChompyState`.
fn build_pvec_to_patterns<L: SynthLanguage>(wkld: Workload) -> PredicateMap<L> {
    let egraph = wkld.to_egraph::<L>();
    let mut pvec_to_patterns: PredicateMap<L> = IndexMap::default();
    let extractor = Extractor::new(&egraph, AstSize);
    for c in egraph.classes() {
        let recexpr_tuple = extractor.find_best(c.id);
        let recexpr = &recexpr_tuple.1;
        let pat: egg::Pattern<L> = L::generalize(recexpr, &mut Default::default());

        if !L::pattern_is_predicate(&pat) {
            continue;
        }

        let pvec = c
            .data
            .cvec
            .iter()
            .map(|x| {
                if let Some(p) = x.as_ref() {
                    L::to_bool(p.clone()).unwrap()
                } else {
                    false
                }
            })
            .collect::<PVec>();

        pvec_to_patterns
            .entry(pvec.clone())
            .or_default()
            .push(recexpr.to_string().parse().unwrap());
    }
    pvec_to_patterns
}
