use crate::{
    conditions::implication_set::ImplicationSet,
    HashMap, SynthAnalysis, SynthLanguage,
};

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
    pub term_egraph: egg::EGraph<L, SynthAnalysis>,
    pub chosen: Ruleset<L>,
    // the last three fields might change significantly in the future,
    // as we explore what the best way to find predicates is.
    pub predicates: Workload,
    pub implications: ImplicationSet<L>,
}
