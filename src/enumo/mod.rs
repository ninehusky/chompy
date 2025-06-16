use crate::{conditions::implication::Implication, HashMap, SynthAnalysis, SynthLanguage};

use egg::Rewrite;
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
/// - `pvec_to_patterns`: A memoization map from predicate vectors to their matched patterns.
pub struct ChompyState<L: SynthLanguage> {
    pub term_egraph: egg::EGraph<L, SynthAnalysis>,
    pub chosen: Ruleset<L>,
    pub predicates: Workload,
    pub implications: Vec<Implication<L>>,
    pub pvec_to_patterns: HashMap<Vec<bool>, Vec<egg::Pattern<L>>>,
}
