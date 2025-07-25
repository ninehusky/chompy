use std::{
    fmt::{Debug, Display},
    hash::Hash,
    str::FromStr,
};

use conditions::assumption::Assumption;
use egg::{
    Analysis, Applier, AstSize, CostFunction, DidMerge, ENodeOrVar, FromOp, Language, PatternAst,
    RecExpr, Rewrite, Subst,
};
use enumo::lookup_pattern;

use crate::{
    conditions::implication::{Implication, ImplicationValidationResult},
    enumo::Sexp,
    *,
};

// An `ImplicationSwitch` models the implication of one condition to another.
//
// For example, given conditions `c`, `c'`, if that `c` implies `c'`,
// then an `ImplicationSwitch` will model the implication `c => c'`.
// In practice, the user is responsible for setting up the fact that `c` is true
// in the e-graph through adding the term `(IsTrue c)`.
//
// When the corresponding `ImplicationSwitch` is run (i.e., when it's run as a rule),
// then it will add `(assume c')` to the e-graph, paving the way for conditional rewrite
// rules.
pub struct ImplicationSwitch<L: SynthLanguage> {
    pub(crate) parent_cond: Pattern<L>,
    pub(crate) my_cond: Pattern<L>,
}

struct ImplicationApplier<L: SynthLanguage> {
    parent_cond: Pattern<L>,
    my_cond: Pattern<L>,
}

// Given a subst and a pattern, this function adds the substituted pattern to the egraph.
pub(crate) fn apply_pat<L: Language, A: Analysis<L>>(
    pat: &[ENodeOrVar<L>],
    egraph: &mut EGraph<L, A>,
    subst: &Subst,
) -> Id {
    let mut ids = vec![0.into(); pat.len()];

    for (i, pat_node) in pat.iter().enumerate() {
        let id = match pat_node {
            ENodeOrVar::Var(w) => subst[*w],
            ENodeOrVar::ENode(e) => {
                let n = e.clone().map_children(|child| ids[usize::from(child)]);
                egraph.add(n)
            }
        };
        ids[i] = id;
    }

    *ids.last().unwrap()
}

impl<L> Applier<L, SynthAnalysis> for ImplicationApplier<L>
where
    L: SynthLanguage,
{
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<L, SynthAnalysis>,
        _eclass: egg::Id,
        subst: &egg::Subst,
        _searcher_ast: Option<&PatternAst<L>>,
        _rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        // it better be the case that the parent condition exists in the e-graph.
        let is_true_parent_pattern: Pattern<L> =
            format!("({} {})", L::assumption_label(), self.parent_cond)
                .parse()
                .unwrap();

        assert!(
            lookup_pattern(&is_true_parent_pattern, egraph, subst),
            "Parent condition {} must be true in the e-graph before applying implication.",
            self.parent_cond
        );

        let is_true_my_pattern: Pattern<L> =
            format!("({} {})", L::assumption_label(), self.my_cond)
                .parse()
                .unwrap();

        if lookup_pattern(&is_true_my_pattern, egraph, subst) {
            // we already have the condition in the egraph, so no need to add it.
            return vec![];
        }

        let new_id = apply_pat(
            is_true_my_pattern.ast.as_ref().iter().as_slice(),
            egraph,
            subst,
        );

        vec![new_id]
    }
}

impl<L: SynthLanguage> ImplicationSwitch<L> {
    pub fn new(parent_cond: &Pattern<L>, my_cond: &Pattern<L>) -> Self {
        Self {
            parent_cond: parent_cond.clone(),
            my_cond: my_cond.clone(),
        }
    }

    pub fn rewrite(&self) -> Rewrite<L, SynthAnalysis> {
        // uhh okay so the searcher is just gonna be a simple searcher for
        // the expression `(IsTrue <parent_cond>)`.
        let searcher: Pattern<L> = format!("(assume {})", self.parent_cond).parse().unwrap();

        let applier: ImplicationApplier<L> = ImplicationApplier {
            parent_cond: self.parent_cond.clone(),
            my_cond: self.my_cond.clone(),
        };

        println!("searcher is for : {searcher}");
        // NOTE @ninehusky: I made the string like this so that we don't confuse it with
        // a rewrite rule.
        Rewrite::new(
            format!("{} implies {}", self.parent_cond, self.my_cond),
            searcher,
            applier,
        )
        .unwrap()
    }
}

#[derive(Clone)]
pub struct SynthAnalysis {
    pub cvec_len: usize,
}

#[allow(clippy::derivable_impls)]
impl Default for SynthAnalysis {
    fn default() -> Self {
        // No cvecs by default. Domains that do cvec matching are responsible
        // for setting the cvec length when they initialize variables.
        Self { cvec_len: 0 }
    }
}

#[derive(Debug, Clone)]
pub struct Signature<L: SynthLanguage> {
    pub cvec: CVec<L>,
    pub simplest: RecExpr<L>,
    pub interval: Interval<L::Constant>,
}

impl<L: SynthLanguage> Signature<L> {
    pub fn is_defined(&self) -> bool {
        self.cvec.is_empty() || self.cvec.iter().any(|v| v.is_some())
    }
}

impl<L: SynthLanguage> Analysis<L> for SynthAnalysis {
    type Data = Signature<L>;

    fn make(egraph: &EGraph<L, Self>, enode: &L) -> Self::Data {
        let get_cvec = |id: &Id| &egraph[*id].data.cvec;
        let get_interval = |id: &Id| &egraph[*id].data.interval;
        let get_simplest = |i: &Id| &egraph[*i].data.simplest;

        let simplest = if enode.is_var() || enode.is_constant() {
            let mut rec = RecExpr::<L>::default();
            rec.add(enode.clone());
            rec
        } else {
            let mut nodes: Vec<L> = vec![];
            let mut map: HashMap<Id, Id> = HashMap::default();
            enode.for_each(|id| {
                map.entry(id).or_insert_with(|| {
                    let s = get_simplest(&id);
                    let i = nodes.len();
                    for n in s.as_ref() {
                        nodes.push(n.clone().map_children(|id| Id::from(usize::from(id) + i)));
                    }

                    Id::from(nodes.len() - 1)
                });
            });

            nodes.push(enode.clone().map_children(|id| *map.get(&id).unwrap()));
            RecExpr::from(nodes)
        };

        let cvec = enode.eval(egraph.analysis.cvec_len, get_cvec);

        Signature {
            cvec,
            interval: enode.mk_interval(get_interval),
            simplest,
        }
    }

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        let mut merge_a = false;
        let mut merge_b = false;
        let cost_fn = |x: &RecExpr<L>| ExtractableAstSize.cost_rec(x);

        if !to.cvec.is_empty() && !from.cvec.is_empty() {
            for i in 0..to.cvec.len() {
                match (to.cvec[i].clone(), from.cvec[i].clone()) {
                    (None, Some(_)) => {
                        to.cvec[i] = from.cvec[i].clone();
                        merge_a = true;
                    }
                    // This is really dangerous.
                    (Some(_), _) => {
                        merge_b = true;
                    }
                    // (Some(x), Some(y)) => assert_eq!(
                    //     x, y,
                    //     "cvecs do not match!!: to is {:?}\n, from is {:?}",
                    //     to, from
                    // ),
                    _ => (),
                }
            }
        }

        // New interval is max of mins, min of maxes
        let new_min = match (to.interval.low.as_ref(), from.interval.low.as_ref()) {
            (None, None) => None,
            (None, Some(y)) => Some(y.clone()),
            (Some(x), None) => Some(x.clone()),
            (Some(x), Some(y)) => Some(x.max(y).clone()),
        };
        let new_max = match (to.interval.high.as_ref(), from.interval.high.as_ref()) {
            (None, None) => None,
            (None, Some(y)) => Some(y.clone()),
            (Some(x), None) => Some(x.clone()),
            (Some(x), Some(y)) => Some(x.min(y).clone()),
        };
        let new_interval = Interval::new(new_min, new_max);

        if cost_fn(&from.simplest) < cost_fn(&to.simplest) {
            to.simplest = from.simplest;
            merge_a = true;
        } else if to.simplest != from.simplest {
            merge_b = true;
        }

        if to.interval != new_interval {
            to.interval = new_interval;
            merge_a = true;
        }

        if to.interval != from.interval {
            merge_b = true;
        }

        DidMerge(merge_a, merge_b)
    }

    fn modify(egraph: &mut EGraph<L, Self>, id: Id) {
        L::custom_modify(egraph, id);

        let interval = &egraph[id].data.interval;
        if let Interval {
            low: Some(low),
            high: Some(high),
        } = interval
        {
            if low == high {
                let enode = L::mk_constant(low.clone(), egraph);
                let added = egraph.add(enode);
                egraph.union(id, added);
            }
        }
    }
}

/// Characteristic Vector. Concrete evaluation on a sample of terms from the
/// domain, used to identify rule candidates.
pub type CVec<L> = Vec<Option<<L as SynthLanguage>::Constant>>;

/// Predicate Vector. Like a CVec, but used for predicates.
pub type PVec = Vec<bool>;

/// Value type in the domain.
pub type Constant<L> = <L as SynthLanguage>::Constant;

/// Trait for defining a language for which to synthesize rewrites.
pub trait SynthLanguage: Language + Send + Sync + Display + FromOp + 'static {
    /// Domain value type
    type Constant: Clone + Hash + Eq + Debug + Display + Ord;

    /// The name of the language (egglog name).
    fn name() -> &'static str {
        unimplemented!()
    }

    /// Returns if the pattern is an assumption.
    fn pattern_is_assumption<L: SynthLanguage>(pat: &Pattern<L>) -> bool {
        // TODO(@ninehusky): let's keep tabs on the performance of this.
        // If for some reason this is bad, we can just convert the pattern to a string.
        match &pat.ast.as_ref().last().unwrap() {
            egg::ENodeOrVar::ENode(e) => L::is_assumption(e),
            egg::ENodeOrVar::Var(_) => false,
        }
    }

    fn pattern_is_predicate<L: SynthLanguage>(pat: &Pattern<L>) -> bool {
        // TODO(@ninehusky): let's keep tabs on the performance of this. (see above)
        match &pat.ast.as_ref().last().unwrap() {
            egg::ENodeOrVar::ENode(e) => e.is_predicate(),
            egg::ENodeOrVar::Var(_) => false,
        }
    }

    fn is_predicate(&self) -> bool {
        false
    }

    /// Returns if the node is an assumption.
    fn is_assumption(&self) -> bool {
        false
    }

    /// Returns the egglog definition for this language.
    /// See the implementation of [`crate::halide::Pred`] for an example of how to do this.
    fn egglog_lang_def() -> String {
        unimplemented!()
    }

    /// Returns the egglog representation of a pattern in this language.
    /// See the implementation of [`crate::halide::Pred`] for an example of how to do this.
    fn to_egglog_term(_pat: Pattern<Self>) -> String {
        unimplemented!()
    }

    /// Convert a constant to a bool if possible.
    fn to_bool(_c: Self::Constant) -> Option<bool> {
        unimplemented!()
    }

    /// Label for assumption nodes.
    /// Don't mess with this unless you know what you're doing.
    fn assumption_label() -> &'static str {
        "assume"
    }

    /// Hook into the e-graph analysis modify method
    /// Useful for domain-specific purposes (for example, constant folding)
    fn custom_modify(_egraph: &mut EGraph<Self, SynthAnalysis>, _id: Id) {}

    /// Interpreter for the domain.
    /// This should return a CVec of the specified length
    /// get_cvec can be used to get the CVecs of children nodes
    fn eval<'a, F>(&'a self, cvec_len: usize, _get_cvec: F) -> CVec<Self>
    where
        F: FnMut(&'a Id) -> &'a CVec<Self>;

    /// Interval analysis for the domain.
    /// By default, returns (-∞, ∞)
    fn mk_interval<'a, F>(&'a self, _get_interval: F) -> Interval<Self::Constant>
    where
        F: FnMut(&'a Id) -> &'a Interval<Self::Constant>,
    {
        Interval::default()
    }

    /// This function gets called when converting a workload to an e-graph
    /// Given a list of variable names, it must add the variables to
    /// the e-graph and may optionally do any additional initialization.
    ///
    /// Most commonly, this involves initializing the CVecs for variables with
    /// sampled values from the domain.
    fn initialize_vars(egraph: &mut EGraph<Self, SynthAnalysis>, vars: &[String]);

    fn to_var(&self) -> Option<Symbol>;

    /// Given a symbol, construct a variable node
    fn mk_var(sym: Symbol) -> Self;

    /// Whether the node is a variable.
    fn is_var(&self) -> bool {
        self.to_var().is_some()
    }

    /// Whether the node is a constant.
    fn is_constant(&self) -> bool;

    /// Given a constant value, construct a node.
    ///
    /// Most domains won't need to use the egraph parameter to add a constant node.
    /// However, Nat represents numbers recursively, so adding a new constant
    /// requires adding multiple nodes to the egraph.
    fn mk_constant(c: Self::Constant, egraph: &mut EGraph<Self, SynthAnalysis>) -> Self;

    /// Given a node, construct a pattern node
    fn to_enode_or_var(self) -> ENodeOrVar<Self> {
        match self.to_var() {
            Some(var) => ENodeOrVar::Var(format!("?{var}").parse().unwrap()),
            None => ENodeOrVar::ENode(self),
        }
    }

    /// Configures whether to run fast-forwarding or cvec algorithm for
    /// finding candidates.
    /// If fast-forwarding is enabled, L::get_exploratory_rules() and L::is_allowed_op()
    /// must be implemented
    fn is_fast_forwarding() -> bool {
        false
    }

    /// Required for fast-forwarding
    ///
    /// These are the exploratory rules that run in the second phase of the
    /// fast-forwarding algorithm
    fn get_exploratory_rules() -> Ruleset<Self> {
        panic!("No exploratory rules")
    }

    /// Required for fast-forwarding
    ///
    /// Determines whether a node may appear in a synthesized rule
    fn is_allowed_op(&self) -> bool {
        true
    }

    /// Used by fast-forwarding
    ///
    /// Determines whether a rewrite rule may be selected.
    /// A rewrite rule is allowed if it only contains allowed nodes on both sides.
    fn is_allowed_rewrite(lhs: &Pattern<Self>, rhs: &Pattern<Self>) -> bool {
        let pattern_is_extractable = |pat: &Pattern<Self>| {
            pat.ast.as_ref().iter().all(|n| match n {
                ENodeOrVar::ENode(n) => n.is_allowed_op(),
                ENodeOrVar::Var(_) => true,
            })
        };
        pattern_is_extractable(lhs) && pattern_is_extractable(rhs)
    }

    fn generalize(expr: &RecExpr<Self>, map: &mut HashMap<Symbol, Var>) -> Pattern<Self> {
        let mut rename_node = |node: &Self| match node.to_var() {
            Some(sym) => {
                let len = map.len();
                let var = map
                    .entry(sym)
                    .or_insert_with(|| format!("?{}", letter(len)).parse().unwrap());
                let s = var.to_string();
                Self::mk_var(s[1..].into())
            }
            None => node.clone(),
        };
        let root = rename_node(expr.as_ref().last().unwrap());
        let expr = root.build_recexpr(|id| rename_node(&expr[id]));
        let nodes: Vec<ENodeOrVar<Self>> = expr
            .as_ref()
            .iter()
            .map(|node| node.clone().to_enode_or_var())
            .collect();
        PatternAst::from(nodes).into()
    }

    fn instantiate(pattern: &Pattern<Self>) -> RecExpr<Self> {
        let nodes: Vec<_> = pattern
            .ast
            .as_ref()
            .iter()
            .map(|n| match n {
                ENodeOrVar::ENode(n) => n.clone(),
                ENodeOrVar::Var(v) => {
                    let s = v.to_string();
                    assert!(s.starts_with('?'));
                    Self::mk_var(s[1..].into())
                }
            })
            .collect();

        RecExpr::from(nodes)
    }

    fn score(
        lhs: &Pattern<Self>,
        rhs: &Pattern<Self>,
        cond: &Option<Assumption<Self>>,
        true_count: Option<usize>,
    ) -> [i32; 3] {
        fn sexp_to_cost(sexp: Sexp) -> i32 {
            match sexp {
                Sexp::Atom(a) => {
                    // if we can parse `a` into a number, then...
                    if a.parse::<i32>().is_ok() {
                        // slight penalty for constants
                        2
                    } else {
                        1
                    }
                }
                Sexp::List(l) => l.into_iter().map(sexp_to_cost).sum::<i32>(),
            }
        }

        let c_cost = if cond.is_some() {
            sexp_to_cost(Sexp::from_str(cond.clone().unwrap().to_string().as_str()).unwrap())
        } else {
            0
        };
        let l_cost = sexp_to_cost(Sexp::from_str(lhs.to_string().as_str()).unwrap());
        let r_cost = sexp_to_cost(Sexp::from_str(rhs.to_string().as_str()).unwrap());

        let mut vars: HashSet<Var> = Default::default();
        vars.extend(lhs.vars());
        vars.extend(rhs.vars());
        if let Some(cond) = cond {
            let cond_pat = cond.chop_assumption();
            vars.extend(cond_pat.vars());
        }

        let lhs_bigger = if AstSize.cost_rec(&lhs.ast) as i32 > AstSize.cost_rec(&rhs.ast) as i32 {
            1
        } else {
            0
        };

        [
            -(l_cost + r_cost + c_cost),
            (true_count.unwrap_or(i32::MAX as usize) as i32),
            lhs_bigger,
        ]
    }

    #[allow(dead_code)]
    fn score_original(
        lhs: &Pattern<Self>,
        rhs: &Pattern<Self>,
        cond: &Option<Pattern<Self>>,
    ) -> [i32; 5] {
        if let Some(cond) = cond {
            let c_size = AstSize.cost_rec(&cond.ast) as i32;
            let l_size = AstSize.cost_rec(&lhs.ast) as i32;
            let r_size = AstSize.cost_rec(&rhs.ast) as i32;
            let mut vars: HashSet<Var> = Default::default();
            vars.extend(lhs.vars());
            vars.extend(rhs.vars());
            vars.extend(cond.vars());

            let mut ops: HashSet<String> = Default::default();
            for node in lhs
                .ast
                .as_ref()
                .iter()
                .chain(rhs.ast.as_ref())
                .chain(cond.ast.as_ref())
            {
                if !node.is_leaf() {
                    ops.insert(node.to_string());
                }
            }

            let num_consts = lhs
                .ast
                .as_ref()
                .iter()
                .chain(rhs.ast.as_ref())
                .chain(cond.ast.as_ref())
                .filter(|n| match n {
                    ENodeOrVar::ENode(n) => n.is_constant(),
                    ENodeOrVar::Var(_) => false,
                })
                .count() as i32;

            [
                vars.len() as i32,
                -num_consts,
                -i32::max(l_size, -i32::max(r_size, c_size)),
                -(l_size + r_size + c_size),
                -(ops.len() as i32),
            ]
        } else {
            let l_size = AstSize.cost_rec(&lhs.ast) as i32;
            let r_size = AstSize.cost_rec(&rhs.ast) as i32;
            let mut vars: HashSet<Var> = Default::default();
            vars.extend(lhs.vars());
            vars.extend(rhs.vars());

            let mut ops: HashSet<String> = Default::default();
            for node in lhs.ast.as_ref().iter().chain(rhs.ast.as_ref()) {
                if !node.is_leaf() {
                    ops.insert(node.to_string());
                }
            }

            let num_consts = lhs
                .ast
                .as_ref()
                .iter()
                .chain(rhs.ast.as_ref())
                .filter(|n| match n {
                    ENodeOrVar::ENode(n) => n.is_constant(),
                    ENodeOrVar::Var(_) => false,
                })
                .count() as i32;

            [
                vars.len() as i32,
                -num_consts,
                -i32::max(l_size, r_size),
                -(l_size + r_size),
                -(ops.len() as i32),
            ]
        }
    }

    fn validate(lhs: &Pattern<Self>, rhs: &Pattern<Self>) -> ValidationResult;

    fn validate_implication(_implication: Implication<Self>) -> ImplicationValidationResult {
        // TODO: when we delete old ruler code, let's make this
        // a required method to implement.
        ImplicationValidationResult::Invalid
    }

    fn validate_with_cond(
        _lhs: &Pattern<Self>,
        _rhs: &Pattern<Self>,
        _cond: &Assumption<Self>,
    ) -> ValidationResult {
        ValidationResult::Valid
    }
}

#[cfg(test)]
pub mod implication_switch_tests {
    use super::*;
    use crate::halide::Pred;
    use conditions::merge_eqs;
    use egg::{EGraph, Runner};

    #[test]
    // in previous step, we have (IsTrue foo)
    // now let's see if we can add (IsTrue bar)
    // given foo implies bar.
    pub fn implication_toggle_one_step() {
        let implication: ImplicationSwitch<Pred> = ImplicationSwitch {
            parent_cond: "foo".parse().unwrap(),
            my_cond: "bar".parse().unwrap(),
        };

        let rewrite: Rewrite<Pred, SynthAnalysis> = implication.rewrite();

        let mut egraph: EGraph<Pred, SynthAnalysis> = Default::default();

        egraph.add_expr(&"(assume foo)".parse().unwrap());

        assert!(egraph
            .lookup_expr(&"(assume foo)".parse().unwrap())
            .is_some());

        assert!(egraph
            .lookup_expr(&"(assume bar)".parse().unwrap())
            .is_none());

        assert!(egraph
            .lookup_expr(&"(assume baz)".parse().unwrap())
            .is_none());

        let runner: Runner<Pred, SynthAnalysis> = Runner::new(SynthAnalysis::default())
            .with_egraph(egraph.clone())
            .run(&[rewrite]);

        let result = runner.egraph.clone();

        assert!(result
            .lookup_expr(&"(assume foo)".parse().unwrap())
            .is_some());

        assert!(result
            .lookup_expr(&"(assume bar)".parse().unwrap())
            .is_some());

        assert_ne!(
            result
                .lookup_expr(&"(assume bar)".parse().unwrap())
                .unwrap(),
            result
                .lookup_expr(&"(assume foo)".parse().unwrap())
                .unwrap()
        );
    }

    // foo ==> bar
    // bar ==> baz
    // assume foo. do we see assume bar and assume baz?
    #[test]
    pub fn implication_toggle_multi_step() {
        let foo_imp_bar = ImplicationSwitch {
            parent_cond: "foo".parse().unwrap(),
            my_cond: "bar".parse().unwrap(),
        }
        .rewrite();

        let bar_imp_baz = ImplicationSwitch {
            parent_cond: "bar".parse().unwrap(),
            my_cond: "baz".parse().unwrap(),
        }
        .rewrite();

        let mut egraph: EGraph<Pred, SynthAnalysis> = Default::default();

        egraph.add_expr(&"(assume foo)".parse().unwrap());

        assert!(egraph
            .lookup_expr(&"(assume foo)".parse().unwrap())
            .is_some());

        assert!(egraph
            .lookup_expr(&"(assume bar)".parse().unwrap())
            .is_none());

        assert!(egraph
            .lookup_expr(&"(assume baz)".parse().unwrap())
            .is_none());

        let runner: Runner<Pred, SynthAnalysis> = Runner::new(SynthAnalysis::default())
            .with_egraph(egraph.clone())
            .run(&[foo_imp_bar, bar_imp_baz]);

        let result = runner.egraph.clone();

        assert!(result
            .lookup_expr(&"(assume foo)".parse().unwrap())
            .is_some());

        assert!(result
            .lookup_expr(&"(assume bar)".parse().unwrap())
            .is_some());

        assert!(result
            .lookup_expr(&"(assume baz)".parse().unwrap())
            .is_some());
    }

    #[test]
    pub fn implication_no_toggle_simple() {
        let bar_imp_baz = ImplicationSwitch {
            parent_cond: "bar".parse().unwrap(),
            my_cond: "baz".parse().unwrap(),
        }
        .rewrite();

        let mut egraph: EGraph<Pred, SynthAnalysis> = Default::default();

        egraph.add_expr(&"(assume foo)".parse().unwrap());

        assert!(egraph
            .lookup_expr(&"(assume foo)".parse().unwrap())
            .is_some());

        assert!(egraph
            .lookup_expr(&"(assume bar)".parse().unwrap())
            .is_none());

        assert!(egraph
            .lookup_expr(&"(assume baz)".parse().unwrap())
            .is_none());

        let runner: Runner<Pred, SynthAnalysis> = Runner::new(SynthAnalysis::default())
            .with_egraph(egraph.clone())
            .run(&[bar_imp_baz]);

        let result = runner.egraph.clone();

        // nothing should have changed.
        assert!(result
            .lookup_expr(&"(assume foo)".parse().unwrap())
            .is_some());

        assert!(result
            .lookup_expr(&"(assume bar)".parse().unwrap())
            .is_none());

        assert!(result
            .lookup_expr(&"(assume baz)".parse().unwrap())
            .is_none());
    }

    #[test]
    // foo ==> bar
    // bar ==> baz
    // bar ==> qux
    pub fn implication_toggle_more_complex() {
        let foo_imp_bar = ImplicationSwitch {
            parent_cond: "foo".parse().unwrap(),
            my_cond: "bar".parse().unwrap(),
        }
        .rewrite();

        let bar_imp_baz = ImplicationSwitch {
            parent_cond: "bar".parse().unwrap(),
            my_cond: "baz".parse().unwrap(),
        }
        .rewrite();

        let baz_imp_qux = ImplicationSwitch {
            parent_cond: "baz".parse().unwrap(),
            my_cond: "qux".parse().unwrap(),
        }
        .rewrite();

        let mut egraph: EGraph<Pred, SynthAnalysis> = Default::default();

        egraph.add_expr(&"(assume foo)".parse().unwrap());

        assert!(egraph
            .lookup_expr(&"(assume foo)".parse().unwrap())
            .is_some());

        assert!(egraph
            .lookup_expr(&"(assume bar)".parse().unwrap())
            .is_none());

        assert!(egraph
            .lookup_expr(&"(assume baz)".parse().unwrap())
            .is_none());

        assert!(egraph
            .lookup_expr(&"(assume qux)".parse().unwrap())
            .is_none());

        let runner: Runner<Pred, SynthAnalysis> = Runner::new(SynthAnalysis::default())
            .with_egraph(egraph.clone())
            .run(&[foo_imp_bar, bar_imp_baz, baz_imp_qux]);

        let result = runner.egraph.clone();

        assert!(result
            .lookup_expr(&"(assume foo)".parse().unwrap())
            .is_some());

        assert!(result
            .lookup_expr(&"(assume bar)".parse().unwrap())
            .is_some());

        assert!(result
            .lookup_expr(&"(assume baz)".parse().unwrap())
            .is_some());

        assert!(result
            .lookup_expr(&"(assume qux)".parse().unwrap())
            .is_some());

        assert_ne!(
            result
                .lookup_expr(&"(assume bar)".parse().unwrap())
                .unwrap(),
            result
                .lookup_expr(&"(assume foo)".parse().unwrap())
                .unwrap()
        );

        assert_ne!(
            result
                .lookup_expr(&"(assume baz)".parse().unwrap())
                .unwrap(),
            result
                .lookup_expr(&"(assume bar)".parse().unwrap())
                .unwrap()
        );

        assert_ne!(
            result
                .lookup_expr(&"(assume qux)".parse().unwrap())
                .unwrap(),
            result
                .lookup_expr(&"(assume baz)".parse().unwrap())
                .unwrap()
        );
    }

    #[test]
    fn implication_toggle_equality_simple() {
        let rule: ImplicationSwitch<Pred> = ImplicationSwitch {
            parent_cond: "(!= ?x 0)".parse().unwrap(),
            my_cond: "(== (/ ?x ?x) 1)".parse().unwrap(),
        };

        let egraph = &mut EGraph::<Pred, SynthAnalysis>::default();

        egraph.add_expr(&"(assume (!= x 0))".parse().unwrap());

        let runner: Runner<Pred, SynthAnalysis> = Runner::new(SynthAnalysis::default())
            .with_egraph(egraph.clone())
            .run(&[rule.rewrite(), merge_eqs()]);

        let egraph = runner.egraph.clone();

        assert!(egraph
            .lookup_expr(&"(assume (== (/ x x) 1))".parse().unwrap())
            .is_some());

        assert_eq!(
            egraph.lookup_expr(&"(/ x x)".parse().unwrap()),
            egraph.lookup_expr(&"1".parse().unwrap())
        );
    }

    #[test]
    fn score_picks_higher_true_count() {
        let score1 = Pred::score(
            &"a".parse().unwrap(),
            &"(min a b)".parse().unwrap(),
            &Some(Assumption::new("(< a b)".to_string()).unwrap()),
            Some(10),
        );

        let score2 = Pred::score(
            &"a".parse().unwrap(),
            &"(min a b)".parse().unwrap(),
            &Some(Assumption::new("(<= a b)".to_string()).unwrap()),
            Some(20),
        );

        assert!(score1.cmp(&score2) == std::cmp::Ordering::Less);

        let mut rules: Ruleset<Pred> = Default::default();
        rules.add_cond_from_recexprs(
            &"a".parse().unwrap(),
            &"(min a b)".parse().unwrap(),
            &"(< a b)".parse().unwrap(),
            10,
        );

        rules.add_cond_from_recexprs(
            &"a".parse().unwrap(),
            &"(min a b)".parse().unwrap(),
            &"(<= a b)".parse().unwrap(),
            20,
        );

        let selected = rules.select(1, &mut Default::default());

        assert_eq!(selected.len(), 1);

        println!("selected: {selected:?}");
    }
}
