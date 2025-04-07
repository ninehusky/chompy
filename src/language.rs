use std::{
    fmt::{Debug, Display},
    hash::Hash,
};

use egg::{
    Analysis, Applier, AstSize, CostFunction, DidMerge, ENodeOrVar, FromOp, Language, PatternAst,
    RecExpr, Rewrite,
};
use enumo::{Rule, Workload};

use crate::*;

// An `ImplicationSwitch` models the implication of one condition to another.
//
// For example, given conditions `c`, `c'`, if that `c` implies `c'`,
// then an `ImplicationSwitch` will model the implication `c => c'`.
// In practice, the user is responsible for setting up the fact that `c` is true
// in the e-graph through adding the term `(IsTrue c)`.
//
// When the corresponding `ImplicationSwitch` is run (i.e., when it's run as a rule),
// then it will add `(IsTrue c')` to the e-graph, paving the way for conditional rewrite
// rules. See `ConditionalRewrite` for more details.
pub struct ImplicationSwitch<L: SynthLanguage> {
    parent_cond: Pattern<L>,
    my_cond: Pattern<L>,
}

struct ImplicationApplier<L: SynthLanguage> {
    parent_cond: Pattern<L>,
    my_cond: Pattern<L>,
}

impl<L> Applier<L, SynthAnalysis> for ImplicationApplier<L>
where
    L: SynthLanguage,
{
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<L, SynthAnalysis>,
        _eclass: egg::Id,
        _subst: &egg::Subst,
        _searcher_ast: Option<&PatternAst<L>>,
        _rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        // it better be the case that the parent condition exists in the e-graph.
        if egraph
            .lookup_expr(
                &format!("(IsTrue {})", self.parent_cond.to_string())
                    .parse()
                    .unwrap(),
            )
            .is_none()
        {
            panic!("Parent condition not found in egraph");
        }

        let new_id = egraph.add_expr(
            &format!("(IsTrue {})", self.my_cond.to_string())
                .parse()
                .unwrap(),
        );
        // may need to return just vec![] in some cases if there was no need
        // to fire the rule?
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
        let searcher: Pattern<L> = format!("(IsTrue {})", self.parent_cond.to_string())
            .parse()
            .unwrap();

        Rewrite::new(
            format!("{} implies {}", self.parent_cond, self.my_cond),
            searcher,
            self.my_cond.clone(),
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
                    (Some(_), None) => {
                        merge_b = true;
                    }
                    (Some(x), Some(y)) => assert_eq!(x, y, "cvecs do not match!!"),
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
/// Value type in the domain.
pub type Constant<L> = <L as SynthLanguage>::Constant;

/// Trait for defining a language for which to synthesize rewrites.
pub trait SynthLanguage: Language + Send + Sync + Display + FromOp + 'static {
    /// Domain value type
    type Constant: Clone + Hash + Eq + Debug + Display + Ord;

    /// Converts a constant to a boolean.
    /// Returns None when the conversion is not defined for the constant.
    fn constant_to_bool(_c: &Self::Constant) -> Option<bool> {
        None
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
            Some(var) => ENodeOrVar::Var(format!("?{}", var).parse().unwrap()),
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

    fn get_condition_propogation_rules(conditions: &Workload) -> Ruleset<Self> {
        let forced = conditions.force();
        let mut result = Ruleset::default();
        let mut cache: HashMap<(String, String), bool> = Default::default();
        let true_recexpr: RecExpr<Self> = "TRUE".parse().unwrap();
        for c in &forced {
            let c_recexpr: RecExpr<Self> = c.to_string().parse().unwrap();
            let c_pat = Pattern::from(&c_recexpr.clone());
            for c2 in &forced {
                let c2_recexpr: RecExpr<Self> = c2.to_string().parse().unwrap();
                let c2_pat = Pattern::from(&c2_recexpr.clone());
                if Self::condition_implies(
                    &c.to_string().parse().unwrap(),
                    &c2.to_string().parse().unwrap(),
                    &mut cache,
                ) {
                    // c => c2
                    let rw_name = format!("{} => {} if {} == true", c, c2, c);
                    let rw: Rewrite<Self, SynthAnalysis> = Rewrite::new(
                        rw_name.clone(),
                        Pattern::from(&true_recexpr.clone()),
                        c2_pat.clone(),
                    )
                    .unwrap();
                    let rule: Rule<Self> = Rule {
                        name: rw_name.into(),
                        lhs: Pattern::from(&true_recexpr.clone()),
                        rhs: c2_pat.clone(),
                        // if cond1 is true, then cond1 -> cond2.
                        cond: Some(c_pat.clone()),
                        rewrite: rw,
                    };
                    let mut dummy = Ruleset::default();
                    dummy.add(rule);
                    result = result.union(&dummy);
                }
            }
        }
        result
    }

    fn condition_implies(
        _lhs: &Pattern<Self>,
        _rhs: &Pattern<Self>,
        _cache: &mut HashMap<(String, String), bool>,
    ) -> bool {
        false
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

    fn score(lhs: &Pattern<Self>, rhs: &Pattern<Self>, cond: &Option<Pattern<Self>>) -> i32 {
        let c_size = if cond.is_some() {
            AstSize.cost_rec(&cond.clone().unwrap().ast) as i32
        } else {
            0
        };
        let l_size = AstSize.cost_rec(&lhs.ast) as i32;
        let r_size = AstSize.cost_rec(&rhs.ast) as i32;

        -(l_size + r_size + c_size)
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

    fn validate_with_cond(
        _lhs: &Pattern<Self>,
        _rhs: &Pattern<Self>,
        _cond: &Pattern<Self>,
    ) -> ValidationResult {
        ValidationResult::Valid
    }
}
