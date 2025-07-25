use conditions::assumption::Assumption;
use egg::{
    Analysis, Applier, AstSize, Condition, ConditionalApplier, ENodeOrVar, Extractor, Language,
    PatternAst, Rewrite, Searcher, Subst,
};
use std::fmt::{Debug, Formatter};
use std::str::FromStr;
use std::sync::Arc;

use crate::enumo::egg_to_serialized_egraph;
use crate::*;

/// A Rewrite rule
#[derive(Clone, Debug)]
pub struct Rule<L: SynthLanguage> {
    /// Readable name of the rewrite rule, formatted as lhs ==> rhs
    pub name: Arc<str>,
    /// The pattern to match on
    pub lhs: Pattern<L>,
    /// The pattern to merge
    pub rhs: Pattern<L>,
    /// The condition under which the rule is sound
    pub cond: Option<Assumption<L>>,
    /// egg::Rewrite
    pub rewrite: Rewrite<L, SynthAnalysis>,
    // The number of times the rule's condition is true, which you usually get via fuzzing.
    pub true_count: Option<usize>,
}

impl<L: SynthLanguage> Display for Rule<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self.cond {
            Some(cond) => {
                let cond_str = cond.to_string();
                assert!(cond_str.starts_with(format!("({}", L::assumption_label()).as_str()));
                // strip the assumption label from the start and the closing parenthesis from the end
                let cond = &cond_str
                    .strip_prefix(format!("({} ", L::assumption_label()).as_str())
                    .unwrap()
                    .strip_suffix(')')
                    .unwrap();
                write!(f, "{} ==> {} if {}", self.lhs, self.rhs, cond)
            }
            None => write!(f, "{} ==> {}", self.lhs, self.rhs),
        }
    }
}

impl<L: SynthLanguage> Rule<L> {
    pub fn from_string(s: &str) -> Result<(Self, Option<Self>), String> {
        let make_name =
            |lhs: &Pattern<L>, rhs: &Pattern<L>, cond: Option<Assumption<L>>| -> String {
                match cond {
                    None => format!("{lhs} ==> {rhs}"),
                    Some(cond) => format!("{lhs} ==> {rhs} if {cond}"),
                }
            };

        let (s, cond) = {
            if let Some((l, r)) = s.split_once(" if ") {
                let cond: Assumption<L> = Assumption::new(r.to_string()).unwrap();
                (l, Some(cond))
            } else {
                (s, None)
            }
        };
        if let Some((l, r)) = s.split_once("=>") {
            let l_pat: Pattern<L> = l.parse().unwrap();
            let r_pat: Pattern<L> = r.parse().unwrap();

            let name = make_name(&l_pat, &r_pat, cond.clone());

            let forwards = if cond.is_some() {
                Rule::new_cond(&l_pat, &r_pat, &cond.clone().unwrap(), None).unwrap()
            } else {
                Self {
                    name: name.clone().into(),
                    lhs: l_pat.clone(),
                    rhs: r_pat.clone(),
                    cond: cond.clone(),
                    rewrite: Rewrite::new(name.clone(), l_pat.clone(), Rhs { rhs: r_pat.clone() })
                        .unwrap(),
                    true_count: None,
                }
            };

            if s.contains("<=>") {
                let backwards_name = make_name(&r_pat, &l_pat, cond.clone());
                assert!(
                    cond.is_none(),
                    "Conditional bidirectional rules not supported."
                );
                let backwards = Self {
                    name: backwards_name.clone().into(),
                    lhs: r_pat.clone(),
                    rhs: l_pat.clone(),
                    cond: cond.clone(),
                    rewrite: Rewrite::new(Symbol::from(backwards_name), r_pat, Rhs { rhs: l_pat })
                        .unwrap(),
                    true_count: None,
                };
                Ok((forwards, Some(backwards)))
            } else {
                Ok((forwards, None))
            }
        } else {
            Err(format!("Failed to parse {s}"))
        }
    }
}

/// Default Applier for rewrite rules
struct Rhs<L: SynthLanguage> {
    rhs: Pattern<L>,
}

impl<L: SynthLanguage> Applier<L, SynthAnalysis> for Rhs<L> {
    fn vars(&self) -> Vec<Var> {
        self.rhs.vars()
    }

    fn apply_one(
        &self,
        egraph: &mut EGraph<L, SynthAnalysis>,
        matched_id: Id,
        subst: &Subst,
        _ast: Option<&PatternAst<L>>,
        sym: Symbol,
    ) -> Vec<Id> {
        if !egraph[matched_id].data.is_defined() {
            return vec![];
        }
        let first_expr = "(min c (max a b))";
        let second_expr = "c";

        let first = egraph.lookup_expr(&first_expr.parse().unwrap());
        let second = egraph.lookup_expr(&second_expr.parse().unwrap());

        let was_equal = match (first, second) {
            (Some(first), Some(second)) => egraph.find(first) == egraph.find(second),
            _ => false,
        };

        let id = apply_pat(self.rhs.ast.as_ref(), egraph, subst);
        if id == matched_id {
            return vec![];
        }

        if !egraph[id].data.is_defined() {
            return vec![];
        }

        egraph.union(id, matched_id);

        let first = egraph.lookup_expr(&first_expr.parse().unwrap());
        let second = egraph.lookup_expr(&second_expr.parse().unwrap());

        // match (first, second) {
        //     (Some(first), Some(second)) => {
        //         if !was_equal && egraph.find(first) == egraph.find(second) {
        //             egraph.rebuild();
        //             // what assumptions are true in the e-graph?
        //             let assumption_searcher: Pattern<L> =
        //                 format!("({} ?c)", L::assumption_label()).parse().unwrap();

        //             let mut eg = egraph.clone();
        //             let mut extract: Extractor<AstSize, L, SynthAnalysis> =
        //                 Extractor::new(&eg, AstSize);
        //             let matched_term = extract.find_best(matched_id).1;

        //             println!("matched on {}", matched_term);

        //             let matches = assumption_searcher.search_with_limit(&eg, 20);

        //             for m in matches {
        //                 let best = extract.find_best(m.eclass).1;
        //                 println!("assumption: {best}");
        //             }

        //             let first_thing = extract.find_best(id).1;
        //             let second_thing = extract.find_best(matched_id).1;

        //             for v in &["a", "b", "c"] {
        //                 let var = Var::from_str(format!("?{v}").as_str()).unwrap();
        //                 if let Some(arg_id) = subst.get(var) {
        //                     let arg = extract.find_best(*arg_id).1;
        //                     println!("{v}: {arg}");
        //                 }
        //             }

        //             println!("my pattern: {}", self.rhs);
        //             println!("my size: {}", egraph.total_number_of_nodes());

        //             println!("the rules i've gotten so far:");

        //             // let serialized = egg_to_serialized_egraph(egraph);
        //             // serialized
        //             //     .to_json_file("dump.json")
        //             //     .expect("Failed to write egraph to file");
        //             println!("I unioned {} and {}.", first_thing, second_thing);
        //             println!("the ast for the _ast: {_ast:?}");
        //             println!("the subst: {subst:?}");

        //             println!("I applied {sym}.");
        //             // let proof = egraph.explain_equivalence(
        //             //     &first_expr.parse().unwrap(),
        //             //     &second_expr.parse().unwrap(),
        //             // );
        //             // println!("the proof: {proof}");
        //             panic!("found it.");
        //         }
        //     }
        //     _ => {}
        // }
        vec![id]
    }
}

pub struct ConditionChecker<L: SynthLanguage> {
    cond: Pattern<L>,
}

// thank you Cole.
pub fn lookup_pattern<L, N>(pattern: &Pattern<L>, egraph: &EGraph<L, N>, subst: &Subst) -> bool
where
    L: Language,
    N: Analysis<L>,
{
    let mut ids: Vec<Option<Id>> = vec![None; pattern.ast.as_ref().len()];
    for (i, enode_or_var) in pattern.ast.as_ref().iter().enumerate() {
        match enode_or_var {
            ENodeOrVar::Var(v) => {
                ids[i] = subst.get(*v).copied();
            }
            ENodeOrVar::ENode(e) => {
                let mut resolved_enode: L = e.clone();
                for child in resolved_enode.children_mut() {
                    match ids[usize::from(*child)] {
                        None => {
                            return false;
                        }
                        Some(id) => {
                            *child = id;
                        }
                    }
                }
                match egraph.lookup(resolved_enode) {
                    None => {
                        return false;
                    }
                    Some(id) => {
                        ids[i] = Some(id);
                    }
                }
            }
        }
    }
    true
}

impl<L: SynthLanguage> Condition<L, SynthAnalysis> for ConditionChecker<L> {
    fn check(
        &self,
        egraph: &mut egg::EGraph<L, SynthAnalysis>,
        _eclass: egg::Id,
        subst: &Subst,
    ) -> bool {
        // let is_true_pat: Pattern<L> = format!("(assume {})", self.cond).parse().unwrap();
        lookup_pattern(&self.cond, egraph, subst)
    }
}

impl<L: SynthLanguage> Rule<L> {
    pub fn new_cond(
        l_pat: &Pattern<L>,
        r_pat: &Pattern<L>,
        cond: &Assumption<L>,
        true_count: Option<usize>,
    ) -> Option<Self> {
        let cond_pat: Pattern<L> = cond.clone().into();
        let cond_display = cond.chop_assumption();

        let name = format!("{l_pat} ==> {r_pat} if {cond_display}");

        let cond_vars = cond_pat.vars();
        let l_vars = l_pat.vars();

        if cond_vars.iter().any(|v| !l_vars.contains(v)) {
            return None; // Condition variables must be a subset of the left-hand side variables
        }

        let rewrite = Rewrite::new(
            name.clone(),
            l_pat.clone(),
            ConditionalApplier {
                condition: ConditionChecker {
                    cond: cond_pat.clone(),
                },
                applier: r_pat.clone(),
            },
        )
        .ok();

        rewrite.map(|rw| Rule {
            name: name.into(),
            lhs: l_pat.clone(),
            rhs: r_pat.clone(),
            cond: Some(cond.clone()),
            rewrite: rw,
            true_count,
        })
    }

    pub fn new(l_pat: &Pattern<L>, r_pat: &Pattern<L>) -> Option<Self> {
        let name = format!("{l_pat} ==> {r_pat}");
        let rhs = Rhs { rhs: r_pat.clone() };
        let rewrite = Rewrite::new(name.clone(), l_pat.clone(), rhs).ok();

        rewrite.map(|rw| Rule {
            name: name.into(),
            lhs: l_pat.clone(),
            rhs: r_pat.clone(),
            cond: None,
            rewrite: rw,
            true_count: None,
        })
    }

    /// A rule is saturating if applying it is guaranteed not to add any
    /// e-classes to the e-graph.
    pub fn is_saturating(&self) -> bool {
        let mut egraph: EGraph<L, SynthAnalysis> = Default::default();
        let l_id = egraph.add_expr(&L::instantiate(&self.lhs));
        let initial_size = egraph.number_of_classes();

        let r_id = egraph.add_expr(&L::instantiate(&self.rhs));

        egraph.union(l_id, r_id);
        egraph.rebuild();
        let final_size = egraph.number_of_classes();

        initial_size >= final_size
    }

    pub fn score(&self) -> impl Ord + Debug {
        L::score(&self.lhs, &self.rhs, &self.cond, self.true_count)
    }

    /// Whether the rule is sound
    pub fn is_valid(&self) -> bool {
        if self.cond.is_some() {
            matches!(
                L::validate_with_cond(&self.lhs, &self.rhs, &self.cond.clone().unwrap()),
                ValidationResult::Valid
            )
        } else {
            matches!(L::validate(&self.lhs, &self.rhs), ValidationResult::Valid)
        }
    }
}

fn apply_pat<L: Language, A: Analysis<L>>(
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

#[cfg(test)]
mod test {
    use egg::{EGraph, Runner};

    use crate::enumo::{Rule, Ruleset};

    use crate::language::SynthAnalysis;

    use super::halide::Pred;
    use super::ImplicationSwitch;

    #[test]
    fn parse() {
        // Unidirectional rule with => delimeter
        let (forwards, backwards) = Rule::<Pred>::from_string("(* a b) => (* c d)")
            .ok()
            .unwrap();
        assert!(backwards.is_none());
        assert_eq!(forwards.name.to_string(), "(* a b) ==> (* c d)");
        assert_eq!(forwards.cond, None);

        // Unidirectional rule with ==> delimeter
        let (forwards, backwards) = Rule::<Pred>::from_string("(* a b) ==> (* c d)")
            .ok()
            .unwrap();
        assert!(backwards.is_none());
        assert_eq!(forwards.name.to_string(), "(* a b) ==> (* c d)");
        assert_eq!(forwards.cond, None);

        // Bidirectional rule <=>
        let (forwards, backwards) = Rule::<Pred>::from_string("(* a b) <=> (* c d)")
            .ok()
            .unwrap();
        assert!(backwards.is_some());
        let bk = backwards.unwrap();
        assert_eq!(bk.name.to_string(), "(* c d) ==> (* a b)");
        assert_eq!(bk.cond, None);
        assert_eq!(forwards.name.to_string(), "(* a b) ==> (* c d)");
        assert_eq!(forwards.cond, None);

        // Conditional rules:
        let (forwards, backwards) = Rule::<Pred>::from_string("(* a b) ==> (* c d) if (< e f)")
            .ok()
            .unwrap();
        assert!(backwards.is_none());
        assert_eq!(forwards.name.to_string(), "(* a b) ==> (* c d) if (< e f)");
        assert!(forwards.cond.is_some());
        assert_eq!(
            forwards.cond.unwrap().chop_assumption().to_string(),
            "(< e f)"
        );
    }

    #[test]
    fn cond_rewrite_fires() {
        let rule: Rule<Pred> = Rule::from_string("(/ ?x ?x) ==> 1 if (!= ?x 0)").unwrap().0;
        let mut ruleset = Ruleset::default();
        ruleset.add(rule.clone());

        let mut egraph: EGraph<Pred, SynthAnalysis> = Default::default();
        egraph.add_expr(&"(/ x x)".parse().unwrap());
        egraph.add_expr(&"1".parse().unwrap());

        egraph.add_expr(&"(assume (!= x 0))".parse().unwrap());

        let runner: Runner<Pred, SynthAnalysis> = Runner::new(SynthAnalysis::default())
            .with_egraph(egraph)
            .run(&[rule.rewrite]);

        let result = runner.egraph;

        assert_eq!(
            result.lookup_expr(&"1".parse().unwrap()),
            result.lookup_expr(&"(/ x x)".parse().unwrap())
        );
    }

    #[test]
    fn cond_rewrite_does_not_fire() {
        let rule: Rule<Pred> = Rule::from_string("(/ x x) ==> 1 if (!= x 0)").unwrap().0;
        let mut ruleset = Ruleset::default();
        ruleset.add(rule.clone());

        let mut egraph: EGraph<Pred, SynthAnalysis> = Default::default();
        egraph.add_expr(&"(/ x x)".parse().unwrap());
        egraph.add_expr(&"1".parse().unwrap());

        egraph.add_expr(&"(assume (== x 0))".parse().unwrap());

        let runner: Runner<Pred, SynthAnalysis> = Runner::new(SynthAnalysis::default())
            .with_egraph(egraph)
            .run(&[rule.rewrite]);

        let result = runner.egraph;

        assert_ne!(
            result.lookup_expr(&"1".parse().unwrap()),
            result.lookup_expr(&"(/ x x)".parse().unwrap())
        );
    }

    // kind of an end-to-end-ish test.
    // 1. add the following implication rules:
    //    x > 5 implies x > 0
    //    x > 0 implies x != 0
    // 2. add the following conditional rule:
    // (/ x x) ==> 1 if (!= x 0)
    // 3. see if (/ a a) rewrites to 1
    #[test]
    fn cond_rewrite_fires_eventually() {
        let rule: Rule<Pred> = Rule::from_string("(/ ?x ?x) ==> 1 if (!= ?x 0)").unwrap().0;
        let mut ruleset = Ruleset::default();
        ruleset.add(rule.clone());

        let x_gt_5_imp_x_gt_0 =
            ImplicationSwitch::new(&"(> x 5)".parse().unwrap(), &"(> x 0)".parse().unwrap())
                .rewrite();

        let x_gt_0_imp_x_not_0 =
            ImplicationSwitch::new(&"(> x 0)".parse().unwrap(), &"(!= x 0)".parse().unwrap())
                .rewrite();

        let mut egraph: EGraph<Pred, SynthAnalysis> = Default::default();

        egraph.add_expr(&"(assume (> x 5))".parse().unwrap());

        let runner: Runner<Pred, SynthAnalysis> = Runner::new(SynthAnalysis::default())
            .with_egraph(egraph.clone())
            .run(&[x_gt_5_imp_x_gt_0, x_gt_0_imp_x_not_0]);

        let mut result = runner.egraph.clone();
        assert!(result
            .lookup_expr(&"(assume (!= x 0))".parse().unwrap())
            .is_some());

        result.add_expr(&"(/ x x)".parse().unwrap());
        result.add_expr(&"(/ y y)".parse().unwrap());

        let runner: Runner<Pred, SynthAnalysis> = Runner::new(SynthAnalysis::default())
            .with_egraph(result)
            .run(&[rule.rewrite]);

        let result = runner.egraph;

        assert_eq!(
            result.lookup_expr(&"1".parse().unwrap()).unwrap(),
            result.lookup_expr(&"(/ x x)".parse().unwrap()).unwrap()
        );

        assert_ne!(
            result.lookup_expr(&"1".parse().unwrap()).unwrap(),
            result.lookup_expr(&"(/ y y)".parse().unwrap()).unwrap()
        )
    }
}
