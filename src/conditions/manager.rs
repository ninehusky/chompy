use crate::{
    conditions::{
        assumption::Assumption, implication::Implication, implication_set::ImplicationSet,
    },
    enumo::{Rule, Ruleset},
    SynthLanguage,
};

use egg::{Pattern, RecExpr};
use egglog::EGraph as EgglogEGraph;

const IMPL_RULESET_NAME: &str = "path-finding";
const RW_RULESET_NAME: &str = "rewrites";

/// This provides an interface for managing the implication egraph.
pub(crate) struct EGraphManager<L: SynthLanguage> {
    pub(crate) egraph: EgglogEGraph,
    _marker: std::marker::PhantomData<L>,
}

impl<L: SynthLanguage> EGraphManager<L> {
    pub fn new() -> Self {
        let egraph = EgglogEGraph::default();
        let mut manager = Self {
            egraph,
            _marker: std::marker::PhantomData,
        };
        manager.init_egraph();
        manager
    }

    /// Initialize the egraph with the language and path relations.
    // Dev note: do we need `and` and `or`? Can we synthesize
    // these by hand? Let's write a test to figure it out.
    fn init_egraph(&mut self) {
        // Initialize the egraph with the language.
        let name = L::name();

        self.egraph
            .parse_and_run_program(None, &L::egglog_lang_def())
            .unwrap();

        self.egraph
            .parse_and_run_program(
                None,
                &format!(
                    r#"

            (ruleset {IMPL_RULESET_NAME})
            (ruleset {RW_RULESET_NAME})

            ;;; Define path relations
            (relation edge ({name} {name}))
            (relation path ({name} {name}))

            ;;; Base case for path finding
            (rule
                ((edge ?l ?r))
                ((path ?l ?r))
                :ruleset {IMPL_RULESET_NAME})
            
            ;;; The inductive case for path finding.
            (rule
                ((path ?l ?x)
                 (edge ?x ?r))
                ((path ?l ?r))
                :ruleset {IMPL_RULESET_NAME})
        "#,
                ),
            )
            .unwrap();
    }

    /// Adds the given implications to the e-graph.
    pub fn add_implications(&mut self, implications: &ImplicationSet<L>) -> Result<(), String> {
        for imp in implications.iter() {
            self.add_implication(imp)?
        }
        Ok(())
    }

    /// Adds the given assumption to the e-graph. Errors if the assumption is symbolic.
    pub fn add_assumption(&mut self, assumption: Assumption<L>) -> Result<(), String> {
        let term = assumption.chop_assumption();
        if !is_concrete(&term.clone()) {
            return Err(format!(
                "Assumption must be generalized (no concrete variables): {term}",
            ));
        }

        let term_str = L::to_egglog_term(term.clone());

        match self.egraph.parse_and_run_program(None, &term_str) {
            Ok(_) => Ok(()),
            Err(e) => Err(format!("Failed to add term {term}: {e}")),
        }
    }

    /// Adds the given rewrites to the e-graph.
    pub fn add_rewrites(&mut self, rws: &Ruleset<L>) -> Result<(), String> {
        for rw in rws.iter() {
            if rw.cond.is_some() {
                // skip rules with conditions for now.
                continue;
            }
            match self.add_rewrite(rw) {
                Ok(_) => continue,
                Err(e) => {
                    if e.to_string()
                        .contains("No support for rewriting on anything")
                    {
                        // this is a special case where the rule is just a variable, so we skip it.
                        continue;
                    } else {
                        return Err(e);
                    }
                }
            }
        }
        Ok(())
    }

    /// Adds the given rewrite to the e-graph.
    pub fn add_rewrite(&mut self, rw: &Rule<L>) -> Result<(), String> {
        if rw.lhs.ast.as_ref().len() == 1
            && matches!(rw.lhs.ast.as_ref()[0], egg::ENodeOrVar::Var(_))
        {
            return Err(format!(
                "No support for rewriting on anything: {:?}",
                rw.lhs
            ));
        }
        // the rule's pattern better be generalized!
        let lhs = L::to_egglog_term(rw.lhs.clone());
        let rhs = L::to_egglog_term(rw.rhs.clone());
        let rw_name = rw.name.to_string();
        let rw_prog = format!(
            r#"
        (rewrite
            {}
            {}
            :ruleset {})
        "#,
            lhs, rhs, RW_RULESET_NAME
        );
        match self.egraph.parse_and_run_program(None, &rw_prog) {
            Ok(_) => Ok(()),
            Err(e) => Err(format!("Failed to add rewrite: {rw_name} :{e}")),
        }
    }

    /// Adds the given implication to the e-graph.
    /// Errors if the implication is not generalized.
    pub fn add_implication(&mut self, imp: &Implication<L>) -> Result<(), String> {
        if !is_generalized(&imp.lhs().clone().into()) {
            return Err(format!(
                "Implication LHS must be generalized (no concrete variables): {}",
                imp.lhs()
            ));
        }
        if !is_generalized(&imp.rhs().clone().into()) {
            return Err(format!(
                "Implication RHS must be generalized (no concrete variables): {}",
                imp.rhs()
            ));
        }
        let rule_def = Self::impl_to_egglog_rule(imp)?;

        match self.egraph.parse_and_run_program(None, &rule_def) {
            Ok(_) => Ok(()),
            Err(e) => Err(format!("Failed to add implication: {e}")),
        }
    }

    /// The assumption should be concrete.
    pub fn check_path(&mut self, from: &Assumption<L>, to: &Assumption<L>) -> Result<bool, String> {
        if !is_concrete(&from.clone().into()) {
            return Err(format!(
                "Assumption must be concrete (no symbolic variables): {}",
                from
            ));
        }

        if !is_concrete(&to.clone().into()) {
            return Err(format!(
                "Assumption must be concrete (no symbolic variables): {}",
                to
            ));
        }

        let lhs = L::to_egglog_term(from.clone().chop_assumption());
        let rhs = L::to_egglog_term(to.clone().chop_assumption());
        let query = format!("(check (path {lhs} {rhs}))");
        match self.egraph.parse_and_run_program(None, &query) {
            Ok(_) => Ok(true),
            Err(e) => {
                assert!(e.to_string().contains("Check failed"));
                Ok(false)
            }
        }
    }

    /// Converts an implication to an egglog rule.
    /// Implications should **never** add new predicates to the egraph; it should only
    /// link together existing ones.
    fn impl_to_egglog_rule(imp: &Implication<L>) -> Result<String, String> {
        let lhs = imp.lhs().clone();
        let rhs = imp.rhs().clone();

        if !is_generalized(&lhs.clone().into()) {
            return Err(format!(
                "Implication LHS must be generalized (no concrete variables): {lhs}"
            ));
        }
        if !is_generalized(&rhs.clone().into()) {
            return Err(format!(
                "Implication RHS must be generalized (no concrete variables): {rhs}"
            ));
        }

        let lhs_recexpr: RecExpr<L> = L::instantiate(&imp.lhs().clone().chop_assumption());
        let rhs_recexpr: RecExpr<L> = L::instantiate(&imp.rhs().clone().chop_assumption());

        let mut map = Default::default();

        let lhs = L::to_egglog_term(L::generalize(&lhs_recexpr, &mut map));
        let rhs = L::to_egglog_term(L::generalize(&rhs_recexpr, &mut map));
        // sanity check: there should be no concrete variables in the lhs or rhs.
        // if you're able to match on lhs, rhs, draw an edge between them.
        let rs_name = IMPL_RULESET_NAME;
        Ok(format!(
            r#"
        (rule
            ({lhs}
             {rhs})
            ((edge {lhs} {rhs}))
            :ruleset {rs_name})
        "#,
        ))
    }

    /// Runs implications on the e-graph.
    pub fn run_implication_rules(&mut self) {
        self.run_egglog_rules(IMPL_RULESET_NAME);
    }

    /// Runs rewrites on the egraph.
    pub fn run_rewrite_rules(&mut self) {
        self.run_egglog_rules(RW_RULESET_NAME);
    }

    // Runs rules till saturation.
    // Can probably make a `Schedule` or something but seems like overkill
    // for now.
    fn run_egglog_rules(&mut self, ruleset_name: &'static str) {
        self.egraph
            .parse_and_run_program(
                None,
                &format!(r#"(run-schedule (saturate {}))"#, ruleset_name),
            )
            .unwrap_or_else(|e| {
                panic!(
                    "Something terrible happened while running egglog rules: {}",
                    e
                );
            });
    }
}

// Returns true if the term is generalized (i.e., contains no concrete variables).
fn is_generalized<L: SynthLanguage>(pat: &Pattern<L>) -> bool {
    pat.ast.as_ref().iter().all(|node| match node {
        egg::ENodeOrVar::ENode(e) => !L::is_var(e),
        egg::ENodeOrVar::Var(_) => true,
    })
}

// Returns true if the term is concrete (i.e., contains no metavariables).
fn is_concrete<L: SynthLanguage>(pat: &Pattern<L>) -> bool {
    pat.ast
        .as_ref()
        .iter()
        .all(|node| matches!(node, egg::ENodeOrVar::ENode(_)))
}

#[cfg(test)]
mod concrete_generalized_tests {
    #[allow(unused_imports)]
    use crate::halide::Pred;
    use egg::Pattern;

    #[test]
    fn test_is_generalized() {
        let pat: Pattern<Pred> = "(== ?x ?y)".parse().unwrap();
        assert!(super::is_generalized(&pat));

        let pat: Pattern<Pred> = "(== x ?y)".parse().unwrap();
        assert!(!super::is_generalized(&pat));

        let pat: Pattern<Pred> = "(== ?x y)".parse().unwrap();
        assert!(!super::is_generalized(&pat));

        let pat: Pattern<Pred> = "(== x y)".parse().unwrap();
        assert!(!super::is_generalized(&pat));
    }

    #[test]
    fn test_is_concrete() {
        let pat: Pattern<Pred> = "(== x y)".parse().unwrap();
        assert!(super::is_concrete(&pat));

        let pat: Pattern<Pred> = "(== ?x y)".parse().unwrap();
        assert!(!super::is_concrete(&pat));

        let pat: Pattern<Pred> = "(== x ?y)".parse().unwrap();
        assert!(!super::is_concrete(&pat));

        let pat: Pattern<Pred> = "(== ?x ?y)".parse().unwrap();
        assert!(!super::is_concrete(&pat));
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        conditions::{assumption::Assumption, implication::Implication, manager::EGraphManager},
        enumo::Rule,
        halide::Pred,
        SynthLanguage,
    };

    fn check_equal<L: SynthLanguage>(
        manager: &mut EGraphManager<L>,
        lhs: &Assumption<L>,
        rhs: &Assumption<L>,
    ) -> bool {
        manager
            .egraph
            .parse_and_run_program(
                None,
                &format!(
                    "(check (= {} {}))",
                    L::to_egglog_term(lhs.chop_assumption()),
                    L::to_egglog_term(rhs.chop_assumption())
                ),
            )
            .is_ok()
    }

    #[test]
    fn egraph_construction_doesnt_blow_up() {
        let _manager: EGraphManager<Pred> = EGraphManager::new();
    }

    // i was gonna make a test to make sure it errs when you pass in a bad term,
    // but assumptions won't even let you construct terms which are not valid
    // predicates in the language.
    #[test]
    fn add_term_ok() {
        let mut manager: EGraphManager<Pred> = EGraphManager::new();
        let assumption: Assumption<Pred> = Assumption::new("(== x y)".to_string()).unwrap();
        manager.add_assumption(assumption).unwrap();
    }

    #[test]
    fn add_rw_ok() {
        let rule: Rule<Pred> = Rule::from_string("(== ?x ?y) ==> (== ?y ?x)").unwrap().0;
        let mut manager: EGraphManager<Pred> = EGraphManager::new();

        manager.add_rewrite(&rule).unwrap();
        manager.add_assumption("(== a b)".parse().unwrap()).unwrap();

        manager.run_rewrite_rules();

        let lhs: Assumption<Pred> = "(== a b)".parse().unwrap();
        let rhs: Assumption<Pred> = "(== b a)".parse().unwrap();
        assert!(check_equal(&mut manager, &lhs, &rhs));
    }

    #[test]
    fn check_equal_fails_when_neq() {
        let rule: Rule<Pred> = Rule::from_string("(== ?x ?y) ==> (== ?y ?x)").unwrap().0;
        let mut manager: EGraphManager<Pred> = EGraphManager::new();

        manager.add_rewrite(&rule).unwrap();
        manager.add_assumption("(== a b)".parse().unwrap()).unwrap();
        manager.add_assumption("(== b c)".parse().unwrap()).unwrap();

        manager.run_rewrite_rules();

        let lhs: Assumption<Pred> = "(== a b)".parse().unwrap();
        let rhs: Assumption<Pred> = "(== b c)".parse().unwrap();
        assert!(!check_equal(&mut manager, &lhs, &rhs));
    }

    #[test]
    fn add_impl_ok_true() {
        let imp: Implication<Pred> = Implication::new(
            "my-imp".into(),
            "(< ?x 0)".parse().unwrap(),
            "(< ?x 1)".parse().unwrap(),
        )
        .unwrap();
        let mut manager: EGraphManager<Pred> = EGraphManager::new();
        manager.add_implication(&imp).unwrap();
        manager.add_assumption("(< a 0)".parse().unwrap()).unwrap();
        manager.add_assumption("(< a 1)".parse().unwrap()).unwrap();
        manager.run_implication_rules();

        let lhs: Assumption<Pred> = "(< a 0)".parse().unwrap();
        let rhs: Assumption<Pred> = "(< a 1)".parse().unwrap();
        assert!(manager.check_path(&lhs, &rhs).unwrap());
    }

    #[test]
    fn add_impl_ok_false() {
        let imp: Implication<Pred> = Implication::new(
            "my-imp".into(),
            "(< ?x 0)".parse().unwrap(),
            "(< ?x 1)".parse().unwrap(),
        )
        .unwrap();
        let mut manager: EGraphManager<Pred> = EGraphManager::new();
        manager.add_implication(&imp).unwrap();
        manager.add_assumption("(< a 0)".parse().unwrap()).unwrap();
        manager.add_assumption("(< a 2)".parse().unwrap()).unwrap();
        manager.run_implication_rules();

        let lhs: Assumption<Pred> = "(< a 0)".parse().unwrap();
        let rhs: Assumption<Pred> = "(< a 1)".parse().unwrap();
        assert!(!manager.check_path(&lhs, &rhs).unwrap());
    }

    #[test]
    fn add_concrete_implication_fails() {
        let imp: Implication<Pred> = Implication::new(
            "my-imp".into(),
            "(< x 0)".parse().unwrap(),
            "(< x 1)".parse().unwrap(),
        )
        .unwrap();
        let mut manager: EGraphManager<Pred> = EGraphManager::new();
        assert!(manager.add_implication(&imp).is_err());
    }

    #[test]
    fn add_general_assumption_fails() {
        let mut manager: EGraphManager<Pred> = EGraphManager::new();
        let assumption: Assumption<Pred> = Assumption::new("(== ?x ?y)".to_string()).unwrap();
        assert!(manager.add_assumption(assumption).is_err());
    }
}
