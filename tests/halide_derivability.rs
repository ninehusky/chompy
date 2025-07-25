use ruler::{
    conditions::{
        assumption::Assumption, implication::Implication, implication_set::ImplicationSet,
    },
    enumo::{build_pvec_to_patterns, Rule, Ruleset, Workload},
    halide::Pred,
    Limits, SynthLanguage,
};

struct DerivabilityResult<L: SynthLanguage> {
    can: Ruleset<L>,
    cannot: Ruleset<L>,
}

const CAVIAR_RULES: &str = r#"
(== ?x ?y) ==> (== ?y ?x)
(== ?x ?y) ==> (== (- ?x ?y) 0)
(== (+ ?x ?y) ?z) ==> (== ?x (- ?z ?y))
(== ?x ?x) ==> 1
(== (* ?x ?y) 0) ==> (|| (== ?x 0) (== ?y 0))
( == (max ?x ?y) ?y) ==> (<= ?x ?y)
( == (min ?x ?y) ?y) ==> (<= ?y ?x)
(<= ?y ?x) ==> ( == (min ?x ?y) ?y)
(== (* ?a ?x) ?b) ==> 0 if (&& (!= ?a 0) (!= (% ?b ?a) 0))
(== (max ?x ?c) 0) ==> 0 if (> ?c 0)
(== (max ?x ?c) 0) ==> (== ?x 0) if (< ?c 0)
(== (min ?x ?c) 0) ==> 0 if (< ?c 0)
(== (min ?x ?c) 0) ==> (== ?x 0) if (> ?c 0)
(|| ?x ?y) ==> (! (&& (! ?x) (! ?y)))
(|| ?y ?x) ==> (|| ?x ?y)
(+ ?a ?b) ==> (+ ?b ?a)
(+ ?a (+ ?b ?c)) ==> (+ (+ ?a ?b) ?c)
(+ ?a 0) ==> ?a
(* ?a (+ ?b ?c)) ==> (+ (* ?a ?b) (* ?a ?c))
(+ (* ?a ?b) (* ?a ?c)) ==> (* ?a (+ ?b ?c))
(+ (/ ?a ?b) ?c) ==> (/ (+ ?a (* ?b ?c)) ?b)
(/ (+ ?a (* ?b ?c)) ?b) ==> (+ (/ ?a ?b) ?c)
( + ( / ?x 2 ) ( % ?x 2 ) ) ==> ( / ( + ?x 1 ) 2 )
( + (* ?x ?a) (* ?y ?b)) ==> ( * (+ (* ?x (/ ?a ?b)) ?y) ?b) if (&& (!= ?b 0) (== (% ?a ?b) 0))
(/ 0 ?x) ==> (0)
(/ ?a ?a) ==> 1 if (!= ?a 0)
(/ (* -1 ?a) ?b) ==> (/ ?a (* -1 ?b))
(/ ?a (* -1 ?b)) ==> (/ (* -1 ?a) ?b)
(* -1 (/ ?a ?b)) ==> (/ (* -1 ?a) ?b)
(/ (* -1 ?a) ?b) ==> (* -1 (/ ?a ?b))
( / ( * ?x ?a ) ?b ) ==> ( / ?x ( / ?b ?a ) ) if (&& (> ?a 0) (== (% ?b ?a) 0))
( / ( * ?x ?a ) ?b ) ==> ( * ?x ( / ?a ?b ) ) if (&& (> ?b 0) (== (% ?a ?b) 0))
( / ( + ( * ?x ?a ) ?y ) ?b ) ==> ( + ( * ?x ( / ?a ?b ) ) ( / ?y ?b ) ) if (&& (> ?b 0) (== (% ?a ?b) 0))
( / ( + ?x ?a ) ?b ) ==> ( + ( / ?x ?b ) ( / ?a ?b ) ) if (&& (> ?b 0) (== (% ?a ?b) 0))
(!= ?x ?y) ==> (! (== ?x ?y))
(max ?a ?b) ==> (* -1 (min (* -1 ?a) (* -1 ?b)))
(&& ?y ?x) ==> (&& ?x ?y)
(&& ?a (&& ?b ?c)) ==> (&& (&& ?a ?b) ?c)
(&& 1 ?x) ==> ?x
(&& ?x ?x) ==> ?x
(&& ?x (! ?x)) ==> 0
( && ( == ?x ?c0 ) ( == ?x ?c1 ) ) ==> 0 if (!= ?c1 ?c0)
( && ( != ?x ?c0 ) ( == ?x ?c1 ) ) ==> ( == ?x ?c1 ) if (!= ?c1 ?c0)
(&& (< ?x ?y) (< ?x ?z)) ==> (< ?x (min ?y ?z))
(< ?x (min ?y ?z)) ==> (&& (< ?x ?y) (< ?x ?z))
(&& (<= ?x ?y) (<= ?x ?z)) ==> (<= ?x (min ?y ?z))
(<= ?x (min ?y ?z)) ==> (&& (<= ?x ?y) (<= ?x ?z))
(&& (< ?y ?x) (< ?z ?x)) ==> (< (max ?y ?z) ?x)
(> ?x (max ?y ?z)) ==> (&& (< ?z ?x) (< ?y ?x))
(&& (<= ?y ?x) (<= ?z ?x)) ==> (<= (max ?y ?z) ?x)
(>= ?x (max ?y ?z)) ==> (&& (<= ?z ?x) (<= ?y ?x))
( && ( < ?c0 ?x ) ( < ?x ?c1 ) ) ==> 0 if (<= ?c1 (+ ?c0 1))
( && ( <= ?c0 ?x ) ( <= ?x ?c1 ) ) ==> 0 if (< ?c1 ?c0)
( && ( <= ?c0 ?x ) ( < ?x ?c1 ) ) ==> 0 if (<= ?c1 ?c0)
(&& ?a (|| ?b ?c)) ==> (|| (&& ?a ?b) (&& ?a ?c))
(|| ?a (&& ?b ?c)) ==> (&& (|| ?a ?b) (|| ?a ?c))
(|| ?x (&& ?x ?y)) ==> ?x
(- ?a ?b) ==> (+ ?a (* -1 ?b))
(* ?a ?b) ==> (* ?b ?a)
(* ?a (* ?b ?c)) ==> (* (* ?a ?b) ?c)
(* ?a 0) ==> 0
(* ?a 1) ==> ?a
(* (/ ?a ?b) ?b) ==> (- ?a (% ?a ?b))
(* (max ?a ?b) (min ?a ?b)) ==> (* ?a ?b)
(/ (* ?y ?x) ?x) ==> ?y
(<= ?x ?y) ==> (! (< ?y ?x))
(! (< ?y ?x)) ==> (<= ?x ?y)
(>= ?x ?y) ==> (! (< ?x ?y))
(! (== ?x ?y)) ==> (!= ?x ?y)
(! (! ?x)) ==> ?x
(> ?x ?z) ==> (< ?z ?x)
(< ?x ?y) ==> (< (* -1 ?y) (* -1 ?x))
(< ?a ?a) ==> 0
(< (+ ?x ?y) ?z) ==> (< ?x (- ?z ?y))
(< ?z (+ ?x ?y)) ==> (< (- ?z ?y) ?x)
(< (- ?a ?y) ?a ) ==> 1 if (> ?y 0)
(< 0 ?y ) ==> 1 if (> ?y 0)
(< ?y 0 ) ==> 1 if (< ?y 0)
( < ( min ?x ?y ) ?x ) ==> ( < ?y ?x )
( < ( min ?z ?y ) ( min ?x ?y ) ) ==> ( < ?z ( min ?x ?y ) )
( < ( max ?z ?y ) ( max ?x ?y ) ) ==> ( < ( max ?z ?y ) ?x )
( < ( min ?z ?y ) ( min ?x ( + ?y ?c0 ) ) ) ==> ( < ( min ?z ?y ) ?x ) if (> ?c0 0)
( < ( max ?z ( + ?y ?c0 ) ) ( max ?x ?y ) ) ==> ( < ( max ?z ( + ?y ?c0 ) ) ?x ) if (> ?c0 0)
( < ( min ?z ( + ?y ?c0 ) ) ( min ?x ?y ) ) ==> ( < ( min ?z ( + ?y ?c0 ) ) ?x ) if (< ?c0 0)
( < ( max ?z ?y ) ( max ?x ( + ?y ?c0 ) ) ) ==> ( < ( max ?z ?y ) ?x ) if (< ?c0 0)
( < ( min ?x ?y ) (+ ?x ?c0) ) ==> 1 if (> ?c0 0)
(< (max ?a ?c) (min ?a ?b)) ==> 0
(< (* ?x ?y) ?z) ==> (< ?x ( / (- ( + ?z ?y ) 1 ) ?y ) )) if (> ?y 0)
(< ?y (/ ?x ?z)) ==> ( < ( - ( * ( + ?y 1 ) ?z ) 1 ) ?x ) if (> ?z 0)
(< ?a (% ?x ?b)) ==> 1 if (<= ?a (- 0 (abs ?b)))
(< ?a (% ?x ?b)) ==> 0 if (>= ?a (abs ?b))
(min ?a ?b) ==> (min ?b ?a)
(min (min ?x ?y) ?z) ==> (min ?x (min ?y ?z))
(min ?x ?x) ==> ?x
(min (max ?x ?y) ?x) ==> ?x
(min (max ?x ?y) (max ?x ?z)) ==> (max (min ?y ?z) ?x)
(min (max (min ?x ?y) ?z) ?y) ==> (min (max ?x ?z) ?y)
(min (+ ?a ?b) ?c) ==> (+ (min ?b (- ?c ?a)) ?a)
(+ (min ?x ?y) ?z) ==> (min (+ ?x ?z) (+ ?y ?z))
(min ?x (+ ?x ?a)) ==> ?x if (> ?a 0)
(min ?x (+ ?x ?a)) ==> (+ ?x ?a) if (< ?a 0)
(* (min ?x ?y) ?z) ==> (min (* ?x ?z) (* ?y ?z)) if (> ?z 0)
(min (* ?x ?z) (* ?y ?z)) ==> (* (min ?x ?y) ?z) if (> ?z 0)
(* (min ?x ?y) ?z) ==> (max (* ?x ?z) (* ?y ?z)) if (< ?z 0)
(max (* ?x ?z) (* ?y ?z)) ==> (* (min ?x ?y) ?z) if (< ?z 0)
(/ (min ?x ?y) ?z) ==> (min (/ ?x ?z) (/ ?y ?z)) if (> ?z 0)
(min (/ ?x ?z) (/ ?y ?z)) ==> (/ (min ?x ?y) ?z) if (> ?z 0)
(/ (max ?x ?y) ?z) ==> (min (/ ?x ?z) (/ ?y ?z)) if (< ?z 0)
(min (/ ?x ?z) (/ ?y ?z)) ==> (/ (max ?x ?y) ?z) if (< ?z 0)
( min ( max ?x ?c0 ) ?c1 ) ==> ?c1 if (<= ?c1 ?c0)
( min ( * ( / ?x ?c0 ) ?c0 ) ?x ) ==> ( * ( / ?x ?c0 ) ?c0 ) if (> ?c0 0)
(min (% ?x ?c0) ?c1) ==> (% ?x ?c0) if (>= ?c1 (- (abs ?c0) 1))
(min (% ?x ?c0) ?c1) ==> ?c1 if (<= ?c1 (- 0 (abs (+ ?c0 1))))
( min ( max ?x ?c0 ) ?c1 ) ==> ( max ( min ?x ?c1 ) ?c0 ) if (<= ?c0 ?c1)
( max ( min ?x ?c1 ) ?c0 ) ==> ( min ( max ?x ?c0 ) ?c1 ) if (<= ?c0 ?c1)
( < ( min ?y ?c0 ) ?c1 ) ==> ( || ( < ?y ?c1 ) ( < ?c0 ?c1 ) )
( < ( max ?y ?c0 ) ?c1 ) ==> ( && ( < ?y ?c1 ) ( < ?c0 ?c1 ) )
( < ?c1 ( max ?y ?c0 ) ) ==> ( || ( < ?c1 ?y ) ( < ?c1 ?c0 ) )
( min ( * ?x ?a ) ?b ) ==> ( * ( min ?x ( / ?b ?a ) ) ?a ) if (&& (> ?a 0) (== (% ?b ?a) 0))
( min ( * ?x ?a ) ( * ?y ?b ) ) ==> ( * ( min ?x ( * ?y ( / ?b ?a ) ) ) ?a ) if (&& (> ?a 0) (== (% ?b ?a) 0))
( min ( * ?x ?a ) ?b ) ==> ( * ( max ?x ( / ?b ?a ) ) ?a ) if (&& (< ?a 0) (== (% ?b ?a) 0))
( min ( * ?x ?a ) ( * ?y ?b ) ) ==> ( * ( max ?x ( * ?y ( / ?b ?a ) ) ) ?a ) if (&& (< ?a 0) (== (% ?b ?a) 0))
(% 0 ?x) ==> 0
(% ?x ?x) ==> 0
(% ?x 1) ==> 0
(% ?x ?c1) ==> (% (+ ?x ?c1) ?c1) if (<= ?c1 (abs ?x))
(% ?x ?c1) ==> (% (- ?x ?c1) ?c1) if (<= ?c1 (abs ?x))
(% (* ?x -1) ?c) ==> (* -1 (% ?x ?c))
(* -1 (% ?x ?c)) ==> (% (* ?x -1) ?c)
(% (- ?x ?y) 2) ==> (% (+ ?x ?y) 2)
( % ( + ( * ?x ?c0 ) ?y ) ?c1 ) ==> ( % ?y ?c1 ) if (&& (!= ?c1 0) (== (% ?c0 ?c1) 0))
(% (* ?c0 ?x) ?c1) ==> 0 if (&& (!= ?c1 0) (== (% ?c0 ?c1) 0))
"#;

fn override_total_rules<L: SynthLanguage>(
    keep_total: &Ruleset<L>,
    keep_cond: &Ruleset<L>,
) -> Ruleset<L> {
    let mut result = Ruleset::default();
    result.extend(keep_total.partition(|r| r.cond.is_none()).0);
    result.extend(keep_cond.partition(|r| r.cond.is_some()).0);
    result
}

fn run_derivability_tests<L: SynthLanguage>(
    base: &Ruleset<L>,
    against: &Ruleset<L>,
    implications: &ImplicationSet<L>,
) -> DerivabilityResult<L> {
    let impl_rules = implications.to_egg_rewrites();

    let (can, cannot) = base.derive(
        ruler::DeriveType::LhsAndRhs,
        against,
        Limits::super_deriving(),
        Some(&impl_rules),
    );

    DerivabilityResult { can, cannot }
}

fn caviar_rules() -> Ruleset<Pred> {
    let rules = CAVIAR_RULES;
    let mut ruleset = Ruleset::default();
    for rule in rules.trim().lines() {
        match Rule::from_string(rule) {
            Ok((rule, None)) => {
                if !rule.is_valid() {
                    println!("skipping {rule} because it is not valid");
                } else {
                    ruleset.add(rule);
                }
            }
            // This error can come from the inclusion of backwards rules:
            // the Caviar ruleset shouldn't have them.
            _ => panic!("Unable to parse single rule: {}", rule),
        }
    }
    ruleset
}

// The naive O(n^2) algorithm to build implications.
// Good for what we'll expect to see in the Caviar
// eval; bad for large sets of assumptions generated
// bottom-up.
fn pairwise_implication_building<L: SynthLanguage>(
    assumptions: &[Assumption<L>],
) -> ImplicationSet<L> {
    let mut implications = ImplicationSet::default();
    for a1 in assumptions {
        for a2 in assumptions {
            let name = format!("{a1} -> {a2}");
            let implication = Implication::new(name.into(), a1.clone(), a2.clone());
            if let Ok(implication) = implication {
                if !implications.contains(&implication) && implication.is_valid() {
                    implications.add(implication);
                }
            }
        }
    }
    implications
}

// Given a ruleset, can Chompy come up with each rule?
// Explodes if rules contains non-conditional rules.
fn can_synthesize_all<L: SynthLanguage>(rules: Ruleset<L>) -> (Ruleset<L>, Ruleset<L>) {
    let mut can = Ruleset::default();
    let mut cannot = Ruleset::default();
    for rule in rules.iter() {
        // we do this weird dummy rulest thing because
        // we need to make sure that the candidates that Chompy spits out
        // are equivalent to the rules in the ruleset under renaming.
        // that is, if the rule is `(f ?x) => (f ?y)`, we want to make
        // sure we're looking for `(f ?a) => (f ?b)`, because that's what
        // Chompy will spit out (if it finds it).
        let mut dummy_ruleset: Ruleset<L> = Ruleset::default();
        let lhs = L::instantiate(&rule.lhs);
        let rhs = L::instantiate(&rule.rhs);
        let cond = L::instantiate(&rule.cond.clone().unwrap().chop_assumption());

        dummy_ruleset.add_cond_from_recexprs(&lhs, &rhs, &cond, 0);

        // it might have accepted the backwards version of the rule, i guess.
        assert!(dummy_ruleset.len() <= 2);
        let desired_rule = dummy_ruleset.iter().take(1).next().unwrap();

        let workload = Workload::new(&[lhs.to_string(), rhs.to_string()]);

        // we append the term workload here because the condition workload
        // needs to have the same environment to evaluate cvecs under as the parent,
        // which means their set of variables must match.
        let cond_workload = Workload::new(&[cond.to_string()]).append(workload.clone());

        let predicate_map = build_pvec_to_patterns(cond_workload);

        let candidates = Ruleset::conditional_cvec_match(
            &workload.to_egraph(),
            &Ruleset::default(),
            &predicate_map,
            &ImplicationSet::default(),
        );

        println!("candidates: (tried to synthesize {rule})");
        for candidate in candidates.iter() {
            println!("  {candidate}");
        }

        if candidates.contains(desired_rule) {
            can.add(rule.clone());
        } else {
            cannot.add(rule.clone());
        }
    }

    (can, cannot)
}

#[cfg(test)]
pub mod halide_derive_tests {
    use std::path::Path;

    use ruler::{
        conditions::{generate::compress, implication_set::run_implication_workload},
        enumo::Metric,
        halide::og_recipe,
        recipe_utils::{recursive_rules_cond, run_workload, Lang},
    };

    use super::*;

    #[test]
    // A simple derivability test. How many Caviar rules can Chompy's rulesets derive?
    fn chompy_vs_caviar() {
        // Don't run this test as part of the "unit tests" thing in CI.
        if std::env::var("SKIP_RECIPES").is_ok() {
            return;
        }

        // root directory: "out/derive.json"
        let binding = std::env::var("OUT_DIR").expect("OUT_DIR environment variable not set")
            + "/derive.json";
        let out_path: &Path = Path::new(&binding);
        let chompy_rules = og_recipe();
        let caviar_rules = caviar_rules();

        let all_conditions: Vec<_> = caviar_rules
            .iter()
            .chain(chompy_rules.iter())
            .filter_map(|r| {
                r.cond.as_ref().and_then(|c| {
                    Assumption::new(
                        Pred::generalize(
                            &Pred::instantiate(&c.chop_assumption()),
                            &mut Default::default(),
                        )
                        .to_string(),
                    )
                    .ok()
                })
            })
            .collect();

        let implication_rules: ImplicationSet<Pred> =
            pairwise_implication_building(&all_conditions);

        // see how many caviar rules we can derive, given the same
        // total caviar rules.
        let chompy_edited = override_total_rules(&caviar_rules, &chompy_rules);
        let chompy_only_conditional_rules = chompy_edited.partition(|r| r.cond.is_some()).0;
        let forward_result =
            run_derivability_tests(&chompy_edited, &caviar_rules, &implication_rules);
        let backward_result = run_derivability_tests(
            &caviar_rules,
            &chompy_only_conditional_rules,
            &implication_rules,
        );

        let to_json = |result: DerivabilityResult<Pred>| {
            serde_json::json!({
                "can": result.can.iter().map(|r| r.to_string()).collect::<Vec<_>>(),
                "cannot": result.cannot.iter().map(|r| r.to_string()).collect::<Vec<_>>(),
            })
        };

        let to_write = serde_json::json!({
            "forwards": to_json(forward_result),
            "backwards": to_json(backward_result),
        });
        std::fs::write(out_path, to_write.to_string())
            .expect("Failed to write derivability results to file");
    }

    // A test to see if we can correctly choose all Caviar handwritten rules
    // as candidates.
    #[test]
    fn synthesize_all_caviar_as_candidates() {
        // Don't run this test as part of the "unit tests" thing in CI.
        if std::env::var("SKIP_RECIPES").is_ok() {
            return;
        }

        let caviar_conditional_rules = caviar_rules().partition(|r| r.cond.is_some()).0;
        let (_, cannot) = can_synthesize_all(caviar_conditional_rules.clone());
        // This is a magic number for now, but later we'll document specific
        // rules we can't derive along with why.
        assert_eq!(cannot.len(), 7);
    }

    #[test]
    // This test makes sure that Chompy's derivability (minimization)
    // algorithm is robust enough to not synthesize both of these rules
    // (it needs to just pick one):
    // // (min ?a ?b) ==> ?a if (<= ?a ?b)
    // // (min ?a ?b) ==> ?b if (<= ?b ?a)
    // // (min ?b ?a) ==> ?b if (<= ?b ?a)
    // // (min ?b ?a) ==> ?a if (<= ?a ?b)
    fn chompy_shouldnt_make_these() {
        if std::env::var("SKIP_RECIPES").is_ok() {
            return;
        }

        let cond_workload = Workload::new(&["(OP V V)"])
            .plug("OP", &Workload::new(&["<", "<="]))
            .plug("V", &Workload::new(&["a", "b", "c", "0"]));

        let rules = run_workload(
            cond_workload.clone(),
            None,
            Ruleset::default(),
            ImplicationSet::default(),
            Limits::synthesis(),
            Limits::minimize(),
            true,
        );

        let cond_workload = compress(&cond_workload, rules.clone());

        let implications = run_implication_workload(
            &cond_workload,
            &["a".to_string(), "b".to_string(), "c".to_string()],
            &Default::default(),
            &rules,
        );

        let min_max_rules: Ruleset<Pred> = recursive_rules_cond(
            Metric::Atoms,
            3,
            Lang::new(&[], &["a", "b", "c"], &[&[], &["min", "max"]]),
            rules.clone(),
            implications.clone(),
            cond_workload.clone(),
        );

        println!("min_max_rules: {}", min_max_rules.len());
        for r in min_max_rules.iter() {
            println!("  {r}");
        }

        let mut against: Ruleset<Pred> = Ruleset::default();
        against.add(
            Rule::from_string("(min ?a ?b) ==> ?a if (<= ?a ?b)")
                .unwrap()
                .0,
        );

        against.add(
            Rule::from_string("(min ?a ?b) ==> ?b if (<= ?b ?a)")
                .unwrap()
                .0,
        );

        against.add(
            Rule::from_string("(min ?b ?a) ==> ?b if (<= ?b ?a)")
                .unwrap()
                .0,
        );

        against.add(
            Rule::from_string("(min ?b ?a) ==> ?a if (<= ?a ?b)")
                .unwrap()
                .0,
        );

        let mut matches = 0;
        for r in against.iter() {
            assert!(min_max_rules.can_derive_cond(
                ruler::DeriveType::LhsAndRhs,
                r,
                Limits::deriving(),
                &implications.to_egg_rewrites(),
            ));
            if min_max_rules.contains(r) {
                matches += 1;
            }
        }

        assert_eq!(matches, 1);
    }

    // A sanity test.
    // If we can't synthesize these rules, or synthesize rules that derive
    // them, something terrible has happened.
    #[test]
    fn chompy_cant_forget_these() {
        if std::env::var("SKIP_RECIPES").is_ok() {
            return;
        }
        let mut all_rules: Ruleset<Pred> = Ruleset::default();
        let mut expected: Ruleset<Pred> = Default::default();
        for line in r#"(* (min ?x ?y) ?z) ==> (min (* ?x ?z) (* ?y ?z)) if (> ?z 0)
(min (* ?x ?z) (* ?y ?z)) ==> (* (min ?x ?y) ?z) if (> ?z 0)
(* (min ?x ?y) ?z) ==> (max (* ?x ?z) (* ?y ?z)) if (< ?z 0)
(max (* ?x ?z) (* ?y ?z)) ==> (* (min ?x ?y) ?z) if (< ?z 0)
(min ?a ?b) ==> ?a if (<= ?a ?b)
(max ?a ?b) ==> ?a if (<= ?b ?a)
(min ?a (+ ?a ?b)) ==> ?a if (<= 0 ?b)
(min ?a (+ ?a ?b)) ==> (+ ?a ?b) if (<= ?b 0)
(max ?a (+ ?a ?b)) ==> ?a if (<= ?b 0)
(max ?a (+ ?a ?b)) ==> (+ ?a ?b) if (<= 0 ?b)"#
            .lines()
        {
            let rule: Rule<Pred> = Rule::from_string(line).unwrap().0;
            assert!(rule.is_valid());
            expected.add(rule);
        }

        let cond_wkld = &Workload::new(&["(OP2 V V)"])
            .plug("OP2", &Workload::new(&["<", "<=", ">", ">="]))
            .plug("V", &Workload::new(&["a", "b", "c", "0"]));

        let cond_rules: Ruleset<Pred> = run_workload(
            cond_wkld.clone(),
            None,
            Ruleset::default(),
            ImplicationSet::default(),
            Limits::synthesis(),
            Limits::minimize(),
            true,
        );

        all_rules.extend(cond_rules.clone());

        let cond_wkld = compress(cond_wkld, cond_rules.clone());

        println!("compressed");
        for c in cond_wkld.clone().force() {
            println!("c: {c}");
        }

        let implications = run_implication_workload(
            &cond_wkld,
            &["a".to_string(), "b".to_string(), "c".to_string()],
            &Default::default(),
            &cond_rules,
        );

        for i in implications.iter() {
            println!("i: {}", i.name());
        }

        let min_max_add_rules = recursive_rules_cond(
            Metric::Atoms,
            5,
            Lang::new(&[], &["a", "b", "c"], &[&[], &["min", "max", "+"]]),
            all_rules.clone(),
            implications.clone(),
            cond_wkld.clone(),
        );

        all_rules.extend(min_max_add_rules);

        let min_max_sub_rules = recursive_rules_cond(
            Metric::Atoms,
            5,
            Lang::new(&[], &["a", "b", "c"], &[&[], &["min", "max", "-"]]),
            all_rules.clone(),
            implications.clone(),
            cond_wkld.clone(),
        );

        all_rules.extend(min_max_sub_rules);

        let min_max_mul_rules = recursive_rules_cond(
            Metric::Atoms,
            7,
            Lang::new(&[], &["a", "b", "c"], &[&[], &["min", "max", "*"]]),
            all_rules.clone(),
            implications.clone(),
            cond_wkld.clone(),
        );

        all_rules.extend(min_max_mul_rules);

        for r in expected.iter() {
            assert!(
                all_rules.can_derive_cond(
                    ruler::DeriveType::LhsAndRhs,
                    r,
                    Limits::deriving(),
                    &implications.to_egg_rewrites(),
                ),
                "couldn't derive rule: {}",
                r
            );
        }
    }
}
