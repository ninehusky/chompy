use ruler::{
    conditions::{
        assumption::Assumption, implication::Implication, implication_set::ImplicationSet,
    },
    enumo::{Rule, Ruleset},
    halide::Pred,
    Limits, SynthLanguage,
};

struct DerivabilityResult<L: SynthLanguage> {
    can: Ruleset<L>,
    cannot: Ruleset<L>,
}

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
        &against,
        Limits::deriving(),
        Some(&impl_rules),
    );

    DerivabilityResult { can, cannot }
}

fn caviar_rules() -> Ruleset<Pred> {
    let rules = r#"
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
    let mut ruleset = Ruleset::default();
    for rule in rules.trim().lines() {
        match Rule::from_string(rule) {
            Ok((rule, None)) => {
                if !rule.is_valid() {
                    println!("skipping {} because it is not valid", rule);
                } else {
                    ruleset.add(rule);
                }
            }
            _ => panic!("Unable to parse single rule: {}", rule),
        }
    }
    ruleset
}

fn pairwise_implication_building<L: SynthLanguage>(
    assumptions: &[Assumption<L>],
) -> ImplicationSet<L> {
    let mut implications = ImplicationSet::default();
    for a1 in assumptions {
        for a2 in assumptions {
            let name = format!("{} -> {}", a1, a2);
            let implication = Implication::new(name.into(), a1.clone(), a2.clone());
            if let Ok(implication) = implication {
                if implication.is_valid() {
                    implications.add(implication);
                }
            }
        }
    }
    implications
}

#[cfg(test)]
pub mod halide_derive_tests {
    use ruler::halide::og_recipe;

    use super::*;

    #[test]
    fn chompy_vs_caviar() {
        // Don't run this test as part of the "unit tests" thing in CI.
        if std::env::var("SKIP_RECIPES").is_ok() {
            return;
        }

        let caviar_rules = caviar_rules();
        let chompy_rules = og_recipe();

        let all_conditions: Vec<_> = caviar_rules
            .iter()
            .chain(chompy_rules.iter())
            .filter_map(|r| {
                r.cond
                    .as_ref()
                    .and_then(|c| Assumption::new(c.to_string()).ok())
            })
            .collect();

        let implication_rules: ImplicationSet<Pred> =
            pairwise_implication_building(&all_conditions);

        // see how many caviar rules we can derive, given the same
        // total caviar rules.
        let chompy_edited = override_total_rules(&caviar_rules, &chompy_rules);

        let result = run_derivability_tests(&chompy_edited, &caviar_rules, &implication_rules);

        println!("Chompy can derive:");
        for rule in result.can.iter() {
            if result.cond.is_none() {
                // skip reporting of total rules
                continue;
            }
            println!("  {}", rule);
        }

        println!("Chompy cannot derive:");
        for rule in result.cannot.iter() {
            println!("  {}", rule);
        }
    }
}
