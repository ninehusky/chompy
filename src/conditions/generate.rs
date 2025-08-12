use egg::{AstSize, Extractor, RecExpr};
use reqwest::Client;

use crate::conditions::implication_set::ImplicationSet;
use crate::SynthLanguage;
use crate::{
    enumo::{Filter, Metric, Rule, Ruleset, Scheduler, Workload},
    halide::Pred,
    recipe_utils::{recursive_rules, run_workload, Lang},
    Limits,
};

pub fn get_condition_workload() -> Workload {
    // we're going to do conjunctions of ==, != with
    // variables and 0.
    let start = std::time::Instant::now();
    println!("Beginning condition workload generation");

    let the_atoms = Workload::new(&["a", "b", "c"]).append(Workload::new(&["0"]));

    let the_ints = the_atoms.clone();

    let leaves = Workload::new(&["0", "1", "(OP2 V V)"])
        .plug("V", &the_ints)
        .plug("OP2", &Workload::new(&["<", "==", "<=", "!="]));

    let branches = Workload::new(&["(OP2 V V)"])
        .plug("V", &leaves)
        .plug("OP2", &Workload::new(&["&&"]))
        .filter(Filter::Canon(vec![
            "a".to_string(),
            "b".to_string(),
            "c".to_string(),
        ]));

    let mut eq_rules = Ruleset::default();
    eq_rules.add(
        Rule::from_string("(&& (<= ?a ?b) (<= ?b ?a)) ==> (== ?a ?b)")
            .unwrap()
            .0,
    );

    let new_rules = recursive_rules(
        Metric::Atoms,
        5,
        Lang::new(
            &["0", "1"],
            &["a", "b", "c"],
            &[&[], &["<", "<=", "==", "!=", "&&"]],
        ),
        Ruleset::default(),
    );

    eq_rules.extend(new_rules);

    let rules = run_workload(
        branches.clone(),
        None,
        eq_rules,
        ImplicationSet::default(),
        Limits::synthesis(),
        Limits::minimize(),
        true,
    );

    let branches_better = compress(&branches, rules.clone());

    println!("Condition workload generation took: {:?}", start.elapsed());

    branches_better
}

pub async fn llm_generate_condition<L: SynthLanguage>(
    lhs: &RecExpr<L>,
    rhs: &RecExpr<L>,
    client: Client,
) {
    let start = std::time::Instant::now();
    println!(
        "[llm_generate_condition] Finding weakest condition matching {}, {}",
        lhs, rhs
    );

    let prompt = r#"
You are an expert in generating weakest preconditions for logical rewrites in Halide IR.

## Goal
Given:
1. Left-hand side (lhs): {}
2. Right-hand side (rhs): {}

Determine the **weakest condition** (in s-expression form) such that, whenever the condition holds for the bound variables in the match, the lhs and rhs evaluate to the same value under Halide’s semantics.

The condition:
- Must be sufficient to guarantee equality between lhs and rhs for the given match.
- Must be **logically weakest** — i.e., if a weaker condition would still guarantee equality, prefer that weaker one.
- Must be expressed **purely in allowed operators** (see below).

## Halide semantics for division and modulo
**Division (`/`):**
- Signed integer division rounds according to the **sign of the denominator**:
  - Positive denominator → rounds toward −∞
  - Negative denominator → rounds toward +∞
- Division by zero returns 0 (no fault).
- Division of largest negative signed int by −1 returns the same largest negative signed int (wraps around).
- Type coercion matches types of operands before division.

**Modulo (`%`):**
- Result is always non-negative.
- `%` by a positive or negative number is the same.
- `%` by zero returns 0 (no fault).
- For `b != 0`: `0 <= (a % b) < abs(b)`.

## Allowed operators in conditions
Logical:
- `&&` (and), `||` (or), `!` (not)

Comparison:
- `<`, `<=`, `>`, `>=`, `==`, `!=`

Arithmetic:
- `+`, `-`, `*`, `/` (Halide semantics), `%` (Halide semantics), `abs`

Constants:
- integers, floats, variable symbols (prefixed with `?`)

## Examples

### Example 1
lhs: `(min (* ?x ?a) ?b)`
rhs: `(* (min ?x (/ ?b ?a)) ?a)`
condition:
`(> ?a 0)`

---

### Example 2
lhs: `(< ?a (% ?x ?b))`
rhs: `0`
condition:
`(or (and (== ?b 0) (>= ?a 0)) (and (!= ?b 0) (>= ?a (- (abs ?b) 1))))`

---

### Example 3
lhs: `(/ ?x ?z)`
rhs: `(/ ?y ?z)`
condition:
`(== ?x ?y)`

---

### Example 4
lhs: `(/ ?x ?z)`
rhs: `(/ (* ?y ?a) ?z)`
condition:
`(== ?x (* ?y ?a))`

---

### Example 5
lhs: `(min (/ ?x ?z) (/ ?y ?z))`
rhs: `(/ (min ?x ?y) ?z)`
condition:
`(!= ?z 0)`

---

## Output format
Return **only** the condition as an s-expression.
Do not explain or justify.
Example:
`(&& (> ?a 0) (== (% ?b ?a) 0))`
"#;
}

pub fn compress(workload: &Workload, prior: Ruleset<Pred>) -> Workload {
    let start = std::time::Instant::now();
    println!("[compress] Starting compression of implication workload.");
    let egraph = workload.to_egraph();
    let compressed = Scheduler::Compress(Limits::minimize()).run(&egraph, &prior);

    let mut result = Workload::empty();

    let extractor = Extractor::new(&compressed, AstSize);
    for c in compressed.classes() {
        let (_, best) = extractor.find_best(c.id);

        result = result.append(Workload::new(&[best.to_string()]));
    }

    println!(
        "[compress] Compression took: {:?}, reduced {} classes to {}",
        start.elapsed(),
        egraph.number_of_classes(),
        compressed.number_of_classes()
    );

    result
}

#[test]
fn test_validity() {


    let rule_str = r#"(% (+ (* ?x ?c0) ?y) ?c1) ==> (% ?y ?c1) if (|| (== ?c1 0) (== (% ?c0 ?c1) 0))"#;
    let rule: Rule<Pred> =
        Rule::from_string(rule_str).unwrap().0;
    assert!(rule.is_valid());

}
