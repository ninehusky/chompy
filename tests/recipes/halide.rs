use egg::{AstSize, EGraph, Extractor, Pattern, RecExpr, Rewrite};
use ruler::{
    enumo::{Filter, Metric, Rule, Ruleset, Workload},
    recipe_utils::{
        base_lang, iter_metric, recursive_rules, recursive_rules_cond, run_workload, Lang,
    },
    HashMap, Limits, SynthAnalysis, SynthLanguage,
};

use crate::Pred;

fn compute_conditional_structures() -> (HashMap<Vec<bool>, Vec<Pattern<Pred>>>, Ruleset<Pred>) {
    // Start by pre-computing a bunch of stuff about conditions.
    let condition_lang = Lang::new(&["0"], &["a", "b", "c"], &[&[], &["<", "<=", "!="]]);

    // chuck em all into an e-graph.
    let base_lang = if condition_lang.ops.len() == 2 {
        base_lang(2)
    } else {
        base_lang(3)
    };
    let mut wkld = iter_metric(base_lang, "EXPR", Metric::Atoms, 3)
        .filter(Filter::Contains("VAR".parse().unwrap()))
        .plug("VAR", &Workload::new(condition_lang.vars))
        .plug("VAL", &Workload::new(condition_lang.vals));
    // let ops = vec![lang.uops, lang.bops, lang.tops];
    for (i, ops) in condition_lang.ops.iter().enumerate() {
        wkld = wkld.plug(format!("OP{}", i + 1), &Workload::new(ops));
    }

    let egraph: EGraph<Pred, SynthAnalysis> = wkld.to_egraph();

    let mut pvec_to_terms: HashMap<Vec<bool>, Vec<Pattern<Pred>>> = HashMap::default();

    let mut cond_prop_ruleset = Ruleset::default();

    let forced = wkld.filter(Filter::MetricEq(Metric::Atoms, 3)).force();

    let true_recexpr: RecExpr<Pred> = "TRUE".parse().unwrap();

    let mut i = 0;
    println!("forced: {:?}", forced.len());
    for cond1 in forced.clone() {
        i += 1;
        let cond1: RecExpr<Pred> = cond1.to_string().parse().unwrap();
        let cond1_pat = Pattern::from(&cond1);

        let cond1_id = egraph
            .lookup_expr(&cond1_pat.to_string().parse().unwrap())
            .unwrap();

        let pvec = egraph[cond1_id]
            .data
            .cvec
            .clone()
            .iter()
            .map(|b| *b != Some(0))
            .collect();

        pvec_to_terms
            .entry(pvec)
            .or_insert_with(Vec::new)
            .push(cond1_pat.clone());

        for cond2 in forced.iter().skip(i) {
            let cond2_recexpr: RecExpr<Pred> = cond2.to_string().parse().unwrap();
            let cond2_pat = Pattern::from(&cond2_recexpr);

            if Pred::condition_implies(&cond1_pat.clone(), &cond2_pat) {
                let rw_name = format!("{} => {}", cond2, true_recexpr);
                let rw: Rewrite<Pred, SynthAnalysis> = Rewrite::new(
                    rw_name.clone(),
                    Pattern::from(&true_recexpr.clone()),
                    cond2_pat.clone(),
                )
                .unwrap();
                let rule: Rule<Pred> = Rule {
                    name: format!("{} => {}", cond2, true_recexpr).into(),
                    lhs: Pattern::from(&true_recexpr.clone()),
                    rhs: cond2_pat.clone(),
                    // if cond1 is true, then cond1 -> cond2.
                    cond: Some(cond1_pat.clone()),
                    rewrite: rw,
                };
                cond_prop_ruleset.add(rule);
            }
        }
    }

    (pvec_to_terms, cond_prop_ruleset)
}

pub fn halide_rules_for_caviar_conditional() -> Ruleset<Pred> {
    let (pvec_to_terms, cond_prop_ruleset) = compute_conditional_structures();
    let mut all_rules = Ruleset::default();
    let bool_only = recursive_rules(
        Metric::Atoms,
        5,
        Lang::new(&["0", "1"], &["a", "b", "c"], &[&["!"], &["&&", "||"]]),
        all_rules.clone(),
    );
    all_rules.extend(bool_only);
    let rat_only = recursive_rules_cond(
        Metric::Atoms,
        5,
        Lang::new(
            &["-1", "0", "1"],
            &["a", "b", "c"],
            &[&[], &["+", "-", "*", "min", "max"]],
        ),
        all_rules.clone(),
        &pvec_to_terms,
        &cond_prop_ruleset,
    );
    all_rules.extend(rat_only.clone());
    let pred_only = recursive_rules_cond(
        Metric::Atoms,
        5,
        Lang::new(
            &["-1", "0", "1"],
            &["a", "b", "c"],
            &[&[], &["<", "<=", "==", "!="], &[]],
        ),
        all_rules.clone(),
        &pvec_to_terms,
        &cond_prop_ruleset,
    );
    all_rules.extend(pred_only);

    let full = recursive_rules_cond(
        Metric::Atoms,
        4,
        Lang::new(
            &["-1", "0", "1"],
            &["a", "b", "c"],
            &[
                &["!"],
                &[
                    "&&", "||", "+", "-", "*", "min", "max", "<", "<=", "==", "!=",
                ],
                &[],
            ],
        ),
        all_rules.clone(),
        &pvec_to_terms,
        &cond_prop_ruleset,
    );
    all_rules.extend(full);

    all_rules
}

pub fn halide_rules_for_caviar_total_only() -> Ruleset<Pred> {
    let mut all_rules = Ruleset::default();
    let bool_only = recursive_rules(
        Metric::Atoms,
        5,
        Lang::new(&["0", "1"], &["a", "b", "c"], &[&["!"], &["&&", "||"]]),
        all_rules.clone(),
    );
    all_rules.extend(bool_only);
    let rat_only = recursive_rules(
        Metric::Atoms,
        5,
        Lang::new(
            &["-1", "0", "1"],
            &["a", "b", "c"],
            &[&[], &["+", "-", "*", "min", "max"]],
        ),
        all_rules.clone(),
    );
    all_rules.extend(rat_only.clone());
    let pred_only = recursive_rules(
        Metric::Atoms,
        5,
        Lang::new(
            &["-1", "0", "1"],
            &["a", "b", "c"],
            &[&[], &["<", "<=", "==", "!="], &[]],
        ),
        all_rules.clone(),
    );
    all_rules.extend(pred_only);

    let full = recursive_rules(
        Metric::Atoms,
        4,
        Lang::new(
            &["-1", "0", "1"],
            &["a", "b", "c"],
            &[
                &["!"],
                &[
                    "&&", "||", "+", "-", "*", "min", "max", "<", "<=", "==", "!=",
                ],
                &[],
            ],
        ),
        all_rules.clone(),
    );
    all_rules.extend(full);

    all_rules
}

#[allow(dead_code)]
pub fn halide_rules() -> Ruleset<Pred> {
    let (pvec_to_terms, cond_prop_ruleset) = compute_conditional_structures();

    let mut all_rules = Ruleset::default();
    let bool_only = recursive_rules(
        Metric::Atoms,
        5,
        Lang::new(&["0", "1"], &["a", "b", "c"], &[&["!"], &["&&", "||", "^"]]),
        all_rules.clone(),
    );
    all_rules.extend(bool_only);
    let rat_only = recursive_rules_cond(
        Metric::Atoms,
        5,
        Lang::new(
            &["-1", "0", "1"],
            &["a", "b", "c"],
            &[&["-"], &["+", "-", "*", "min", "max"]],
        ),
        all_rules.clone(),
        &pvec_to_terms,
        &cond_prop_ruleset,
    );
    all_rules.extend(rat_only.clone());
    let pred_only = recursive_rules_cond(
        Metric::Atoms,
        5,
        Lang::new(
            &["-1", "0", "1"],
            &["a", "b", "c"],
            &[&["-"], &["<", "<=", "==", "!="], &["select"]],
        ),
        all_rules.clone(),
        &pvec_to_terms,
        &cond_prop_ruleset,
    );
    all_rules.extend(pred_only);

    let full = recursive_rules_cond(
        Metric::Atoms,
        4,
        Lang::new(
            &["-1", "0", "1"],
            &["a", "b", "c"],
            &[
                &["-", "!"],
                &[
                    "&&", "||", "^", "+", "-", "*", "min", "max", "<", "<=", "==", "!=",
                ],
                &["select"],
            ],
        ),
        all_rules.clone(),
        &pvec_to_terms,
        &cond_prop_ruleset,
    );
    all_rules.extend(full);

    println!("all_rules: done");

    let nested_bops_arith = Workload::new(&["(bop e e)", "v"])
        .plug("e", &Workload::new(&["(bop v v)", "(uop v)", "v"]))
        .plug("bop", &Workload::new(&["+", "-", "*", "<", "max", "min"]))
        .plug("uop", &Workload::new(&["-", "!"]))
        .plug("v", &Workload::new(&["a", "b", "c"]))
        .filter(Filter::Canon(vec![
            "a".to_string(),
            "b".to_string(),
            "c".to_string(),
        ]));
    let new = run_workload(
        nested_bops_arith,
        all_rules.clone(),
        Limits::synthesis(),
        Limits::minimize(),
        true,
        None,
        None,
    );
    all_rules.extend(new);
    let nested_bops_full = Workload::new(&["(bop e e)", "v"])
        .plug("e", &Workload::new(&["(bop v v)", "(uop v)", "v"]))
        .plug(
            "bop",
            &Workload::new(&["&&", "||", "!=", "<=", "==", "<", "max", "min"]),
        )
        .plug("uop", &Workload::new(&["-", "!"]))
        .plug("v", &Workload::new(&["a", "b", "c"]))
        .filter(Filter::Canon(vec![
            "a".to_string(),
            "b".to_string(),
            "c".to_string(),
        ]));
    let new = run_workload(
        nested_bops_full,
        all_rules.clone(),
        Limits::synthesis(),
        Limits::minimize(),
        true,
        None,
        None,
    );
    all_rules.extend(new.clone());

    // NOTE: The following workloads do NOT use all_rules as prior rules
    // Using all_rules as prior_rules leads to OOM
    let select_base = Workload::new([
        "(select V V V)",
        "(select V (OP V V) V)",
        "(select V V (OP V V))",
        "(select V (OP V V) (OP V V))",
        "(OP V (select V V V))",
    ])
    .plug("V", &Workload::new(["a", "b", "c", "d"]));

    let arith = select_base
        .clone()
        .plug("OP", &Workload::new(["+", "-", "*"]));
    let new = run_workload(
        arith,
        rat_only.clone(),
        Limits::synthesis(),
        Limits {
            iter: 1,
            node: 100_000,
            match_: 100_000,
        },
        true,
        None,
        None,
    );
    all_rules.extend(new);

    let arith = select_base.plug("OP", &Workload::new(["min", "max"]));
    let new = run_workload(
        arith,
        rat_only.clone(),
        Limits::synthesis(),
        Limits {
            iter: 1,
            node: 100_000,
            match_: 100_000,
        },
        true,
        None,
        None,
    );
    all_rules.extend(new);

    all_rules
}
