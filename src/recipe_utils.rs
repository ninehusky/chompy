use std::time::Instant;

use egg::EGraph;

use crate::{
    conditions::implication_set::ImplicationSet,
    enumo::{ChompyState, Filter, Metric, Ruleset, Scheduler, Workload},
    Limits, SynthAnalysis, SynthLanguage,
};

/// Iterate a grammar (represented as a workload) up to a certain size metric
pub fn iter_metric(wkld: Workload, atom: &str, met: Metric, n: usize) -> Workload {
    let mut pegs = wkld.clone();
    for i in 1..(n + 1) {
        pegs = wkld
            .clone()
            .plug(atom, &pegs)
            .filter(Filter::MetricLt(met, i + 1));
    }
    pegs
}

pub fn substitute(workload: Workload, sub: Workload, atom: &str) -> Workload {
    let mut pegs = Workload::Set(vec![]);
    let substitutions = sub.force();
    for sub in substitutions {
        pegs = pegs.append(workload.clone().plug(atom, &Workload::Set(vec![sub])));
    }
    pegs
}

fn run_workload_internal<L: SynthLanguage>(
    state: &mut ChompyState<L>,
    prior_limits: Limits,
    minimize_limits: Limits,
    fast_match: bool,
    allow_empty: bool,
) -> Ruleset<L> {
    let prior: Ruleset<L> = state.chosen().clone();
    let cond_workload = state.predicates().clone();

    let t = Instant::now();
    let num_prior = prior.len();

    // 1. Create an e-graph from the workload, and compress
    //    it using the prior rules.
    let egraph: EGraph<L, SynthAnalysis> = state.terms().to_egraph();
    let compressed = Scheduler::Compress(prior_limits).run(&egraph, &prior);

    // 2. Discover total candidates using cvec matching.
    let mut total_candidates = if fast_match {
        Ruleset::fast_cvec_match(&compressed, prior.clone())
    } else {
        Ruleset::cvec_match(&compressed)
    };

    let mut chosen: Ruleset<L> = prior.clone();

    // 3. Shrink the total candidates to a minimal set using the existing rules.
    let (chosen_total, _) =
        total_candidates.minimize(prior.clone(), Scheduler::Compress(minimize_limits));

    chosen.extend(chosen_total.clone());

    // 4. Using the rules that we've just discovered, shrink the egraph again.
    let compressed = Scheduler::Compress(prior_limits).run(&compressed, &chosen);

    // 5. Find conditional rules.
    // To help Chompy scale to higher condition sizes, we'll need to limit the size of the conditions we consider.
    // As a heuristic, we'll go in ascending order of condition sizes.

    if cond_workload == Workload::empty() {
        // If there are no conditions, we can just return the chosen rules.
        return chosen;
    }

    // TODO: Make this a parameter; 5 is a bit arbitrary lol.
    let max_cond_size = 5;

    let impl_prop_rules = state.implications();

    for cond_size in 1..=max_cond_size {
        let curr_wkld = cond_workload
            .clone()
            .filter(Filter::MetricEq(Metric::Atoms, cond_size + 1));

        if curr_wkld.force().is_empty() {
            continue;
        }

        let mut conditional_candidates = Ruleset::conditional_cvec_match(
            &compressed,
            &chosen,
            &state.pvec_to_patterns(),
            state.implications(),
        );

        let (chosen_cond, _) = conditional_candidates
            .minimize_cond(chosen.clone(), &impl_prop_rules.to_egg_rewrites());
        chosen_cond.pretty_print();
        chosen.extend(chosen_cond.clone());
    }

    let time = t.elapsed().as_secs_f64();

    if chosen.is_empty() && !allow_empty {
        panic!("Didn't learn any rules!");
    }

    println!(
        "Learned {} bidirectional rewrites, and {} conditional rules ({} total rewrites) in {} using {} prior rewrites",
        chosen.bidir_len(),
        chosen.condition_len(),
        chosen.len(),
        time,
        num_prior
    );

    chosen.pretty_print();

    chosen
}

/// Runs rule inference:
///     1. convert workload to e-graph
///     2. If there are prior rules, compress the e-graph using them
///     3. Find candidates via CVec matching
///     4. Minimize the candidates with respect to the prior rules
pub fn run_workload<L: SynthLanguage>(
    workload: Workload,
    cond_workload: Option<Workload>,
    prior: Ruleset<L>,
    prior_impls: ImplicationSet<L>,
    prior_limits: Limits,
    minimize_limits: Limits,
    fast_match: bool,
) -> Ruleset<L> {
    println!("[run_workload] Running workload");
    let start = Instant::now();
    let mut state: ChompyState<L> = ChompyState::new(
        workload,
        prior,
        cond_workload.unwrap_or(Workload::empty()),
        prior_impls,
    );

    let res = run_workload_internal(&mut state, prior_limits, minimize_limits, fast_match, true);
    println!(
        "[run_workload] Finished workload in {:.2}s",
        start.elapsed().as_secs_f64()
    );
    res
}

/// The fast-forwarding algorithm
///     1. Convert workload to e-graph
///     2. Find allowed rules in prior
///     3. Compress the e-graph with allowed rules
///     4. Grow the e-graph using the exploratory rules from the domain
///     5. Extract rule candidates
///     6. Compress the e-graph with all rules
///     7. Extract rule candidates
///     8. Minimize rule candidates
pub fn run_fast_forwarding<L: SynthLanguage>(
    workload: Workload,
    prior: Ruleset<L>,
    prior_limits: Limits,
    minimize_limits: Limits,
) -> Ruleset<L> {
    let t = Instant::now();

    let eg_init = workload.to_egraph::<L>();
    let num_prior = prior.len();

    // Allowed rules: compress e-graph, no candidates
    let (allowed, _) = prior.partition(|rule| L::is_allowed_rewrite(&rule.lhs, &rule.rhs));
    let eg_allowed = Scheduler::Compress(prior_limits).run(&eg_init, &allowed);

    // Translation rules: grow egraph, extract candidates, assert!(saturated)
    let exploratory = L::get_exploratory_rules();
    let eg_denote = Scheduler::Simple(prior_limits).run(&eg_allowed, &exploratory);
    let mut candidates = Ruleset::extract_candidates(&eg_allowed, &eg_denote);

    // All rules: compress e-graph, extract candidates
    let mut all_rules = prior.clone();
    all_rules.extend(exploratory);
    let eg_final = Scheduler::Compress(prior_limits).run(&eg_denote, &all_rules);
    candidates.extend(Ruleset::extract_candidates(&eg_denote, &eg_final));

    let chosen = candidates
        .minimize(prior, Scheduler::Compress(minimize_limits))
        .0;
    let time = t.elapsed().as_secs_f64();

    println!(
        "Learned {} bidirectional rewrites ({} total rewrites) in {} using {} prior rewrites",
        chosen.bidir_len(),
        chosen.len(),
        time,
        num_prior
    );

    chosen.pretty_print();

    chosen
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Lang {
    pub vals: Vec<String>,
    pub vars: Vec<String>,
    pub ops: Vec<Vec<String>>,
}

impl Lang {
    pub fn new(vals: &[&str], vars: &[&str], ops: &[&[&str]]) -> Self {
        Self {
            vals: vals.iter().map(|x| x.to_string()).collect(),
            vars: vars.iter().map(|x| x.to_string()).collect(),
            ops: ops
                .iter()
                .map(|o| o.iter().map(|x| x.to_string()).collect())
                .collect(),
        }
    }
}

/// Incrementally construct a ruleset by running rule inference up to a size bound,
/// using previously-learned rules at each step.
pub fn recursive_rules_cond<L: SynthLanguage>(
    metric: Metric,
    n: usize,
    lang: Lang,
    prior: Ruleset<L>,
    prior_impls: ImplicationSet<L>,
    conditions: Workload,
) -> Ruleset<L> {
    if n < 1 {
        Ruleset::default()
    } else {
        let mut rec = recursive_rules_cond(
            metric,
            n - 1,
            lang.clone(),
            prior.clone(),
            prior_impls.clone(),
            conditions.clone(),
        );
        let base_lang = if lang.ops.len() == 2 {
            base_lang(2)
        } else {
            base_lang(3)
        };
        let mut wkld = iter_metric(base_lang, "EXPR", metric, n)
            .filter(Filter::Contains("VAR".parse().unwrap()))
            .plug("VAR", &Workload::new(lang.vars))
            .plug("VAL", &Workload::new(lang.vals));
        // let ops = vec![lang.uops, lang.bops, lang.tops];
        for (i, ops) in lang.ops.iter().enumerate() {
            wkld = wkld.plug(format!("OP{}", i + 1), &Workload::new(ops));
        }

        rec.extend(prior);
        let allow_empty = n < 3;

        let mut state: ChompyState<L> =
            ChompyState::new(wkld, rec.clone(), conditions.clone(), prior_impls);

        let new_rules = run_workload_internal(
            &mut state,
            Limits::synthesis(),
            Limits::minimize(),
            true,
            allow_empty,
        );
        let mut all = new_rules;
        all.extend(rec);
        all
    }
}

/// Incrementally construct a ruleset by running rule inference up to a size bound,
/// using previously-learned rules at each step.
pub fn recursive_rules<L: SynthLanguage>(
    metric: Metric,
    n: usize,
    lang: Lang,
    prior: Ruleset<L>,
) -> Ruleset<L> {
    recursive_rules_cond(
        metric,
        n,
        lang,
        prior,
        ImplicationSet::default(),
        Workload::empty(),
    )
}

/// Util function for making a grammar with variables, values, and operators with up to n arguments.
pub fn base_lang(n: usize) -> Workload {
    let mut vals = vec!["VAR".to_string(), "VAL".to_string()];
    for i in 1..(n + 1) {
        let s = format!("(OP{}{})", i, " EXPR".repeat(i));
        vals.push(s);
    }
    Workload::new(vals)
}

#[cfg(test)]
mod test {
    use crate::{
        enumo::{Metric, Workload},
        recipe_utils::{base_lang, iter_metric},
    };

    #[test]
    fn iter_metric_test() {
        let lang = base_lang(2);
        let atoms1 = iter_metric(lang.clone(), "EXPR", Metric::Atoms, 1).force();
        assert_eq!(atoms1.len(), 2);

        let atoms2 = iter_metric(lang.clone(), "EXPR", Metric::Atoms, 2).force();
        assert_eq!(atoms2.len(), 4);

        let atoms3 = iter_metric(lang.clone(), "EXPR", Metric::Atoms, 3).force();
        assert_eq!(atoms3.len(), 10);

        let atoms4 = iter_metric(lang.clone(), "EXPR", Metric::Atoms, 4).force();
        assert_eq!(atoms4.len(), 24);

        let atoms5 = iter_metric(lang.clone(), "EXPR", Metric::Atoms, 5).force();
        assert_eq!(atoms5.len(), 66);

        let atoms6 = iter_metric(lang.clone(), "EXPR", Metric::Atoms, 6).force();
        assert_eq!(atoms6.len(), 188);

        let atoms6 = iter_metric(lang.clone(), "EXPR", Metric::Atoms, 7).force();
        assert_eq!(atoms6.len(), 570);

        let depth1 = iter_metric(lang.clone(), "EXPR", Metric::Depth, 1).force();
        assert_eq!(depth1.len(), 2);

        let depth2 = iter_metric(lang.clone(), "EXPR", Metric::Depth, 2).force();
        assert_eq!(depth2.len(), 8);

        let depth3 = iter_metric(lang.clone(), "EXPR", Metric::Depth, 3).force();
        assert_eq!(depth3.len(), 74);

        let depth4 = iter_metric(lang.clone(), "EXPR", Metric::Depth, 4).force();
        assert_eq!(depth4.len(), 5552);

        let lists1 = iter_metric(lang.clone(), "EXPR", Metric::Lists, 1).force();
        assert_eq!(lists1.len(), 8);

        let lists2 = iter_metric(lang.clone(), "EXPR", Metric::Lists, 2).force();
        assert_eq!(lists2.len(), 38);

        let lists3 = iter_metric(lang.clone(), "EXPR", Metric::Lists, 3).force();
        assert_eq!(lists3.len(), 224);
    }

    #[test]
    fn iter_metric_fast() {
        // This test will not finish if the pushing monotonic filters through plugs optimization is not working.
        let three = iter_metric(base_lang(3), "EXPR", Metric::Atoms, 3);
        assert_eq!(three.force().len(), 10);

        let four = iter_metric(base_lang(3), "EXPR", Metric::Atoms, 4);
        assert_eq!(four.force().len(), 32);

        let five = iter_metric(base_lang(3), "EXPR", Metric::Atoms, 5);
        assert_eq!(five.force().len(), 106);

        let six = iter_metric(base_lang(3), "EXPR", Metric::Atoms, 6);
        assert_eq!(six.force().len(), 388);
    }

    #[test]
    fn base_lang_test() {
        assert_eq!(base_lang(0).force().len(), 2);
        assert_eq!(base_lang(1).force().len(), 3);
        assert_eq!(base_lang(2).force().len(), 4);
        assert_eq!(base_lang(3).force().len(), 5);
    }

    #[test]
    fn empty_plug() {
        let wkld =
            iter_metric(base_lang(3), "EXPR", Metric::Atoms, 6).plug("OP3", &Workload::empty());
        assert_eq!(wkld.force().len(), 188);
    }
}
