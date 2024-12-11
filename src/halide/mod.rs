use chompy::{Chomper, Rule};
use halide::HalideChomper;
use rand::{rngs::StdRng, Rng, SeedableRng};
use ruler::ValidationResult;
use std::{io::Write, sync::Arc};

use ruler::HashMap;

use std::str::FromStr;

use chompy::{init_egraph, ite::DummySort};
use egglog::{sort::EqSort, EGraph};

use ruler::enumo::Sexp;

pub mod halide;

// returns handwritten conditional rules which are valid.
// TODO: make github issue about invalid handwritten rules.
pub fn get_validated_handwritten_rules() -> Vec<Rule> {
    let lines = include_str!("../../tests/halide/rules.txt").lines();
    let chomper = HalideChomper {
        env: Default::default(),
    };
    let mut rules: Vec<Rule> = vec![];
    for line in lines {
        // split on ;
        let parts: Vec<&str> = line.split(';').collect();
        let rule = match parts.len() {
            2 => Rule {
                condition: None,
                lhs: parts[0].parse().unwrap(),
                rhs: parts[1].parse().unwrap(),
            },
            3 => Rule {
                condition: Some((parts[2].parse().unwrap(), vec![])),
                lhs: parts[0].parse().unwrap(),
                rhs: parts[1].parse().unwrap(),
            },
            _ => panic!("Unexpected number of parts: {}", parts.len()),
        };

        let generalized = chomper.generalize_rule(&rule);
        if let ValidationResult::Valid = chomper.validate_rule(&generalized) {
            rules.push(rule);
        } else {
            println!("Invalid rule: {}", line);
        }
    }
    rules
}

#[test]
fn run_halide_experiment() {
    let env = HalideChomper::make_env(&mut StdRng::seed_from_u64(0));
    let mut chomper = HalideChomper { env };
    let mut egraph = EGraph::default();

    #[derive(Debug)]
    struct HalidePredicateInterpreter {
        chomper: HalideChomper,
    }

    impl chompy::ite::PredicateInterpreter for HalidePredicateInterpreter {
        fn interp_cond(&self, sexp: &Sexp) -> bool {
            let cvec = self.chomper.clone().interpret_term(sexp);
            cvec.iter().all(|x| x.is_some() && x.unwrap() != 0)
        }
    }

    // TODO: this is only safe if we make sure the chomper doesn't actually store any state.
    let pred_interpreter = HalidePredicateInterpreter {
        chomper: chomper.clone(),
    };

    let halide_sort = Arc::new(EqSort {
        name: "HalideExpr".into(),
    });
    let dummy_sort = Arc::new(DummySort {
        sort: halide_sort.clone(),
        interpreter: Arc::new(pred_interpreter),
    });
    egraph.add_arcsort(halide_sort.clone()).unwrap();
    egraph.add_arcsort(dummy_sort).unwrap();
    init_egraph!(egraph, "../../tests/egglog/halide.egg");

    let initial_egraph = egraph.clone();

    let start_time = std::time::Instant::now();
    let rules = chomper.run_chompy(&mut egraph);
    let elapsed = start_time.elapsed();

    // output each rule to synth-rules.txt
    let mut file = std::fs::File::create("synth-rules.txt").unwrap();
    file.write_all(
        format!(
            "{} rules found in {} seconds\n\n",
            rules.len(),
            elapsed.as_secs_f64()
        )
        .as_bytes(),
    )
    .unwrap();
    for rule in &rules {
        match &rule.condition {
            Some((cond, _)) => {
                file.write_all(
                    format!("if {} then {} ~> {}\n\n", cond, rule.lhs, rule.rhs).as_bytes(),
                )
                .unwrap();
            }
            None => {
                file.write_all(format!("{} ~> {}\n\n", rule.lhs, rule.rhs).as_bytes())
                    .unwrap();
            }
        }
    }

    let handwritten_rules = get_validated_handwritten_rules();

    let mut rng = StdRng::seed_from_u64(0);

    // for each handwritten rule, see if it is derivable from the rules found by chompy.
    let mut found_rules_count = 0;
    let total_rules = handwritten_rules.len();
    for rule in handwritten_rules {
        let generalized = chomper.generalize_rule(&rule);
        let env = {
            if let Some((cond, _)) = &generalized.condition {
                halide::generate_environment(&cond)
            } else {
                HashMap::default()
            }
        };
        // halide::generate_environment(&(generalized.condition.clone().unwrap().0));
        // put random values in for non-conditioned variables.
        // union the variables in the lhs and rhs.
        let lhs_vars = halide::get_vars(&generalized.lhs);
        let rhs_vars = halide::get_vars(&generalized.rhs);

        let mut higher_lvl_env: HashMap<String, Vec<Option<i64>>> = HashMap::default();

        for var in lhs_vars.union(&rhs_vars) {
            if !higher_lvl_env.contains_key(var) {
                let num: i64 = rng.gen();
                let num = num % 10;
                higher_lvl_env.insert(var.clone(), vec![Some(num)]);
            }
        }

        let mut chomper = HalideChomper {
            env: higher_lvl_env.clone(),
        };

        println!("higher_lvl_env: {:?}", higher_lvl_env);

        let cond = if let Some((cond, _)) = &generalized.condition {
            Some((cond.clone(), vec![env]))
        } else {
            None
        };

        // give the derivability check a timeout of 10 seconds.
        //
        let timeout = std::time::Duration::from_secs(10);

        if chomper.check_derivability(
            &initial_egraph.clone(),
            &rules,
            &Rule {
                condition: cond,
                lhs: generalized.lhs.clone(),
                rhs: generalized.rhs.clone(),
            },
            true,
        ) {
            found_rules_count += 1;
        } else {
        }
    }

    println!("Found {}/{} rules", found_rules_count, total_rules);
}
