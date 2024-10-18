use egglog::EGraph;
use ruler::{HashMap, HashSet, ValidationResult};

use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::str::FromStr;

use ruler::enumo::{Sexp, Workload};

pub type Constant<R> = <R as Chomper>::Constant;
pub type CVec<R> = Vec<Option<<R as Chomper>::Constant>>;

#[derive(Debug, PartialEq)]
pub struct Rule {
    pub condition: Option<Sexp>,
    pub lhs: Sexp,
    pub rhs: Sexp,
}
pub struct Rules {
    pub non_conditional: Vec<Rule>,
    pub conditional: Vec<Rule>,
}

pub trait Chomper {
    type Constant: Debug + Clone + Eq + Hash;

    fn get_eclass_term_map(&self, egraph: &mut EGraph) -> HashMap<i64, Sexp> {
        let mut outputs = egraph
            .parse_and_run_program(
                None,
                r#"
                (push)
                (run eclass-report 100)
                (pop)"#,
            )
            .unwrap()
            .into_iter()
            .peekable();

        let mut map = HashMap::default();

        while outputs.peek().is_some() {
            outputs.next().unwrap();
            let eclass = outputs.next().unwrap().to_string().parse::<i64>().unwrap();
            outputs.next().unwrap();
            let term = outputs.next().unwrap();
            map.insert(eclass, Sexp::from_str(&term).unwrap());
        }
        map
    }

    fn cvec_match(
        &mut self,
        egraph: &mut EGraph,
        mask_to_preds: &HashMap<Vec<bool>, HashSet<String>>,
    ) -> Rules {
        let mut result = Rules {
            non_conditional: vec![],
            conditional: vec![],
        };

        let eclass_term_map: HashMap<i64, Sexp> = self.get_eclass_term_map(egraph);
        let ec_keys: Vec<&i64> = eclass_term_map.keys().into_iter().collect();
        for i in 0..ec_keys.len() {
            let ec1 = ec_keys[i];
            let term1 = eclass_term_map.get(&ec1).unwrap();
            let cvec1 = self.interpret_term(&term1);
            if cvec1.iter().all(|x| x.is_none()) {
                // ignore cvecs which don't really matter
                continue;
            }
            for j in i + 1..ec_keys.len() {
                // TODO: check if we merged ec1 and ec2 in an earlier step?
                let ec2 = ec_keys[j];
                let term2 = eclass_term_map.get(ec2).unwrap();
                let cvec2 = self.interpret_term(&term2);

                if cvec2.iter().all(|x| x.is_none()) {
                    continue;
                }

                if cvec1 == cvec2 {
                    result.non_conditional.push(Rule {
                        condition: None,
                        lhs: term1.clone(),
                        rhs: term2.clone(),
                    });
                    result.non_conditional.push(Rule {
                        condition: None,
                        lhs: term2.clone(),
                        rhs: term1.clone(),
                    });
                } else {
                    // TODO: check if they are conditionally equal
                    // let is_equal
                    let mut has_meaningful_diff = false;
                    let mut matching_count = 0;
                    let mut same_vals: Vec<bool> = vec![];

                    for (cvec_1_el, cvec_2_el) in cvec1.iter().zip(cvec2.iter()) {
                        let has_match = cvec_1_el == cvec_2_el;
                        if !has_match {
                            if cvec_1_el.is_some() || cvec_2_el.is_some() {
                                has_meaningful_diff = true;
                            }
                        }
                        same_vals.push(has_match);
                        matching_count += 1;
                    }

                    if !has_meaningful_diff {
                        continue;
                    }

                    // filter out bad predicates that only match on one value
                    if matching_count < 2 {
                        continue;
                    }

                    // we want sufficient conditions, not sufficent and necessary.
                    let masks = mask_to_preds.keys().into_iter().filter(|mask| {
                        mask.iter()
                            .zip(same_vals.iter())
                            .all(|(mask_val, same_val)| {
                                // pred --> lhs == rhs
                                // pred OR not lhs == rhs
                                *mask_val || !(same_val)
                            })
                    });

                    for mask in masks {
                        let preds = mask_to_preds.get(mask).unwrap();
                        for pred in preds {
                            result.conditional.push(Rule {
                                condition: Some(Sexp::from_str(pred).unwrap()),
                                lhs: term1.clone(),
                                rhs: term2.clone(),
                            });
                            result.conditional.push(Rule {
                                condition: Some(Sexp::from_str(pred).unwrap()),
                                lhs: term2.clone(),
                                rhs: term1.clone(),
                            });
                        }
                    }
                }
            }
        }
        result
    }

    // applies the given productions to the old terms to get some new workload
    fn make_terms(&self, old_terms: &Workload) -> Workload;
    fn make_preds(&self) -> Workload;

    fn validate_rule(&self, rule: Rule) -> ValidationResult;
    fn interpret_term(&mut self, term: &ruler::enumo::Sexp) -> CVec<Self>;
    fn interpret_pred(&mut self, term: &ruler::enumo::Sexp) -> Vec<bool>;
}
