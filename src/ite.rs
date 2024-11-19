use std::{str::FromStr, sync::Arc};

use log::info;

use std::fmt::Debug;

use egglog::{
    ast::{Span, Symbol},
    constraint::{SimpleTypeConstraint, TypeConstraint},
    sort::Sort,
    ArcSort, PrimitiveLike,
};
use ruler::enumo::Sexp;

pub trait PredicateInterpreter: Debug + Send + Sync {
    fn interp_cond(&self, sexp: &Sexp) -> bool;
}

#[derive(Debug)]
pub struct DummySort {
    // the language that a condition will operate on
    pub sort: ArcSort,
    pub interpreter: Arc<dyn PredicateInterpreter>,
}

impl Sort for DummySort {
    fn name(&self) -> Symbol {
        "dummy".into()
    }

    fn as_arc_any(
        self: std::sync::Arc<Self>,
    ) -> std::sync::Arc<dyn std::any::Any + Send + Sync + 'static> {
        self
    }

    fn make_expr(
        &self,
        _egraph: &egglog::EGraph,
        _value: egglog::Value,
    ) -> (usize, egglog::ast::Expr) {
        (0, egglog::ast::Expr::lit_no_span(Symbol::from("dummy")))
    }

    fn register_primitives(self: std::sync::Arc<Self>, info: &mut egglog::TypeInfo) {
        info.add_primitive(Ite {
            name: "ite".into(),
            sort: self.sort.clone(),
            interpreter: self.interpreter.clone(),
        });
    }
}

pub struct Ite {
    name: Symbol,
    sort: Arc<dyn Sort>,
    interpreter: Arc<dyn PredicateInterpreter>,
}

// (ite pred_expr expr expr) -> expr.
// will evaluate to first expr if pred_expr = true (according to interpreter semantics), else the other expr.
impl PrimitiveLike for Ite {
    fn name(&self) -> Symbol {
        self.name
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        SimpleTypeConstraint::new(
            self.name(),
            vec![
                self.sort.clone(),
                self.sort.clone(),
                self.sort.clone(),
                self.sort.clone(),
            ],
            span.clone(),
        )
        .into_box()
    }

    fn apply(
        &self,
        values: &[egglog::Value],
        egraph: Option<&mut egglog::EGraph>,
    ) -> Option<egglog::Value> {
        let egraph = egraph.unwrap();
        let sexp = Sexp::from_str(&egraph.extract_value_to_string(values[0])).unwrap();

        info!("apply on {}", sexp);

        if self.interpreter.interp_cond(&sexp) {
            Some(values[1])
        } else {
            Some(values[2])
        }
    }
}

// idk why clippy complains about the two use statements below.
#[allow(unused_imports)]
pub mod tests {
    use super::*;
    use egglog::sort::EqSort;

    #[test]
    fn test_ite_create() {
        #[derive(Debug)]
        struct MathInterpreter;

        impl PredicateInterpreter for MathInterpreter {
            fn interp_cond(&self, sexp: &Sexp) -> bool {
                fn interp_internal(sexp: &Sexp) -> i64 {
                    match sexp {
                        Sexp::Atom(atom) => panic!("Unexpected atom: {}", atom),
                        Sexp::List(l) => {
                            if let Sexp::Atom(op) = &l[0] {
                                match op.as_str() {
                                    "Eq" => {
                                        let a = interp_internal(&l[1]);
                                        let b = interp_internal(&l[2]);
                                        if a == b {
                                            1
                                        } else {
                                            0
                                        }
                                    }
                                    "Mul" => interp_internal(&l[1]) * interp_internal(&l[2]),
                                    "Num" => l[1].to_string().parse().unwrap(),
                                    _ => panic!("Unexpected operator: {:?}", op),
                                }
                            } else {
                                panic!("Unexpected list operator: {:?}", l[0]);
                            }
                        }
                    }
                }

                interp_internal(sexp) == 1
            }
        }

        let math_sort = Arc::new(EqSort {
            name: "Math".into(),
        });
        let dummy_sort = Arc::new(DummySort {
            sort: math_sort.clone(),
            interpreter: Arc::new(MathInterpreter),
        });

        let mut egraph = egglog::EGraph::default();

        egraph.add_arcsort(math_sort.clone()).unwrap();
        egraph.add_arcsort(dummy_sort).unwrap();

        egraph
            .parse_and_run_program(
                None,
                r#"
                (function Num (i64) Math)
                (function Mul (Math Math) Math)
                (function Eq (Math Math) Math)

                (relation universe (Math))
                "#,
            )
            .unwrap();

        egraph
            .parse_and_run_program(
                None,
                r#"
                (rule
                    ((universe ?e))
                    ((union ?e (ite (Eq ?e (Num 1)) (Mul ?e ?e) ?e)))
                )

                "#,
            )
            .unwrap();

        egraph
            .parse_and_run_program(
                None,
                r#"
                (universe (Mul (Num 1) (Num 1)))
                (universe (Num 1))
                (universe (Num 2))
            "#,
            )
            .unwrap();

        egraph.parse_and_run_program(None, "(run 1000)").unwrap();

        egraph
            .parse_and_run_program(None, "(check (= (Mul (Num 1) (Num 1)) (Num 1)))")
            .unwrap();

        egraph
            .parse_and_run_program(None, "(fail (check (= (Mul (Num 2) (Num 2)) (Num 2))))")
            .unwrap();
    }
}