use std::str::FromStr;

use chompy::Rule;
use ruler::enumo::Sexp;

pub fn extract_halide_rules(src: &str) -> Vec<Rule> {
    let lines = src.lines();
    let mut results = vec![];
    for line in lines {
        let rule = parse_line(line);
        if let Some(rule) = rule {
            results.push(rule);
        }
    }
    results
}

fn parse_line(line: &str) -> Option<Rule> {
    // first, get the condition.
    let (rule, condition) = line.split_once("if").unwrap();
    // assert that there is only one ==> in the rule.
    assert_eq!(rule.matches("==>").count(), 1);
    // now, get the lhs/rhs from the rule, split on "==>".
    let (lhs, rhs) = rule.split_once("==>").unwrap();
    // now, parse the lhs and rhs.

    let condition = parse_expr(condition);
    let parsed_lhs = parse_expr(lhs);
    let parsed_rhs = parse_expr(rhs);
    Some(Rule {
        condition: Some((condition, vec![])),
        lhs: parsed_lhs,
        rhs: parsed_rhs,
    })
}

fn parse_expr(expr: &str) -> Sexp {
    Sexp::from_str("(xx)").unwrap()
}
