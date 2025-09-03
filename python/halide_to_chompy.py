#!/usr/bin/env python3

from lark import Lark, Transformer
import argparse

grammar = r"""
?start: rule

rule: expr "==>" expr ("if" expr)?

?expr: expr "||" expr   -> or_
     | expr "&&" expr   -> and_
     | expr COMPOP expr -> cmp
     | "!" expr         -> not_
     | sum_expr

?sum_expr: sum_expr "+" term -> add
         | sum_expr "-" term -> sub
         | term

?term: term "*" factor -> mul
     | term "/" factor -> div
     | factor

?factor: "-" factor     -> neg
       | func_call
       | NUMBER        -> number
       | NAME          -> var
       | "(" expr ")"  -> parens

func_call: NAME "(" args? ")"
args: expr ("," expr)*

COMPOP: "==" | "!=" | "<" | "<=" | ">" | ">="

%import common.CNAME -> NAME
%import common.NUMBER
%import common.WS
%ignore WS
"""

class ToSExpr(Transformer):
    def neg(self, items):
        return f"(- {items[0]})"

    def add(self, items):
        return f"(+ {items[0]} {items[1]})"

    def sub(self, items):
        return f"(- {items[0]} {items[1]})"

    def mul(self, items):
        return f"(* {items[0]} {items[1]})"

    def div(self, items):
        return f"(/ {items[0]} {items[1]})"

    def or_(self, items):
        return f"(|| {items[0]} {items[1]})"

    def and_(self, items):
        return f"(&& {items[0]} {items[1]})"

    def not_(self, items):
        return f"(! {items[0]})"

    def cmp(self, items):
        op = items[1].value
        return f"({op} {items[0]} {items[2]})"

    def number(self, token):
        return token[0].value

    def var(self, token):
        return token[0].value

    def parens(self, items):
        return items[0]

    def func_call(self, items):
        name = items[0]
        args = items[1] if len(items) > 1 else []
        return f"({name} {' '.join(args)})"

    def args(self, items):
        return items

    def rule(self, items):
        lhs = items[0]
        rhs = items[1]
        cond = f" if {items[2]}" if len(items) == 3 else ""
        return f"{lhs} ==> {rhs}{cond}"


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Convert Halide expressions to S-expressions.")
    parser.add_argument("input", type=str, help="Input file containing Halide expressions.")
    parser.add_argument("output", type=str, help="Output file for S-expressions.")

    args = parser.parse_args()

    halide_parser = Lark(grammar, parser="lalr", transformer=ToSExpr())

    rules = []
    with open(args.input, "r") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            try:
                parsed = halide_parser.parse(line)
                rules.append(parsed)
            except Exception as e:
                print(f"Skipping line due to parse error: {line}\n  Error: {e}")

    with open(args.output, "w") as f:
        for rule in rules:
            f.write(rule + "\n")
