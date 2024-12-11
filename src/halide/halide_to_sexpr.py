#!/usr/bin/python3

import ast
import re

REWRITE_FILES = ["out-c.txt", "out-nc.txt"]

OUTPUT_FILE = "rules.txt"

BAD_STR = "BAD"

def ast_to_sexpr(node):
    if type(node) == ast.Expr:
        return ast_to_sexpr(node.value)
    match type(node):
        case ast.Constant:
            assert type(node.value) == int
            return f"(Lit {node.value})"
        case ast.Name:
            if node.id == "false":
                return "(Lit 0)"
            elif node.id == "true":
                return "(Lit 1)"
            return f"(Var {node.id})"
        case ast.Call:
            call_to_op_str = {
                "max": "Max",
                "min": "Min",
                "select": "Select",
            }

            func = call_to_op_str.get(node.func.id, BAD_STR)

            return f"({func} {' '.join(map(ast_to_sexpr, node.args))})"
        case ast.UnaryOp:
            ast_to_op_str = {
                ast.USub: "Neg",
                ast.Not:  "Not",
            }
            op = ast_to_op_str[type(node.op)]
            return f"({op} {ast_to_sexpr(node.operand)})"
        case ast.BoolOp:
            boolop_to_op_str = {
                ast.And: "And",
                ast.Or:  "Or",
            }
            op = boolop_to_op_str[type(node.op)]
            return f"({op} {" ".join(map(ast_to_sexpr, node.values))})"
        case ast.BinOp:
            ast_to_op_str = {
                ast.Add:  "Add",
                ast.Sub:  "Sub",
                ast.Mult: "Mul",
                ast.Div:  "Div",
            }
            op = ast_to_op_str[type(node.op)]
            return f"({op} {ast_to_sexpr(node.left)} {ast_to_sexpr(node.right)})"
        case ast.Compare:
            ast_to_cmp_str = {
                ast.Eq:    "Eq",
                ast.NotEq: "Neq",
                ast.Lt:    "Lt",
                ast.LtE:   "Leq",
                # these are not in the Enumo subset of Halide eval
                # ast.Gt:    "Gt",
                # ast.GtE:   "Ge",
            }
            cmp = ast_to_cmp_str.get(type(node.ops[0]), BAD_STR)
            return f"({cmp} {ast_to_sexpr(node.left)} {ast_to_sexpr(node.comparators[0])})"
        # default case
        case _:
            raise Exception(f"unknown node: {type(node)}")

if __name__ == "__main__":
    with open(OUTPUT_FILE, "w+") as out:
        for file in REWRITE_FILES:
            with open(file, "r") as f:
                lines = f.readlines()
                total_rules = len(lines)
                added_rules_count = 0
                for line in lines:
                    line = line.replace("&&", "and").replace("||", "or").replace("!", "not ").replace("not =", "!=")
                    # split on "==>" or "if"
                    parts = list(map(lambda expr: ast_to_sexpr(ast.parse(re.sub(r"^\s+", "", expr)).body[0]),
                                re.split(r"==>|if ", line)))

                    rule = ";".join(parts)

                    if len(parts) != 2 and len(parts) != 3:
                        raise Exception(f"bad length: {len(parts)}")
                    elif BAD_STR not in rule:
                        added_rules_count += 1
                        out.write(f"{rule}\n")

                print(f"Added {added_rules_count} / {total_rules} rules from {file}")



