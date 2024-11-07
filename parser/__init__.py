from pyrsercomb import token, regex, fix, Parser, string, lift3, const, lift2

from models import (
    Identifier, IntExpr, BinaryIntExpr, BinaryBoolExpr, BoolExpr, Comparison, Assignment, If, While,
    Statement)

lpar, rpar = token(string("(")), token(string(")"))
lbracket, rbracket = token(string("[")), token(string("]"))
lbrace, rbrace = token(string("{")), token(string("}"))
semicolon = token(string(";"))
assign = token(string(":="))

ident = token(regex(r"[a-z][A-Za-z0-9_]*"))[Identifier]
integer = token(regex(r"-?[0-9]+"))[int]
int_op = token(regex(r"[*/+-]"))


def def_int_expr(
        parser: Parser[str, IntExpr]
) -> Parser[str, IntExpr]:
    expr_with_parens = lpar >> parser << rpar
    expr = expr_with_parens ^ ident ^ integer
    binary = (expr & token(int_op) & expr)[
        lift3(BinaryIntExpr)
    ]
    return binary ^ expr


int_expr = fix(def_int_expr)

comparison_op = token(regex(r"(<|<=|>=|>|=|!=)"))
comparison = (int_expr & comparison_op & int_expr)[lift3(Comparison)]

false = token(string("false"))[const(False)]
true = token(string("true"))[const(True)]

boolean = true ^ false

bool_op = token(regex(r"(&&|\\|\\|)"))


def def_bool_expr(parser: Parser[str, BoolExpr]) -> Parser[str, BoolExpr]:
    expr_with_parens = lpar >> parser << rpar
    expr = expr_with_parens ^ boolean ^ comparison
    binary = (expr & token(bool_op) & expr)[
        lift3(BinaryBoolExpr)
    ]
    return binary ^ expr


bool_expr = fix(def_bool_expr)

skip = token(string("skip"))[const(None)] << semicolon
assignment = (ident << assign & int_expr)[lift2(Assignment)] << semicolon


def def_statement(parser: Parser[str, Statement]) -> Parser[str, Statement]:
    if_statement = (
            token(string("if")) >> bool_expr << token(string("then"))
            & parser << token(string("else"))
            & parser 
    )[lift3(If)]

    while_statement = (
            token(string("while")) >> bool_expr << token(string("do"))
            & token(lbracket >> bool_expr << rbracket)
            & parser
    )[lift3(While)]

    block = lbrace >> ~parser << rbrace

    return block ^ if_statement ^ while_statement ^ skip ^ assignment


statement = fix(def_statement)

program = ~statement

if __name__ == "__main__":
#     print(bool_expr.parse_or_raise("true;"))
#     print(program.parse_or_raise("skip;"))
#     print(program.parse_or_raise("x := (50 * y) + 7;"))
    print(program.parse_or_raise("""
    if x > y then { 
        x := (50 * y) + 7; 
        y := x;
    } else 
        skip; 
    """))
#     print(program.parse_or_raise("""
#     x := 0;
#     while x < 10 do {
#         x := x + 1;
#         y := y + 1;
#     } end
#     """))
