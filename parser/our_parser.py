#import the parser
from re import L, S
from parser import Statement, int_expr, bool_expr
from parser.models import Assignment, If, While
from commands.commands import Command, SkipCommand, AssignCommand, IfCommand, WhileCommand, SeqCommand
from pyrsercomb import token, regex, fix, Parser, string, lift3, const, lift2
from models import Identifier, IntExpr, BinaryIntExpr, BinaryBoolExpr, BoolExpr, Comparison, Assignment, If, While, Statement

from z3 import BoolRef, ExprRef, Implies, And, Not, Int, Bool, substitute
import z3

from typing import List

parser = Parser()

def from_parser_to_commands(parse_result : Statement) -> Command:
    if isinstance(parse_result, ):
        return SkipCommand()
    elif isinstance(parse_result, Assignment):
        return AssignCommand(parse_result.variable, from_int_expr_to_z3(parse_result.expression))
    elif isinstance(parse_result, If):
        return IfCommand(from_bool_expr_to_z3(parse_result.condition), from_parser_to_commands(parse_result.then_branch), from_parser_to_commands(parse_result.else_branch))
    elif isinstance(parse_result, While):
        return WhileCommand(from_bool_expr_to_z3(parse_result.condition), from_parser_to_commands(parse_result.body), from_bool_expr_to_z3(parse_result.invariant))
    # elif isinstance(parse_result, List["statement"]):
    #     c1 = from_parser_to_commands(parse_result[0])
    #     c2 = from_parser_to_commands(parse_result[1:])
    #     mid = get_annotations()
    #     return SeqCommand(c1, c2, mid)
    else:
        raise Exception("Invalid command")
    
    
def file_to_string(file):
    with open(file, "r") as f:
        return f.read()

# file : str -> Statement    
def parse_file(file) -> Statement:
    file_content = file_to_string(file)
    return parser.parse(file_content) # or parser.parse_or_raise(file_content)

def parse_annotations(annotations_file : str) -> List[BoolRef]:
    with open(annotations_file, "r") as f:
        return [z3.Bool(line) for line in f.readlines()]

def from_int_expr_to_z3(expr : IntExpr) -> ExprRef: 
    if isinstance(expr, Identifier):
        return Int(expr.name)
    elif isinstance(expr, int):
        return Int(expr)
    elif isinstance(expr, BinaryIntExpr):
        left_z3 = from_int_expr_to_z3(expr.left)
        right_z3 = from_int_expr_to_z3(expr.right)
        if expr.op == "+":
            return left_z3 + right_z3
        elif expr.op == "-":
            return left_z3 - right_z3
        elif expr.op == "*":
            return left_z3 * right_z3
        elif expr.op == "/":
            return left_z3 / right_z3
    else:
        raise Exception("Invalid int expression")

def from_bool_expr_to_z3(expr : BoolExpr) -> BoolRef:
    if isinstance(expr, Identifier):
        return Bool(expr.name)
    elif isinstance(expr, bool):
        return z3.BoolVal(expr)
    elif isinstance(expr, Comparison):
        left_z3 = from_int_expr_to_z3(expr.left)
        right_z3 = from_int_expr_to_z3(expr.right)
        if expr.op == "<":
            return left_z3 < right_z3
        elif expr.op == "<=":
            return left_z3 <= right_z3
        elif expr.op == ">":
            return left_z3 > right_z3
        elif expr.op == ">=":
            return left_z3 >= right_z3
        elif expr.op == "=":
            return left_z3 == right_z3
        elif expr.op == "!=":
            return left_z3 != right_z3
    elif isinstance(expr, BinaryBoolExpr):
        left_z3 = from_bool_expr_to_z3(expr.left)
        right_z3 = from_bool_expr_to_z3(expr.right)
        if expr.op == "&&":
            return z3.And(left_z3, right_z3)
        elif expr.op == "||":
            return z3.Or(left_z3, right_z3)
    else:
        raise Exception("Invalid bool expression")

def get_annotations() -> BoolRef:
    pass