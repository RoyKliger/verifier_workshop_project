#import the parser
from parser import Statement, int_expr, bool_expr, program
from parser.models import Assignment, If, While, For
from commands.hybrid import Command, SkipCommand, AssignCommand, IfCommand, WhileCommand, SeqCommand
from parser.models import Identifier, IntExpr, BinaryIntExpr, BinaryBoolExpr, BoolExpr, Comparison, Assignment, If, While, Statement
from global_variables import program_variables

from z3 import BoolRef, ExprRef, Int, Bool
import z3

from typing import List


class OurParser():
            
    def from_parser_to_commands(self, parse_result : List[Statement]) -> Command:
        if parse_result is None or len(parse_result) == 0 or parse_result[0] is None:
            # Parse_result is None in the case of a skip command.
            return SkipCommand()
        first_statement = parse_result[0]
        mid = boolexpr_z3ify(first_statement.mid)
        mid = None if mid is False else mid
        if isinstance(first_statement, Assignment):
            # Add variable to set of program variables
            #program_variables = program_variables.add(first_statement.variable.name)
            # Recursively build the sequence of commands
            first_command = AssignCommand(intexpr_z3ify(first_statement.variable), intexpr_z3ify(first_statement.value))
            return first_command if len(parse_result) == 1 else SeqCommand(first_command, self.from_parser_to_commands(list(parse_result[1:])), mid)
        elif isinstance(first_statement, If):
            # Add variables to set of program variables
            #program_variables = program_variables.union(get_variables_from_boolexpr(first_statement.condition))
            # Recursively build the sequence of commands
            first_command = IfCommand(boolexpr_z3ify(first_statement.condition), self.from_parser_to_commands(first_statement.if_true), self.from_parser_to_commands(first_statement.if_false))
            return first_command if len(parse_result) == 1 else SeqCommand(first_command, self.from_parser_to_commands(list(parse_result[1:])), mid)
        # FIX THE FOLLOWING CODE. parse_result.invariant does not exist, we need to obtain the invariant from the annotations file
        elif isinstance(first_statement, While):
            # Add variables to set of program variables
            #program_variables = program_variables.union(get_variables_from_boolexpr(first_statement.condition))

            # Recursively build the sequence of commands
            first_command = WhileCommand(boolexpr_z3ify(first_statement.condition), self.from_parser_to_commands(first_statement.body), boolexpr_z3ify(first_statement.invariant))
            return first_command if len(parse_result) == 1 else SeqCommand(first_command, self.from_parser_to_commands(list(parse_result[1:])), mid)
        
        elif isinstance(first_statement, For):
            bodyCommand = self.from_parser_to_commands(first_statement.body)
            diffCommand = self.from_parser_to_commands([first_statement.diff])

            first_command = SeqCommand(
                self.from_parser_to_commands([first_statement.start]),
                WhileCommand(
                    boolexpr_z3ify(first_statement.end),
                    SeqCommand(
                        bodyCommand,
                        diffCommand
                    ),
                    # While loop invariant
                    boolexpr_z3ify(first_statement.invariant)
                    #diffCommand.substitute(boolexpr_z3ify(first_statement.end)
                )
            )
            return first_command if len(parse_result) == 1 else SeqCommand(first_command, self.from_parser_to_commands(list(parse_result[1:])), mid)
        
        # elif isinstance(parse_result, List["statement"]):
        #     c1 = from_parser_to_commands(parse_result[0])
        #     c2 = from_parser_to_commands(parse_result[1:])
        #     mid = get_annotations()
        #     return SeqCommand(c1, c2, mid)
        else:
            raise Exception("Invalid command, here is the command: ", parse_result)
        
    def add_default_mids(self, str: str) -> str:
        i = 0
        while i < len(str):
            if str[i] == ";":
                i += 1
                while i < len(str) and str[i] == " ":
                    i += 1
                if i >= len(str) or str[i] != "[":
                    str = str[:i] + "[false] " + str[i:]
                    i += len("[false] ")
            elif str[i:i+2] == "do":
                j = i + 2
                while j < len(str) and (str[j] == " " or str[j] == "\n"):
                    j += 1
                if j < len(str) and str[j] == "{" and (j == i + 2 or str[i+2:j].strip() != "["):
                    str = str[:j] + "[false] " + str[j:]
                    i = j + len("[false] ")
                else:
                    i = j
            elif str[i:i+3] == "end":
                j = i + 3
                while j < len(str) and str[j] == " ":
                    j += 1
                if j >= len(str) or str[j] != "[":
                    str = str[:j] + "[false] " + str[j:]
                    i = j + len("[false] ")
                else:
                    i = j
            else:
                i += 1

        print("MID STRING:", str)
        return str

    
    # str -> Command
    def parse_code(self, code_str : str) -> Command:
        """
        Parses a given code string and converts it into a sequence of commands.
        Args:
            code_str (str): The string representation of the code to be parsed.
        Returns:
            Command: A command object representing the parsed code. If the code is empty,
                    it returns a SkipCommand. If the code contains only one command,
                    it returns that command. Otherwise, it returns a SeqCommand
                    containing the sequence of commands.
        """

        code_str = self.add_default_mids(code_str)


        lst = program.parse_or_raise(code_str) # or program.parse(code_str)?

        print("Parsed code: ", lst)

        # code_str does not contain any commands i.e. it is empty
        if len(lst) == 0:
            return SkipCommand()
        
        # this is a separate case to avoid index out of range exception in c2
        if len(lst) == 1:
            return self.from_parser_to_commands([lst[0]])
        
        c1 = self.from_parser_to_commands([lst[0]])
        c2 = self.from_parser_to_commands(lst[1:])

        # recursively build the sequence of commands
        return SeqCommand(c1, c2, boolexpr_z3ify(lst[0].mid))


    def parse_single_annotation(self, annotation : str) -> BoolRef:
        global program_variables
        annotation_expr = boolexpr_z3ify(bool_expr.parse_or_raise(annotation))
        program_variables = program_variables.union(get_variables_from_boolexpr(annotation_expr))
        return annotation_expr

    

def get_variables_from_boolexpr(expr: BoolExpr) -> set:
    variables = set()
    if isinstance(expr, Identifier):
        variables.add(expr.name)
    elif isinstance(expr, Comparison):
        variables.update(get_variables_from_intexpr(expr.left))
        variables.update(get_variables_from_intexpr(expr.right))
    elif isinstance(expr, BinaryBoolExpr):
        variables.update(get_variables_from_boolexpr(expr.left))
        variables.update(get_variables_from_boolexpr(expr.right))
    return variables

def get_variables_from_intexpr(expr: IntExpr) -> set:
    variables = set()
    if isinstance(expr, Identifier):
        variables.add(expr.name)
    elif isinstance(expr, BinaryIntExpr):
        variables.update(get_variables_from_intexpr(expr.left))
        variables.update(get_variables_from_intexpr(expr.right))
    return variables


def intexpr_z3ify(expr : IntExpr) -> ExprRef | None:
    if isinstance(expr, Identifier):
        return Int(expr.name)
    elif isinstance(expr, int):
        return z3.IntVal(expr)
    elif isinstance(expr, BinaryIntExpr):
        left_z3 = intexpr_z3ify(expr.left)
        right_z3 = intexpr_z3ify(expr.right)
        if expr.op == "+":
            return left_z3 + right_z3
        elif expr.op == "-":
            return left_z3 - right_z3
        elif expr.op == "*":
            return left_z3 * right_z3
        elif expr.op == "/":
            return left_z3 / right_z3
    else: # This should never happen
        raise Exception("Invalid int expression")

def boolexpr_z3ify(expr : BoolExpr) -> BoolRef:
    if isinstance(expr, Identifier):
        return Bool(expr.name)
    elif isinstance(expr, bool):
        return z3.BoolVal(expr)
    elif isinstance(expr, Comparison):
        left_z3 = intexpr_z3ify(expr.left)
        right_z3 = intexpr_z3ify(expr.right)
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
        left_z3 = boolexpr_z3ify(expr.left)
        right_z3 = boolexpr_z3ify(expr.right)
        if expr.op == "&&":
            return z3.And(left_z3, right_z3)
        elif expr.op == "||":
            return z3.Or(left_z3, right_z3)
    else: # This should never happen
        raise Exception("Invalid bool expression")
