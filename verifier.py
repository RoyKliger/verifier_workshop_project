from z3 import BoolRef
import z3

from commands import Command, AssignCommand, IfCommand, WhileCommand, SeqCommand, SkipCommand


def get_logics_formula(pre : BoolRef, command : Command, post : BoolRef) -> BoolRef:
    return command.verify(pre, post)

def solve(pre, command, post):
    print("\nExample verification problem:")
    print("\nPrecondition: ", pre)
    print("\nCommand: ", command)
    print("\nPostcondition: ", post, "\n")
    s = z3.Solver()
    formula = get_logics_formula(pre, command, post)
    print("Verification condition: ", formula)
    s.add(z3.Not(formula))
    if s.check() == z3.sat:
        print("The verification condition is not valid.")
        print(s.model())
        return False
    else:
        print("The verification condition is valid.")
        return True

def get_args():
    pre : BoolRef = get_formula_from_user()
    c : Command = get_command_form_user()
    post : BoolRef = get_formula_from_user()
    return pre, c, post
    
def get_formula_from_user() -> BoolRef:
    formula = input("Enter a formula: ")
    return z3.parse_smt2_string(formula)

def get_command_form_user() -> Command:
    command = input("Enter a command: ")
    return parse_command(command)

def parse_command(command: str) -> Command:
    return parse_command_rec(command.split())

def parse_command_rec(tokens) -> Command:
    if tokens[0] == "skip":
        return SkipCommand()
    elif tokens[0] == "if":
        cond = z3.parse_smt2_string(tokens[1])
        c1 = parse_command_rec(tokens[3:])
        c2 = parse_command_rec(tokens[3 + len(str(c1).split()) + 1:])
        return IfCommand(cond, c1, c2)
    elif tokens[0] == "while":
        cond = z3.parse_smt2_string(tokens[1])
        inv = z3.parse_smt2_string(tokens[3])
        body = parse_command_rec(tokens[5:])
        return WhileCommand(cond, body, inv)
    elif tokens[1] == ":=":
        var = z3.Int(tokens[0])
        expr = z3.parse_smt2_string(" ".join(tokens[2:]))
        return AssignCommand(var, expr)
    elif tokens[1] == ";":
        c1 = parse_command_rec(tokens[0])
        c2 = parse_command_rec(tokens[2:])
        mid = z3.Bool("mid")
        return SeqCommand(c1, c2, mid)
    else:
        raise Exception("Invalid command")

def simple_example():
    x = z3.Int('x')
    c = SeqCommand(
        AssignCommand(x, z3.IntVal(0)),
        WhileCommand(x < 5,
            AssignCommand(x, x + 1),
            x <= 5  # Add logical mid value
        ),
        x == 0  # Add logical mid value
    )
    post = x == 5
    solve(z3.BoolVal(True), c, post)

def simple_example2():
    x = z3.Int('x')
    y = z3.Int('y')
    z = z3.Int('z')
    c = SeqCommand(
        AssignCommand(x, z3.IntVal(0)),
        SeqCommand(
            AssignCommand(y, z3.IntVal(5)),
            SeqCommand(
                AssignCommand(z, z3.IntVal(10)),
                AssignCommand(z, y),
                z3.And(x == 0, y == 5, z == 10)
            ),
            z3.And(x == 0 , y == 5)  # Add logical mid value
        ),
        x == 0  # Add logical mid value
    )
    post = z3.And(x == 0, y == 5, z == 5)
    solve(z3.BoolVal(True), c, post)
   
def simple_example3():
    x = z3.Int('x')
    y = z3.Int('y')
    c = SeqCommand(
        AssignCommand(x, z3.IntVal(0)),
        IfCommand(x == 0,
            AssignCommand(y, z3.IntVal(5)),
            AssignCommand(y, z3.IntVal(10))
        ),
        x == 0  # Add logical mid value
    )
    post = z3.And(x == 0, y == 5)
    solve(z3.BoolVal(True), c, post) 
# Example verification problem
def simple_example0():
    
    pre : BoolRef
    pre = z3.BoolVal(True)
    x = z3.Int('x')
    y = z3.Int('y')
    z = z3.Int('z')
    c = SeqCommand(
        AssignCommand(x, z3.IntVal(0)),
        SeqCommand(
            AssignCommand(y, z3.IntVal(5)),
            SeqCommand(
                IfCommand(z3.Or(x == 0, y == 0),
                    AssignCommand(z, z3.IntVal(10)),
                    AssignCommand(z, z3.IntVal(20))
                ),
                WhileCommand(z > 0,
                    SeqCommand(
                        AssignCommand(x, x + 1),
                        AssignCommand(z, z - 1),
                        x == 9 - z
                    ),
                    z3.And(x <= 10, z >= 0, x == 10 - z)  # Add logical mid value
                ),
                z3.And(x == 0, z == 10, y == 5)
            ),
            z3.And(x == 0, y == 5)  # Add logical mid value
        ),
        x == 0  # Add logical mid value
    )
    post = z3.And(x == 10, y == 5, z == 0)
    print("Example verification problem:")
    print("\nPrecondition: ", pre)
    print("\nCommand: ", c)
    print("\nPostcondition: ", post, "\n")
    solve(pre, c, post)


if __name__ == "__main__":
    simple_example3()
    # pre, c, post = get_args()
    # solve(pre, c, post)

