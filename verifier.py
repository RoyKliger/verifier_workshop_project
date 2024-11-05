from z3 import BoolRef
import z3

from commands.commands_wlp_hybrid import Command, AssignCommand, IfCommand, WhileCommand, SeqCommand, SkipCommand, get_logics_formula
# from old_parsing import parse_command



def solve(pre : BoolRef, command : Command, post: BoolRef):
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
    solve(z3.Int('x') == 0, AssignCommand(z3.Int('x'), z3.IntVal(1)), z3.Int('x') == 1)
    # pre, c, post = get_args()
    # solve(pre, c, post)

