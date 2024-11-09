from z3 import BoolRef
import z3

from commands.commands_wlp_hybrid import Command, AssignCommand, IfCommand, WhileCommand, SeqCommand, SkipCommand, get_logics_formula
from parser.our_parser import OurParser
# from old_parsing import parse_command

def verify_code(code : str, pre : str, post : str):
  """
  Solves the verification problem for the given code and annotations.
  Args:
    code (str): The string representation of the code.
    pre (str): The string representation of the pre-condition.
    post (str): The string representation of the post-condition.
  Returns:
    None
  """

  parser = OurParser()

  parsed_pre = parser.parse_single_annotation(pre)
  parsed_code = parser.parse_code(code)
  parsed_post = parser.parse_single_annotation(post)

  print("Parsed pre-condition: ", parsed_pre)
  print("Parsed code: ", parsed_code)
  print("Parsed post-condition: ", parsed_post)
  return solve(parsed_pre, parsed_code, parsed_post)



def solve(pre : BoolRef, command : Command, post: BoolRef):

    # create solver
    s = z3.Solver()

    print("\n\nCALCULATING FORMULA\n\n")

    # obtain the proper verification condition
    formula = z3.And(
        z3.Implies(
            pre,
            command.calculate_wlp(post)
        ),
        command.vc(post)
    )

    print("Verification condition: ", formula)

    # check if the negation of the vc is satisfiable
    s.add(z3.Not(formula))
    if s.check() == z3.sat:
        print("The verification condition is not valid.")
        print(s.model())
        return False, formula, s.model()
    else:
        print("The verification condition is valid.")
        return True, formula, None


# def simple_example():
#     x = z3.Int('x')
#     c = SeqCommand(
#         AssignCommand(x, z3.IntVal(0)),
#         WhileCommand(x < 5,
#             AssignCommand(x, x + 1),
#             x <= 5  # Add logical mid value
#         ),
#         x == 0  # Add logical mid value
#     )
#     post = x == 5
#     solve(z3.BoolVal(True), c, post)

# def simple_example2():
#     x = z3.Int('x')
#     y = z3.Int('y')
#     z = z3.Int('z')
#     c = SeqCommand(
#         AssignCommand(x, z3.IntVal(0)),
#         SeqCommand(
#             AssignCommand(y, z3.IntVal(5)),
#             SeqCommand(
#                 AssignCommand(z, z3.IntVal(10)),
#                 AssignCommand(z, y),
#                 z3.And(x == 0, y == 5, z == 10)
#             ),
#             z3.And(x == 0 , y == 5)  # Add logical mid value
#         ),
#         x == 0  # Add logical mid value
#     )
#     post = z3.And(x == 0, y == 5, z == 5)
#     solve(z3.BoolVal(True), c, post)
   
# def simple_example3():
#     x = z3.Int('x')
#     y = z3.Int('y')
#     c = SeqCommand(
#         AssignCommand(x, z3.IntVal(0)),
#         IfCommand(x == 0,
#             AssignCommand(y, z3.IntVal(5)),
#             AssignCommand(y, z3.IntVal(10))
#         ),
#         x == 0  # Add logical mid value
#     )
#     post = z3.And(x == 0, y == 5)
#     solve(z3.BoolVal(True), c, post) 
# # Example verification problem
# def simple_example0():
    
#     pre : BoolRef
#     pre = z3.BoolVal(True)
#     x = z3.Int('x')
#     y = z3.Int('y')
#     z = z3.Int('z')
#     c = SeqCommand(
#         AssignCommand(x, z3.IntVal(0)),
#         SeqCommand(
#             AssignCommand(y, z3.IntVal(5)),
#             SeqCommand(
#                 IfCommand(z3.Or(x == 0, y == 0),
#                     AssignCommand(z, z3.IntVal(10)),
#                     AssignCommand(z, z3.IntVal(20))
#                 ),
#                 WhileCommand(z > 0,
#                     SeqCommand(
#                         AssignCommand(x, x + 1),
#                         AssignCommand(z, z - 1),
#                         x == 9 - z
#                     ),
#                     z3.And(x <= 10, z >= 0, x == 10 - z)  # Add logical mid value
#                 ),
#                 z3.And(x == 0, z == 10, y == 5)
#             ),
#             z3.And(x == 0, y == 5)  # Add logical mid value
#         ),
#         x == 0  # Add logical mid value
#     )
#     post = z3.And(x == 10, y == 5, z == 0)
#     print("Example verification problem:")
#     print("\nPrecondition: ", pre)
#     print("\nCommand: ", c)
#     print("\nPostcondition: ", post, "\n")
#     solve(pre, c, post)


if __name__ == "__main__":
    solve(z3.Int('x') != z3.Int('y'), IfCommand(z3.Int('x') == z3.Int('y'), AssignCommand(z3.Int('x'), z3.Int('y') + 1), AssignCommand(z3.Int('x'), z3.Int('y'))), z3.Int('x') == z3.Int('y'))
    # pre, c, post = get_args()
    # solve(pre, c, post)

