from z3 import BoolRef
import z3

from commands.wlp import Command
from parser.our_parser import OurParser
from global_variables import loops

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

  global loops
  loops = False # Resetting before parsing new code

  parser = OurParser()

  parsed_pre = parser.parse_single_annotation(pre)
  parsed_code = parser.parse_code(code)
  parsed_post = parser.parse_single_annotation(post)

  return solve(parsed_pre, parsed_code, parsed_post)

def solve(pre : BoolRef, command : Command, post: BoolRef):

    # create solver
    s = z3.Solver()

    # Obtain the proper verification condition
    formula = z3.Implies(pre, command.calculate_wlp(post))
    print("Verification condition: ", formula)

    # Check if the negation of the vc is satisfiable
    s.add(z3.Not(formula))
    if s.check() == z3.sat:
        print("The verification condition is not valid.")
        print(s.model())
        return False, formula, s.model() # passed, formula, model
    else:
        print("The verification condition is valid.")
        return True, formula, None # passed, formula, model (None if no model)