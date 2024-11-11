from z3 import BoolRef
import z3

from commands.commands_wlp_hybrid import Command
from parser.our_parser import OurParser

from flask import Flask, request, jsonify, send_from_directory

app = Flask(__name__)


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

  
  parsed_code = parser.parse_code(code)
  parsed_pre = parser.parse_single_annotation(pre)
  parsed_post = parser.parse_single_annotation(post)

  ret_value = solve(parsed_pre, parsed_code, parsed_post)

  return {
      'success': ret_value[0],
      'formula': str(ret_value[1]),
      'model': None if ret_value[2] is None else str(ret_value[2])
  }

def solve(pre : BoolRef, command : Command, post: BoolRef):

    # create solver
    s = z3.Solver()

    print(command)
    # obtain the proper verification condition
    formula = z3.Implies(pre, command.calculate_wlp(post))
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

# Serve index.html from the current directory
@app.route('/')
def index():
    return send_from_directory('.', 'index.html')  # '.' refers to the current directory

# Verification route
@app.route('/verify', methods=['POST'])
def verify_server():
    data = request.get_json()
    code = data['code']
    pre_condition = data['preCondition']
    post_condition = data['postCondition']

    # Call your verification logic here (e.g., verify_code function)
    result = verify_code(code, pre_condition, post_condition)
    return jsonify(result)

if __name__ == "__main__":
    app.run(debug=True)