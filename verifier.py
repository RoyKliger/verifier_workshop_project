from z3 import BoolRef
import z3

from commands.commands import Command, HoareTriple
from parser.our_parser import OurParser
from global_variables import program_variables
from logger import log, clear_logs

def verify_code(code : str, pre : str, post : str, verification_type: str = "wlp"):
    """
    Solves the verification problem for the given code and annotations.
    Args:
        code (str): The string representation of the code.
        pre (str): The string representation of the pre-condition.
        post (str): The string representation of the post-condition.
    Returns:
        None
    """

    # global program_variables
    program_variables = set()

    clear_logs()

    parser = OurParser()

    parsed_pre = parser.parse_single_annotation(pre)
    parsed_code = parser.parse_code(code)
    parsed_post = parser.parse_single_annotation(post)

    return solve(parsed_pre, parsed_code, parsed_post, verification_type)

def solve(pre : BoolRef, command : Command, post: BoolRef, verification_type: str = "wlp"):

    # create solver
    s = z3.Solver()
    verification_set = get_verification_conditions(pre, command, post, verification_type)
    formula = z3.And(list(verification_set))

    # Check if the negation of the vc is satisfiable
    s.add(z3.Not(formula))
    if s.check() == z3.sat:
        log("The verification condition is not valid.")
        model = s.model()
        log(model)
        # check which formulas in the set are not satisfied
        unvalid_formulas = []
        for f in verification_set:
            s.add(z3.Not(f))
            if s.check() == z3.sat:
                unvalid_formulas.append(f)
                log(f"Unsatisfied formula: {f} with model {s.model()}")
        return False, formula, model
    else:
        log("The verification condition is valid.")
        return True, formula, None # passed, formula, model (None if no model)
        

def get_verification_conditions(pre : BoolRef, command : Command, post : BoolRef, verification_type: str) -> set[BoolRef]:
    if verification_type == "wlp":
        return {z3.Implies(pre, command.calculate_wlp(post))}
    elif verification_type == "hybrid":
        hoare_triple = HoareTriple(pre, command, post)
        return hoare_triple.verifyTriple()
    elif verification_type == "hoare_logic":
        return command.verify(pre, post)
    else:
        log("Invalid verification type")
        raise ValueError("Invalid verification type")
