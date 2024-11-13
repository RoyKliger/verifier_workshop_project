from z3 import BoolRef
import z3

from commands import Command, HoareTriple
from parser.our_parser import OurParser
from global_variables import program_variables
from logger import log, clear_logs

def verify_code(code : str, pre : str, post : str, verification_type: str = "wlp"):
    """
    Parses and verifies the given code based on the pre-condition and post-condition and type of verification.
    Args:
        code (str): The string representation of the code.
        pre (str): The string representation of the pre-condition.
        post (str): The string representation of the post-condition.
    Returns:
        Tuple[bool, BoolRef, Model, str]: A tuple containing the following elements:
            - A boolean indicating whether the verification was successful.
            - The formula representing the verification condition.
            - The model of the verification condition (None if no model exists).
            - A string containing a message (errors or other suggestions), empty if there isn't a mesage to send.
    """

    global program_variables
    program_variables = set()
    clear_logs()

    if verification_type not in ["wlp", "hybrid", "hoare_logic"]:
        log("Invalid verification type")
        return False, None, None, "ERROR: Invalid verification type. Please choose one of the following: 'wlp', 'hybrid', or 'hoare_logic'."
    
    parser = OurParser()
    bad_invariants = False
    message = ""

    try:   
        parsed_pre = parser.parse_single_annotation(pre)
        parsed_post = parser.parse_single_annotation(post)
    except Exception as e:
        log(f"An error occurred: {e}")
        return False, None, None, f"ERROR: pre-condition or post-condition is invalid: {e}"
    try:
        parsed_code = parser.parse_code(code)
        log(f"Parsed command: {parsed_code}")
        is_valid, formula, model, bad_invariants = solve(parsed_pre, parsed_code, parsed_post, verification_type)
    except Exception as e:
        log(f"An error occurred: {e}")
        return False, None, None, f"ERROR: {e}"
    
    if bad_invariants:
        message = "The system has recognized that the invariants are not strong enough. Please check the invariants."

    elif not is_valid:
        if verification_type == "wlp":
            message = "Consider strengthening the invariants. You may also try using the hybrid or hoare_logic verification methods by adding more annotations if required."
        elif verification_type == "hybrid":
            message = "Consider strengthening the invariants and annotations. You may also try using the hoare_logic verification method by adding annotations."
        else:
            message = "Consider strengthening the invariants and annotations."
    log("message: " + message)
    
    return is_valid, formula, model, message
    
def solve(pre : BoolRef, command : Command, post: BoolRef, verification_type: str = "wlp"):
    """
    Solves the verification problem for the given pre-condition, command, and post-condition.
    
    Args:
        pre (BoolRef): The pre-condition as a Z3 boolean formula.
        command (Command): The command to be verified.
        post (BoolRef): The post-condition as a Z3 boolean formula.
        verification_type (str): The type of verification to be used ("wlp", "hybrid", or "hoare_logic").
    
    Returns:
        Tuple[bool, BoolRef, Model, bool]: A tuple containing the following elements:
            - A boolean indicating whether the verification was successful.
            - The formula representing the verification condition.
            - The model of the verification condition (None if no model exists).
            - A boolean indicating whether the annotations might not be strong enough.
    """
    # create solver
    s = z3.Solver()
    verification_set = get_verification_conditions(pre, command, post, verification_type)
    formula = z3.And(list(verification_set))
    model = None
    is_valid = False
    bad_invariants = False

    # Check if the negation of the vc is satisfiable
    s.add(z3.Not(formula))
    if s.check() == z3.sat:
        log("The verification condition is not valid.")
        model = s.model()
        log(model)
        
        check_model = model.eval(pre, model_completion=True)
        if  z3.is_false(check_model):
            bad_invariants = True
        # check which formulas in the set are not satisfied
        unvalid_formulas = []
        for f in verification_set:
            s.add(z3.Not(f))
            if s.check() == z3.sat:
                unvalid_formulas.append(f)
                log(f"Unsatisfied formula: {f} with model {s.model()}")
        
    else:
        log("The verification condition is valid.")
        is_valid = True
        
    return is_valid, formula, model, bad_invariants  # passed, formula, model (None if no model)


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
