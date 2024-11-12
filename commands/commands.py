from z3 import BoolRef, ExprRef
import z3
from typing import List, Set

from logger import log
from global_variables import program_variables


# Define the abstract syntax for the language
class Command:  
    def verify(self, pre, post) -> Set[BoolRef]:
        pass
    
    def hybrid_verify(self, pre: BoolRef, post: BoolRef) -> Set[BoolRef]:
        pass

    def calculate_wlp(self, post) -> BoolRef:
        pass
    
    
class SkipCommand(Command):
    def __str__(self):
        return "skip"
    
    def verify(self, pre, post) -> Set[BoolRef]:
        return {z3.Implies(pre, post)}
    
    def hybrid_verify(self, pre: BoolRef, post: BoolRef) -> Set[BoolRef]:
        return {z3.Implies(pre, post)}
    
    def calculate_wlp(self, post) -> BoolRef:
        return post
    

class AssignCommand(Command):
    def __init__(self, var: ExprRef, expr: ExprRef):
        self.var = var
        self.expr = expr
        
        # A value was assigned to var, so it is a program variable
        program_variables.add(var)

    def __str__(self):
        return f"{self.var} := {self.expr}"
    
    def verify(self, pre : BoolRef, post : BoolRef) -> Set[BoolRef]:
        return {z3.Implies(pre, substitute(post, self.var, self.expr))}
    
    def hybrid_verify(self, pre: BoolRef, post: BoolRef) -> Set[BoolRef]:
        return {z3.Implies(pre, substitute(post, self.var, self.expr))}
    
    def calculate_wlp(self, post: BoolRef) -> BoolRef:
        return substitute(post, self.var, self.expr)

class IfCommand(Command):
    def __init__(self, cond: BoolRef, c1: Command, c2: Command):
        self.cond = cond
        self.c1 = c1
        self.c2 = c2

    def __str__(self):
        return f"if ({self.cond}) then {{ {self.c1} }} else {{ {self.c2} }}"

    def verify(self, pre: BoolRef, post: BoolRef) -> Set[BoolRef]:
        then_pre = z3.And(pre, self.cond)
        else_pre = z3.And(pre, z3.Not(self.cond))
        return self.c1.verify(then_pre, post).union(self.c2.verify(else_pre, post))
    
    def hybrid_verify(self, pre: BoolRef, post: BoolRef) -> Set[BoolRef]:
        then_pre = z3.And(pre, self.cond)
        else_pre = z3.And(pre, z3.Not(self.cond))
        then_hoare_triple = HoareTriple(then_pre, self.c1, post)
        else_hoare_triple = HoareTriple(else_pre, self.c2, post)
        then_vc = then_hoare_triple.verifyTriple()
        else_vc = else_hoare_triple.verifyTriple()
        return then_vc.union(else_vc)
           
    def calculate_wlp(self, post : BoolRef) -> BoolRef:
        return z3.And(
            z3.Implies(self.cond, self.c1.calculate_wlp(post)),
            z3.Implies(z3.Not(self.cond), self.c2.calculate_wlp(post))
        )
    
class WhileCommand(Command):
    def __init__(self, cond: BoolRef, body: Command, inv: BoolRef):
        self.cond = cond
        self.body = body
        self.inv = inv

    def __str__(self):
        return f"while ({self.cond}) do {{ {self.body} }}"
    
    def verify(self, pre: BoolRef, post: BoolRef) -> Set[BoolRef]:
        body_pre = z3.And(self.inv, self.cond)
        pre_inv = z3.Implies(pre, self.inv)
        post_inv = z3.Implies(z3.And(self.inv, z3.Not(self.cond)), post)
        body_verift_set = self.body.verify(body_pre, self.inv)
        return {pre_inv, post_inv}.union(body_verift_set)
        
    def hybrid_verify(self, pre: BoolRef, post: BoolRef) -> Set[BoolRef]:
        body_pre = z3.And(self.inv, self.cond)
        pre_inv = z3.Implies(pre, self.inv)
        post_inv = z3.Implies(z3.And(self.inv, z3.Not(self.cond)), post)
        body_pre = z3.And(self.inv, self.cond)
        body_hoare_triple = HoareTriple(body_pre, self.body, self.inv)
        body_vc = body_hoare_triple.verifyTriple()
        body_vc.add(pre_inv)
        body_vc.add(post_inv)
        return body_vc
    
    def calculate_wlp(self, post : BoolRef) -> BoolRef:
        global program_variables
        return z3.And(self.inv, z3.ForAll(list(program_variables), z3.And(z3.Implies(z3.And(self.inv, self.cond), self.body.calculate_wlp(self.inv)), z3.Implies(z3.And(z3.Not(self.cond), self.inv), post))))

class SeqCommand(Command):
    def __init__(self, c1: Command, c2: Command, mid: BoolRef | None = None):
        self.c1 = c1
        self.c2 = c2
        self.mid = mid

    def __str__(self):
        return f"{self.c1}; {self.c2} [{self.mid}]"
    
    def verify(self, pre: BoolRef, post: BoolRef) -> Set[BoolRef]:
        c1_verifications = self.c1.verify(pre, self.mid)
        c2_verifications = self.c2.verify(self.mid, post)
        return c1_verifications.union(c2_verifications)
    
    def hybrid_verify(self, pre: BoolRef, post: BoolRef) -> Set[BoolRef]:
        if self.mid is None:
            self.mid = z3.BoolVal(True)
            alert_no_mid_value()
            
        first_hoare_triple = HoareTriple(pre, self.c1, self.mid)
        second_hoare_triple = HoareTriple(self.mid, self.c2, post)
        first_vc = first_hoare_triple.verifyTriple()
        second_vc = second_hoare_triple.verifyTriple()
        return first_vc.union(second_vc)
        
    def calculate_wlp(self, post : BoolRef) -> BoolRef:
        return self.c1.calculate_wlp(self.c2.calculate_wlp(post))
    
            
# Helper functions for Hoare logic
def substitute(formula: BoolRef, var, val) -> BoolRef:  
    """returns new formula with all occurences of var replaced by val"""
    # log(f"Performing commands_wlp_hybrid.substitute with inputs:\nformula: {formula} of type {type(formula)}\nvar: {var} of type {type(var)}\nval: {val} of type {type(val)}")
    return z3.substitute(formula, (var, val))


class HoareTriple:
    def __init__(self, pre: BoolRef, command : Command, post: BoolRef, is_loop_free: bool = False):
        self.pre = pre
        self.command = command
        self.post = post
        self.is_loop_free = is_loop_free

    def __str__(self):
        return f"{{ pre: {self.pre} }} command: {self.command} {{ post: {self.post} }}"
    
    def __repr__(self):
        return self.__str__()
    
    def verifyTriple(self) -> Set[BoolRef]:
        formulas : Set[BoolRef] = set()
        chunks : List[HoareTriple] = split_to_chunks(self.pre, self.command, self.post) 
        log("Chunks:")
        for chunk in chunks:
            log(f"Chunk is {chunk} and is loop free is {chunk.is_loop_free}")
            if chunk.is_loop_free:
                formulas.add(verify_with_wlp(chunk.pre, chunk.command, chunk.post))
            else:
                formulas.update(verify_with_vc(chunk.pre, chunk.command, chunk.post))
        return formulas
        
        
def split_to_chunks(pre : BoolRef, command : Command, post : BoolRef) -> List[HoareTriple]:
        """Returns a list of HoareTriples that are contained in this HoareTriple where each HoareTriple represents a chunk of code 
            that is loop free or contains a loop, plus a logical mid value that is True between the chunks.
            We assume that between each chunk there is a logical mid value that is True       
        """
        chunks = []
        is_loop_stopper = lambda command : isinstance(command, WhileCommand) or (isinstance(command, IfCommand) and is_containing_loop(command)) or (isinstance(command, SeqCommand) and (isinstance(command.c1, WhileCommand) or (isinstance(command.c1, IfCommand) and is_containing_loop(command.c1))))
        
        def helper(pre: BoolRef, command: Command, post: BoolRef):
            
            first_chunk_commands = []
            current_command = command
            
            if isinstance(command, WhileCommand):
                chunks.append(HoareTriple(pre, command, post, False))
                return
            elif not isinstance(command, SeqCommand):
                chunks.append(HoareTriple(pre, command, post, True))
                return
                
            while isinstance(current_command, SeqCommand):
                
                if isinstance(current_command.c1, WhileCommand):
                    mid = check_and_assign_mid(current_command.mid)                   
                    chunks.append(HoareTriple(pre, current_command.c1, mid, False))
                    helper(mid, current_command.c2, post)
                    break
                                       
                elif isinstance(current_command.c1, IfCommand):
                    if is_containing_loop(current_command.c1):
                        mid = check_and_assign_mid(current_command.mid)                   
                        chunks.append(HoareTriple(pre, current_command.c1, mid, False))
                        helper(mid, current_command.c2, post)
                        break
                    
                elif is_loop_stopper(current_command.c2):
                    first_chunk_commands.append(current_command.c1)
                    packed_command = pack_command(first_chunk_commands)
                    mid = check_and_assign_mid(current_command.mid)                   
                    chunks.append(HoareTriple(pre, packed_command, mid, True))
                    helper(mid, current_command.c2, post)
                    break
                        
                else:
                    first_chunk_commands.append(current_command.c1)
                    current_command = current_command.c2       
            return
                
        helper(pre, command, post)
        return chunks    

def pack_command(commands : List[Command]) -> Command:
    if len(commands) == 0:
        return SkipCommand()
    if len(commands) == 1:
        return commands[0]
    return SeqCommand(commands[0], pack_command(commands[1:]))

def is_containing_loop(command : Command) -> bool:
    if isinstance(command, WhileCommand):
        return True
    if isinstance(command, SeqCommand):
        return is_containing_loop(command.c1) or is_containing_loop(command.c2)
    if isinstance(command, IfCommand):
        return is_containing_loop(command.c1) or is_containing_loop(command.c2)
    return False

def verify_with_vc(pre : BoolRef, command : Command, post : BoolRef) -> Set[BoolRef]:
    return command.hybrid_verify(pre, post)

def verify_with_wlp(pre : BoolRef, command : Command, post : BoolRef) -> BoolRef:
    return z3.Implies(pre, command.calculate_wlp(post))
    
def alert_no_mid_value():
    log("No mid value was provided for the SeqCommand. The verification may not be correct!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
    
def check_and_assign_mid(mid : BoolRef | None) -> BoolRef:
    if mid is None:
        mid = z3.BoolVal(True)
        alert_no_mid_value()
    return mid

def solve(pre : BoolRef, command : Command, post: BoolRef):

    # create solver
    s = z3.Solver()

    # log(command)
    # obtain the proper verification condition
    hoare_triple = HoareTriple(pre, command, post)
    formula_set = hoare_triple.verifyTriple()
    formula = z3.And(list(formula_set))

    # Check if the negation of the vc is satisfiable
    s.add(z3.Not(formula))
    if s.check() == z3.sat:
        log("The verification condition is not valid.")
        model = s.model()
        log(model)
        # check which formulas in the set are not satisfied
        unvalid_formulas = []
        for f in formula_set:
            s.add(z3.Not(f))
            if s.check() == z3.sat:
                unvalid_formulas.append(f)
                log(f"Unsatisfied formula: {f}")
                log(s.model())
        return False, formula, model
    else:
        log("The verification condition is valid.")
        return True, formula, None


if __name__ == "__main__":
    # Example 1: Skip Command
    log("Example 1: Skip Command")
    pre = z3.Bool(True)
    post = z3.Bool(True)
    skip_command = SkipCommand()
    log(f"Hoare Triple: {{ pre: {pre} }} \ncommand: {skip_command} \n{{ post: {post} }}")
    log(f"Verification Conditions: {solve(pre, skip_command, post)}")

    # Example 2: Assign Command
    log("\nExample 2: Assign Command")
    x = z3.Int('x')
    expr = z3.IntVal(5)
    assign_command = AssignCommand(x, expr)
    pre_assign = x == 0
    post_assign = x == 5
    log(f"Hoare Triple: {{ pre: {pre_assign} }} \ncommand: {assign_command} \n{{ post: {post_assign} }}")
    log(f"Verification Conditions: {solve(pre_assign, assign_command, post_assign)}")

    # Example 3: If Command
    log("\nExample 3: If Command")
    cond = x > 0
    assign_command1 = AssignCommand(x, z3.IntVal(10))
    assign_command2 = AssignCommand(x, z3.IntVal(20))
    if_command = IfCommand(cond, assign_command1, assign_command2)
    pre_if = z3.And(x >= 0, x <= 100)  # Example precondition
    post_if = z3.Or(x == 10, x == 20)  # Example postcondition
    log(f"Hoare Triple: {{ pre: {pre_if} }} \ncommand: {if_command} \n{{ post: {post_if} }}")
    log(f"Verification Conditions: {solve(pre_if, if_command, post_if)}")

    # Example 4: While Command with mid values
    log("\nExample 4: While Command with mid values")
    y = z3.Int('y')
    inv = z3.And(y >= 0, y <= 10)  # Example invariant
    cond = y > 0  # Example condition
    body_command = AssignCommand(y, y - 1)
    while_command = WhileCommand(cond, body_command, inv)
    pre_while = y == 10  # Example precondition
    mid_pre_while = y == 10  # Example mid value
    mid_post_while = y == 0  # Example mid value
    post_while = y == 0  # Example postcondition
    seq_command = SeqCommand(AssignCommand(x, z3.IntVal(0)), SeqCommand(while_command, AssignCommand(x, y), mid_post_while), mid_pre_while)
    log(f"Hoare Triple: {{ pre: {pre_while} }} \ncommand: {seq_command} \n{{ post: {post_while} }}")
    log(f"Verification Conditions: {solve(pre_while, seq_command, post_while)}")

    # Example 5: Sequence Command
    log("\nExample 5: Sequence Command")
    seq_command = SeqCommand(AssignCommand(x, z3.IntVal(1)), SeqCommand(AssignCommand(y, z3.IntVal(2)), AssignCommand(x, x + y)))
    pre_seq = z3.And(x == 0, y == 0)  # Example precondition
    post_seq = x == 3  # Example postcondition
    log(f"Hoare Triple: {{ pre: {pre_seq} }} \ncommand: {seq_command} \n{{ post: {post_seq} }}")
    log(f"Verification Conditions: {solve(pre_seq, seq_command, post_seq)}")

