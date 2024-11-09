from z3 import BoolRef, ExprRef
import z3


# Define the abstract syntax for the language
class Command:

    def vc(self, post : BoolRef) -> BoolRef:
        pass

    def calculate_wlp(self, post) -> BoolRef:
        pass

class SkipCommand(Command):
    def __str__(self):
        return "skip"
    
    def vc(self, post : BoolRef) -> BoolRef:
        return True
    
    def calculate_wlp(self, post) -> BoolRef:
        return post

class AssignCommand(Command):
    def __init__(self, var, expr):
        self.var = var
        self.expr = expr

    def __str__(self):
        return f"{self.var} := {self.expr}"
    
    def vc(self, post : BoolRef) -> BoolRef:
        print(f"\nPerforming AssignCommand.vc with inputs:\npost: {post} of type {type(post)}\nself.var: {self.var} of type {type(self.var)}\nself.expr: {self.expr} of type {type(self.expr)}\n")
        return True
    
    def calculate_wlp(self, post: BoolRef) -> BoolRef:
        print(f"\nPerforming AssignCommand.calculate_wlp with inputs:\npost: {post} of type {type(post)}\nself.var: {self.var} of type {type(self.var)}\nself.expr: {self.expr} of type {type(self.expr)}\n")
        return substitute(post, self.var, self.expr)

class IfCommand(Command):
    def __init__(self, cond: BoolRef, c1: Command, c2: Command):
        self.cond = cond
        self.c1 = c1
        self.c2 = c2

    def __str__(self):
        return f"if ({self.cond}) then {{ {self.c1} }} else {{ {self.c2} }}"

    def vc(self, post: BoolRef) -> BoolRef:
        print(f"\nPerforming IfCommand.vc with inputs:\npost: {post} of type {type(post)}\nself.cond: {self.cond} of type {type(self.cond)}\nself.c1: {self.c1} of type {type(self.c1)}\nself.c2: {self.c2} of type {type(self.c2)}\n")
        return z3.And(
            self.c1.vc(post),
            self.c2.vc(post)
        )
    
    def calculate_wlp(self, post : BoolRef) -> BoolRef:
        print(f"\nPerforming IfCommand.calculate_wlp with inputs:\npost: {post} of type {type(post)}\nself.cond: {self.cond} of type {type(self.cond)}\nself.c1: {self.c1} of type {type(self.c1)}\nself.c2: {self.c2} of type {type(self.c2)}\n")
        return z3.And(
            z3.Implies(self.cond, self.c1.calculate_wlp(post)),
            z3.Implies(z3.Not(self.cond), self.c2.calculate_wlp(post))
        )
    
        # z3.Or(
        #     z3.And(self.cond, self.c1.calculate_wlp(post)),
        #     z3.And(z3.Not(self.cond), self.c2.calculate_wlp(post))
        # )
    
class WhileCommand(Command):
    def __init__(self, cond: BoolRef, body: Command, inv: BoolRef):
        self.cond = cond
        self.body = body
        self.inv = inv

    def __str__(self):
        return f"while ({self.cond}) do {{ {self.body} }}"
    
    def vc(self, post: BoolRef) -> BoolRef:
        print(f"\nPerforming WhileCommand.vc with inputs:\npost: {post} of type {type(post)}\nself.cond: {self.cond} of type {type(self.cond)}\nself.body: {self.body} of type {type(self.body)}\nself.inv: {self.inv} of type {type(self.inv)}\n")
        
        # Assume invariant holds before entering the loop, to check it is well-established
        # invariant_initial_check = self.inv
        
        # Ensure that if the invariant holds and the condition is true, the body maintains the invariant
        invariant_preservation = z3.Implies(z3.And(self.inv, self.cond), self.body.calculate_wlp(self.inv))
        
        # Ensure that on loop exit, the invariant and the negated condition imply the postcondition
        loop_exit_condition = z3.Implies(z3.And(self.inv, z3.Not(self.cond)), post)
        
        # Combine all parts of the verification condition
        return z3.And(invariant_preservation, loop_exit_condition)
    
    # def vc(self, post: BoolRef) -> BoolRef:
    #     print(f"\nPerforming WhileCommand.vc with inputs:\npost: {post} of type {type(post)}\nself.cond: {self.cond} of type {type(self.cond)}\nself.body: {self.body} of type {type(self.body)}\nself.inv: {self.inv} of type {type(self.inv)}\n")
    #     return z3.And(
    #         z3.Implies(z3.And(self.inv, z3.Not(self.cond)), post),
    #         z3.Implies(z3.And(self.inv, self.cond), self.body.calculate_wlp(self.inv)),
    #     )
    
    def calculate_wlp(self, post : BoolRef) -> BoolRef:
        print(f"\nPerforming WhileCommand.calculate_wlp with inputs:\npost: {post} of type {type(post)}\nself.cond: {self.cond} of type {type(self.cond)}\nself.body: {self.body} of type {type(self.body)}\nself.inv: {self.inv} of type {type(self.inv)}\n")
        return self.inv

class SeqCommand(Command):
    def __init__(self, c1: Command, c2: Command, mid: BoolRef = None):
        self.c1 = c1
        self.c2 = c2
        self.mid = mid

    def __str__(self):
        return f"{self.c1}; {self.c2}"
    
    def vc(self, post : BoolRef) -> BoolRef:
        print(f"\nPerforming SeqCommand.vc with inputs:\npost: {post} of type {type(post)}\nself.c1: {self.c1} of type {type(self.c1)}\nself.c2: {self.c2} of type {type(self.c2)}\n")
        return z3.And(
            self.c1.vc(self.c2.calculate_wlp(post)),
            self.c2.vc(post)
        )        
    
    def calculate_wlp(self, post : BoolRef) -> BoolRef:
        print(f"\nPerforming SeqCommand.calculate_wlp with inputs:\npost: {post} of type {type(post)}\nself.c1: {self.c1} of type {type(self.c1)}\nself.c2: {self.c2} of type {type(self.c2)}\n")
        return self.c1.calculate_wlp(self.c2.calculate_wlp(post))

# Helper functions for Hoare logic
def substitute(formula : BoolRef, var, val) -> BoolRef:  
    """returns new formula with all occurences of var replaced by val"""
    print(f"Performing commands_wlp_hybrid.substitute with inputs:\nformula: {formula} of type {type(formula)}\nvar: {var} of type {type(var)}\nval: {val} of type {type(val)}")
    return z3.substitute(formula, (var, val))

def get_logics_formula(pre : BoolRef, command : Command, post : BoolRef) -> BoolRef:
    """returns the verification condition for the given pre-condition, command and post-condition"""
    return command.vc(pre, post)