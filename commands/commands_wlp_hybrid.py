from z3 import BoolRef, ExprRef
import z3


# Define the abstract syntax for the language
class Command:
    def verify(self, pre: BoolRef, post: BoolRef) -> BoolRef:
        return z3.Implies(pre, self.calculate_wlp(post))

    def calculate_wlp(self, post) -> BoolRef:
        pass

class SkipCommand(Command):
    def __str__(self):
        return "skip"
    
    def calculate_wlp(self, post) -> BoolRef:
        return post

class AssignCommand(Command):
    def __init__(self, var, expr):
        self.var = var
        self.expr = expr

    def __str__(self):
        return f"{self.var} := {self.expr}"
    
    # def verify(self, pre, post) -> BoolRef:
    #     # print("\nASSIGN: ", z3.Implies(pre, substitute(post, self.var, self.expr)))
    #     # if z3.z3util.get_vars(self.expr) == []:
    #         # return z3.Implies(substitute(post, self.var, self.expr), post)
    #         # return z3.Implies(pre, z3.And(pre, self.var == self.expr))
    #     return z3.Implies(pre, substitute(post, self.var, self.expr))
    
    def calculate_wlp(self, post: BoolRef) -> BoolRef:
        return substitute(post, self.var, self.expr)

class IfCommand(Command):
    def __init__(self, cond: BoolRef, c1: Command, c2: Command):
        self.cond = cond
        self.c1 = c1
        self.c2 = c2

    def __str__(self):
        return f"if ({self.cond}) then {{ {self.c1} }} else {{ {self.c2} }}"

    # def verify(self, pre: BoolRef, post: BoolRef) -> BoolRef:
    #     then_pre = z3.And(pre, self.cond)
    #     else_pre = z3.And(pre, z3.Not(self.cond))
    #     # print("\nIF: ", z3.And(self.c1.verify(then_pre, post), self.c2.verify(else_pre, post)))
    #     return z3.And(self.c1.verify(then_pre, post), self.c2.verify(else_pre, post))
    
    def calculate_wlp(self, post : BoolRef) -> BoolRef:

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
    
    def verify(self, pre: BoolRef, post: BoolRef) -> BoolRef:
        body_pre = z3.And(self.inv, self.cond)
        return z3.And(
            z3.Implies(pre, self.inv),
            z3.Implies(z3.And(self.inv, z3.Not(self.cond)), post),
            self.body.verify(body_pre, self.inv)
        )
    
    def calculate_wlp(self, post : BoolRef) -> BoolRef:
        return self.inv

class SeqCommand(Command):
    def __init__(self, c1: Command, c2: Command, mid: BoolRef = None):
        self.c1 = c1
        self.c2 = c2
        self.mid = mid

    def __str__(self):
        return f"{self.c1}; {self.c2}"
    
    def verify(self, pre: BoolRef, post: BoolRef) -> BoolRef:
        
        # one of the commands is a while command
        if isinstance(self.c1, WhileCommand):
            
            # by hoare logic table for sequence command
            # we cannot use wlp
            return self.c1.verify(pre, self.c2.calculate_wlp(post))
        
        elif isinstance(self.c2, WhileCommand):

            # c2 is the last command
            # we can use the input post condition

            

        # both commands are not while commands
        # we can use wlp
        return super().verify(pre, post)
    
    def calculate_wlp(self, post : BoolRef) -> BoolRef:
        return self.c1.calculate_wlp(self.c2.calculate_wlp(post))

# Helper functions for Hoare logic
def substitute(formula: BoolRef, var, val) -> BoolRef:  
    """returns new formula with all occurences of var replaced by val"""
    print(f"Performing commands_wlp_hybrid.substitute with inputs:\nformula: {formula} of type {type(formula)}\nvar: {var} of type {type(var)}\nval: {val} of type {type(val)}")
    return z3.substitute(formula, (var, val))

def get_logics_formula(pre : BoolRef, command : Command, post : BoolRef) -> BoolRef:
    """returns the verification condition for the given pre-condition, command and post-condition"""
    return command.verify(pre, post)