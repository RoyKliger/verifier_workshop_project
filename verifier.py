from z3 import *

# Define the abstract syntax for the language
class Statement:
    pass

class Skip(Statement):
    def __str__(self):
        return "skip"

class Assign(Statement):
    def __init__(self, var, expr):
        self.var = var
        self.expr = expr

    def __str__(self):
        return f"{self.var} := {self.expr}"

class If(Statement):
    def __init__(self, cond, then_stmt, else_stmt):
        self.cond = cond
        self.then_stmt = then_stmt
        self.else_stmt = else_stmt

    def __str__(self):
        return f"if ({self.cond}) then {{ {self.then_stmt} }} else {{ {self.else_stmt} }}"

class While(Statement):
    def __init__(self, cond, body):
        self.cond = cond
        self.body = body

    def __str__(self):
        return f"while ({self.cond}) do {{ {self.body} }}"

# Helper functions for Hoare logic
def subst(expr, var, val):
    """Substitute var with val in expr"""
    if isinstance(expr, BoolRef):
        return expr.substitute({var: val})
    elif isinstance(expr, IntRef):
        return expr.substitute({var: val})
    return expr

# Hoare logic rules
def hoare_skip(pre, post):
    return pre == post

def hoare_assign(pre, var, expr, post):
    return subst(post, var, expr) == pre

def hoare_if(pre, cond, then_stmt, else_stmt, post):
    then_pre = And(pre, cond)
    else_pre = And(pre, Not(cond))
    return And(hoare(then_pre, then_stmt, post), hoare(else_pre, else_stmt, post))

def hoare_while(pre, cond, body, post):
    invariant = Bool("invariant")
    body_pre = And(invariant, cond)
    return And(
        Implies(pre, invariant),
        Implies(And(invariant, Not(cond)), post),
        hoare(body_pre, body, invariant)
    )

def hoare(pre, stmt, post):
    if isinstance(stmt, Skip):
        return hoare_skip(pre, post)
    elif isinstance(stmt, Assign):
        return hoare_assign(pre, stmt.var, stmt.expr, post)
    elif isinstance(stmt, If):
        return hoare_if(pre, stmt.cond, stmt.then_stmt, stmt.else_stmt, post)
    elif isinstance(stmt, While):
        return hoare_while(pre, stmt.cond, stmt.body, post)
    return False

# Example verification problem
def verify():
    x = Int('x')
    y = Int('y')

    pre = x == 0
    post = x == 1

    stmt = Assign(x, y + 1)

    s = Solver()
    s.add(Not(hoare(pre, stmt, post)))

    if s.check() == sat:
        print("The verification condition is not valid.")
    else:
        print("The verification condition is valid.")

if __name__ == "__main__":
    verify()

