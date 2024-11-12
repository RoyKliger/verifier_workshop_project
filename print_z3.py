from z3 import *
from sympy import symbols, And as SymAnd, Or as SymOr, Not as SymNot, Eq as SymEq
from sympy import latex, pretty


def z3_to_latex(expr):
  return latex(z3_to_sympy(expr))

def z3_to_sympy(expr):
  try:
    if is_int_value(expr):
      return int(str(expr))
    elif is_var(expr):
      return symbols(str(expr))
    elif is_const(expr):
      return symbols(str(expr))
    elif is_add(expr):
      return sum(z3_to_sympy(c) for c in expr.children())
    elif is_sub(expr):
      return z3_to_sympy(expr.arg(0)) - z3_to_sympy(expr.arg(1))
    elif is_mul(expr):
      result = z3_to_sympy(expr.arg(0))
      for child in expr.children()[1:]:
          result *= z3_to_sympy(child)
      return result
    elif is_eq(expr):
      return SymEq(z3_to_sympy(expr.arg(0)), z3_to_sympy(expr.arg(1)))
    elif is_lt(expr):
      return z3_to_sympy(expr.arg(0)) < z3_to_sympy(expr.arg(1))
    elif is_le(expr):
      return z3_to_sympy(expr.arg(0)) <= z3_to_sympy(expr.arg(1))
    elif is_gt(expr):
      return z3_to_sympy(expr.arg(0)) > z3_to_sympy(expr.arg(1))
    elif is_ge(expr):
      return z3_to_sympy(expr.arg(0)) >= z3_to_sympy(expr.arg(1))
    elif is_implies(expr):
      return SymOr(SymNot(z3_to_sympy(expr.arg(0))), z3_to_sympy(expr.arg(1)))
    elif is_and(expr):
      return SymAnd(*[z3_to_sympy(c) for c in expr.children()])
    elif is_or(expr):
      return SymOr(*[z3_to_sympy(c) for c in expr.children()])
    elif is_not(expr):
      return SymNot(z3_to_sympy(expr.arg(0)))
    elif is_quantifier(expr) and expr.is_forall():
      variables = [symbols(expr.var_name(i)) for i in range(expr.num_vars())]
      body = z3_to_sympy(expr.body())
      return ForAll(variables, body)
    else:
      raise NotImplementedError(f"Unknown expression type: {expr}")
  except Exception:
    return expr