from pyrsercomb import token, regex, fix, Parser, string, lift3, const, lift2
from __init__ import program, bool_expr, int_expr, statement
import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
from verifier import verify_code

test_code = """
x := 0; [x = 0]
y := 0; [y = 0 && x = 0]
"""

parsed_result = program.parse_or_raise(test_code)
print(parsed_result)


print(verify_code(test_code, "true", "x >= 0"))