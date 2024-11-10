from pyrsercomb import token, regex, fix, Parser, string, lift3, const, lift2
from __init__ import program, bool_expr, int_expr, statement
import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
from verifier import verify_code

test_code = """
for x := 0; x < 10; x := x + 1; do [x >= 0 && x <= 10] {
    y := y + 1;
}
"""

parsed_result = program.parse_or_raise(test_code)
print(parsed_result)


print(verify_code(test_code, "true", "y > 0"))