from pyrsercomb import token, regex, fix, Parser, string, lift3, const, lift2
from __init__ import program, bool_expr, int_expr, statement

test_code = """
for x := 0; x < 10; x := x + 1; do {
    y := y + 1;
}
"""

parsed_result = program.parse_or_raise(test_code)
print(parsed_result)