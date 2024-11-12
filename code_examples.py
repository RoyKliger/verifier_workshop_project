

# Example 1 - Division with remainder

code1 = '''
q := 0;
r := a;
while r >= b do [a = (q*b) + r && (0 <= r && r <= a)] {
    r := r - b;
    q := q + 1;
} end
'''

pre1 = '''
a >= 0 && b > 0
'''

post1 = '''
r < b && a = (q*b) + r
'''