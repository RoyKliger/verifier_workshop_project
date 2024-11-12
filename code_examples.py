

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

# example 2 - simple increment using 2 varaibles

code2 = '''
x := 0; [x = 0 && y = 0]
while x < 10 do [x <= 10 && x = y] {
    x := x + 1;
    y := y + 1;
} end
'''

pre2 = '''
y = 0
'''

post2 = '''
y = 10
'''