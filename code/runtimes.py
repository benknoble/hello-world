#! /usr/bin/env python3
import math

ns = [1000000.0,
      60000000.0,
      3600000000.0,
      86400000000.0,
      2592000000000.0,
      31536000000000.0]


def solve_factorial(n):
    i = 1
    while math.factorial(i) <= n: i += 1
    return i-1


def solve_nlgn(n):
    def nlgn(i): return i * math.log2(i)
    def nlgn_prime(i): return math.log2(i) + 1/math.log(2)
    a = n / math.log2(n)
    for _ in range(2):
        a = a - (nlgn(a) - n)/nlgn_prime(a)
    return a


print('factorial')
print(list(map(solve_factorial, ns)))
# => [9, 11, 12, 13, 15, 16, 17]

print('nlgn')
print(list(map(int, map(solve_nlgn, ns))))
# => [62746, 2801417, 133378060, 2755147525, 71870856556, 797633894364]
