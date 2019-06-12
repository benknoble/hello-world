#! /usr/bin/env python3

import math

_ts = [1 for _ in range(5)]


def recurrence(n):
    if n <= 5: return 1
    else: return 4 * recurrence(math.floor(n / 2) + 2) + n


def recurrence2(n):
    def index(n): return n - 1
    if 0 <= index(n) < len(_ts): return _ts[index(n)]
    _ts.insert(index(n), 4 * _ts[index(math.floor(n/2) + 2)] + n)
    return _ts[index(n)]


def main():
    ts = map(recurrence, range(1, 21))
    ts2 = map(recurrence2, range(1, 21))
    print(' n | T(n) | T_2(n)')
    for (i, (t1, t2)) in enumerate(zip(ts, ts2)):
        print('%2d | %4d | %4d' % (i+1, t2, t2))


if __name__ == '__main__':
    main()
