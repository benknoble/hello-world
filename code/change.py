#! /usr/bin/env python3


def min_bills(val, denominations):
    # build table m
    m = [
            [0 for _ in range(len(denominations)+1)]
            for _ in range(val+1)
            ]
    for j in range(val+1):
        m[j][0] = j
    for j in range(1, val+1):
        for i in range(1, len(denominations)+1):
            if j == denominations[i-1]:
                m[j][i] = 1
            elif denominations[i-1] > j:
                m[j][i] = m[j][i-1]
            else:  # denominations[i-1] < j
                m[j][i] = min(
                        m[j][i-1],
                        m[j-denominations[i-1]][i] + 1
                        )
    return m[val][len(denominations)]


def main():
    denominations = [
            1,
            4,
            7,
            13,
            28,
            52,
            91,
            365
            ]
    ks = [
            12,  # => 3
            455  # => 5
            ]
    for k in ks:
        print(min_bills(k, denominations))


if __name__ == '__main__':
    main()
