#! /usr/bin/env python3


def ins_sort_indices(A):
    F = list(range(len(A)))
    for j in range(len(A)):
        key = A[F[j]]
        i = j-1
        while i >= 0 and A[F[i]] > key:
            F[i+1] = F[i]
            i = i-1
        F[i+1] = j
    return F


def T(F):
    T = list(range(len(F)))
    for (i, f) in enumerate(F):
        T[f] = i
    return T


if __name__ == '__main__':
    As = [
            [1, 2, 3],
            [3, 5, 4],
            [2, 3, 1],
            ]
    for a in As:
        print('A=', a)
        indices = ins_sort_indices(a)
        t = T(indices)
        print('sorted(A)=', end='')
        for i in indices:
            print(a[i], end='')
        print('')
        print('F=', indices)
        print('T=', t)
        print('')
