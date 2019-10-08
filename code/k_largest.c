/*d. ben knoble 2019.10.02*/

/*
 * PROGRAM
 *
 * k_largest
 *
 * Finds the kth largest element of an array of integers in O(n) time.
 *
 * Reads from standard input
 *
 * - k: which element to find
 * - n: number of elements
 * - n elements
 *
 * Nonmatching values are silently thrown away
 *
 * Outputs kth largest element to standard out.
 *
 * IMPLEMENTATION
 *
 * see kth_largest function
 */

#include <assert.h>
#include <err.h>
#include <stdio.h>
#include <stdlib.h>

int compare_longs(const void *a, const void *b) {
    long x = *(long *)a;
    long y = *(long *)b;
    if (x < y)
        return -1;
    else if (x > y)
        return 1;
    return 0;
}

void sort(long *a, size_t n) {
    qsort(a, n, sizeof(*a), compare_longs);
}

size_t med_index(size_t i) {
    return (size_t)(i/2);
}

void swap(long *a, long *b) {
    long t = *a;
    *a = *b;
    *b = t;
}

size_t partition(long pivot, long *array, size_t n_elts) {
    // find the pivot
    size_t pos = n_elts;
    for (size_t i = 0; i < n_elts; ++i) {
        if (array[i] == pivot) {
            pos = i;
            break;
        }
    }
    assert(pos < n_elts);
    swap(&array[pos], &array[n_elts-1]);
    // now pivot is at the end of the array

    size_t i = 0;
    for (size_t j = 0; j < n_elts; ++j) {
        if (array[j] < pivot) {
            swap(&array[j], &array[i]);
            ++i;
        }
    }
    swap(&array[i], &array[n_elts-1]);

    return i;
}

// may modify array
long kth_largest(size_t k, long *array, size_t n_elts) {
    size_t n_sublists = n_elts/5;
    if (n_sublists == 0) {
        sort(array, n_elts);
        return array[k];
    }
    long *medians = malloc(n_sublists * sizeof(*medians));
    if (medians == NULL) { err(1, NULL); }

    // sort sublists of 5 elements
    for (size_t i = 0; i < n_sublists; ++i) {
        size_t start = i*5;
        size_t left = n_elts - start < 5 ? n_elts - start : 5;
        sort(&array[start], left);
        if (left == 5)
            medians[i] = array[start + 3];
        else
            medians[i] = array[start + med_index(left)];
    }

    // determine pivot (possibly recursively)
    long pivot;
    if (n_sublists < 5)
        pivot = medians[med_index(n_sublists)];
    else
        pivot = kth_largest(med_index(n_sublists), medians, n_sublists);
    free(medians);

    // partition
    size_t rank = partition(pivot, array, n_elts);
    if (k < rank)
        return kth_largest(k, array, rank-1);
    else if (k > rank)
        return kth_largest(rank - k, &array[rank+1], n_elts-(rank+1));
    // else k == rank
    return pivot;
}

int main(int argc, char **argv) {
    size_t k;
    size_t n_elts;
    while (scanf("%zu", &k) != 1);
    while (scanf("%zu", &n_elts) != 1);
    long *array = malloc(n_elts * sizeof(*array));
    if (array == NULL) { err(1, NULL); }
    for (size_t i = 0; i < n_elts; ++i)
        while (scanf("%ld", &array[i]) != 1);

    printf("%ld\n", kth_largest(k, array, n_elts));
    free(array);
}
