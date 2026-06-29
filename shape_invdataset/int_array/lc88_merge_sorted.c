#include "int_array_def.h"

void array_merge_sorted(int *a, int m, int *b, int n)
/*@ With total
    Require 0 <= m && 0 <= n && total == m + n && total < INT_MAX &&
            IntArray::full_shape(a, total) * IntArray::full_shape(b, n)
    Ensure IntArray::full_shape(a, total) * IntArray::full_shape(b, n)
*/
{
    int i;
    int j;
    int k;
    i = m - 1;
    j = n - 1;
    k = m + n - 1;
    /*@ Inv
        exists v_i v_j v_k v_total,
        0 - 1 <= v_i && v_i < m@pre && 0 - 1 <= v_j && v_j < n@pre &&
        v_k == v_i + v_j + 1 &&
        v_total == m@pre + n@pre &&
        a == a@pre && b == b@pre && m == m@pre && n == n@pre &&
        0 <= m@pre && 0 <= n@pre && v_total < INT_MAX &&
        store(&i, int, v_i) * store(&j, int, v_j) * store(&k, int, v_k) *
        IntArray::full_shape(a@pre, v_total) *
        IntArray::full_shape(b@pre, n@pre)
    */
    while (j >= 0) {
        if (i >= 0 && a[i] > b[j]) {
            a[k] = a[i];
            i = i - 1;
        } else {
            a[k] = b[j];
            j = j - 1;
        }
        k = k - 1;
    }
}
