#include "int_array_def.h"

void array_merge_sorted(int *a, int m, int *b, int n)
/*@ Require 0 <= m && 0 <= n && m + n < INT_MAX &&
            IntArray::full_shape(a, m + n) * IntArray::full_shape(b, n)
    Ensure IntArray::full_shape(a, m + n) * IntArray::full_shape(b, n)
*/
{
    int i;
    int j;
    int k;
    i = m - 1;
    j = n - 1;
    k = m + n - 1;
    /*@ Inv Assert
        -1 <= i && i < m@pre && -1 <= j && j < n@pre &&
        k == i + j + 1 &&
        a == a@pre && b == b@pre && m == m@pre && n == n@pre &&
        0 <= m@pre && 0 <= n@pre && m@pre + n@pre < INT_MAX &&
        IntArray::full_shape(a@pre, m@pre + n@pre) *
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
