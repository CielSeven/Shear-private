#include "int_array_def.h"

int array_max_subarray(int *a, int n)
/*@
    Require 0 <= n && n < 1000 && IntArray::full_shape(a, n)
    Ensure IntArray::full_shape(a, n)
*/
{
    int i;
    int best;
    int current;
    if (n <= 0) {
        return 0;
    }
    best = a[0];
    current = a[0];
    i = 1;
    /*@ Inv
        exists v_i v_best v_current,
        1 <= v_i && v_i <= n@pre &&
        a == a@pre && n == n@pre &&
        0 <= n@pre && n@pre < 1000 &&
        0 - 1000000 <= v_current && v_current <= 1000000 &&
        0 - 1000000 <= v_best && v_best <= 1000000 &&
        store(&i, int, v_i) * store(&best, int, v_best) *
        store(&current, int, v_current) *
        IntArray::full_shape(a@pre, n@pre)
    */
    while (i < n) {
        if (current < 0) {
            current = a[i];
        } else {
            current = current + a[i];
        }
        if (best < current) {
            best = current;
        }
        i = i + 1;
    }
    return best;
}
