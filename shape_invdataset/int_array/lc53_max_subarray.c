#include "int_array_def.h"

int array_max_subarray(int *a, int n)
/*@ With l
    Require 0 <= n && n < 1000 && IntArray::full(a, n, l) &&
            (forall (k: Z), (0 <= k && k < n) => -1000 <= l[k] && l[k] <= 1000)
    Ensure IntArray::full(a, n, l)
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
    /*@ Inv Assert
        exists v_best v_current,
        best == v_best && current == v_current &&
        1 <= i && i <= n@pre &&
        a == a@pre && n == n@pre &&
        0 <= n@pre && n@pre < 1000 &&
        -1000000 <= v_current && v_current <= 1000000 &&
        -1000000 <= v_best && v_best <= 1000000 &&
        (forall (k: Z), (0 <= k && k < n@pre) => -1000 <= l[k] && l[k] <= 1000) &&
        IntArray::full(a@pre, n@pre, l)
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
