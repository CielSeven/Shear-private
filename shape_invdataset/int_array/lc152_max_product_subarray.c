#include "int_array_def.h"

int array_max_product_subarray(int *a, int n)
/*@ Require 0 <= n && n < INT_MAX && IntArray::full_shape(a, n)
    Ensure IntArray::full_shape(a, n)
*/
{
    int i;
    int best;
    int max_here;
    int min_here;
    int x;
    int p1;
    int p2;
    if (n <= 0) {
        return 0;
    }
    best = a[0];
    max_here = a[0];
    min_here = a[0];
    x = 0;
    p1 = 0;
    p2 = 0;
    i = 1;
    /*@ Inv
        exists v_i v_best v_max v_min v_x v_p1 v_p2,
        1 <= v_i && v_i <= n@pre &&
        a == a@pre && n == n@pre &&
        0 <= n@pre && n@pre < INT_MAX &&
        store(&i, int, v_i) * store(&best, int, v_best) *
        store(&max_here, int, v_max) * store(&min_here, int, v_min) *
        store(&x, int, v_x) * store(&p1, int, v_p1) * store(&p2, int, v_p2) *
        IntArray::full_shape(a@pre, n@pre)
    */
    while (i < n) {
        x = a[i];
        p1 = max_here * x;
        p2 = min_here * x;
        max_here = x;
        if (p1 > max_here) {
            max_here = p1;
        }
        if (p2 > max_here) {
            max_here = p2;
        }
        min_here = x;
        if (p1 < min_here) {
            min_here = p1;
        }
        if (p2 < min_here) {
            min_here = p2;
        }
        if (max_here > best) {
            best = max_here;
        }
        i = i + 1;
    }
    return best;
}
