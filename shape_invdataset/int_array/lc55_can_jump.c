#include "int_array_def.h"

int array_can_jump(int *a, int n)
/*@
    Require 0 <= n && n < 1000000 && IntArray::full_shape(a, n)
    Ensure IntArray::full_shape(a, n)
*/
{
    int i;
    int farthest;
    i = 0;
    farthest = 0;
    /*@ Inv
        exists v_i v_farthest,
        0 <= v_i && v_i <= n@pre &&
        a == a@pre && n == n@pre &&
        0 <= n@pre && n@pre < 1000000 &&
        0 <= v_farthest && v_farthest <= n@pre + n@pre &&
        store(&i, int, v_i) * store(&farthest, int, v_farthest) *
        IntArray::full_shape(a@pre, n@pre)
    */
    while (i < n) {
        if (i > farthest) {
            return 0;
        }
        if (i + a[i] > farthest) {
            farthest = i + a[i];
        }
        i = i + 1;
    }
    return 1;
}
