#include "int_array_def.h"

int array_jump_min_steps(int *a, int n)
/*@
    Require 0 <= n && n < 1000000 && IntArray::full_shape(a, n)
    Ensure IntArray::full_shape(a, n)
*/
{
    int i;
    int jumps;
    int current_end;
    int farthest;
    if (n <= 1) {
        return 0;
    }
    jumps = 0;
    current_end = 0;
    farthest = 0;
    i = 0;
    /*@ Inv
        exists v_i v_jumps v_current_end v_farthest,
        0 <= v_i && v_i <= n@pre - 1 &&
        a == a@pre && n == n@pre &&
        0 <= n@pre && n@pre < 1000000 &&
        0 <= v_jumps && v_jumps <= n@pre &&
        0 <= v_current_end && v_current_end <= n@pre + n@pre &&
        0 <= v_farthest && v_farthest <= n@pre + n@pre &&
        store(&i, int, v_i) * store(&jumps, int, v_jumps) *
        store(&current_end, int, v_current_end) * store(&farthest, int, v_farthest) *
        IntArray::full_shape(a@pre, n@pre)
    */
    while (i < n - 1) {
        if (i + a[i] > farthest) {
            farthest = i + a[i];
        }
        if (i == current_end) {
            jumps = jumps + 1;
            current_end = farthest;
            if (current_end >= n - 1) {
                return jumps;
            }
        }
        i = i + 1;
    }
    return jumps;
}
