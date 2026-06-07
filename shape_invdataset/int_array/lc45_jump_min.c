#include "int_array_def.h"

int array_jump_min_steps(int *a, int n)
/*@ With l
    Require 0 <= n && n < 1000000 && IntArray::full(a, n, l) &&
            (forall (k: Z), (0 <= k && k < n) => 0 <= l[k] && l[k] <= n)
    Ensure IntArray::full(a, n, l)
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
    /*@ Inv Assert
        exists v_jumps v_current_end v_farthest,
        jumps == v_jumps && current_end == v_current_end && farthest == v_farthest &&
        0 <= i && i <= n@pre - 1 &&
        a == a@pre && n == n@pre &&
        0 <= n@pre && n@pre < 1000000 &&
        0 <= v_jumps && v_jumps <= n@pre &&
        0 <= v_current_end && v_current_end <= 2 * n@pre &&
        0 <= v_farthest && v_farthest <= 2 * n@pre &&
        (forall (k: Z), (0 <= k && k < n@pre) => 0 <= l[k] && l[k] <= n@pre) &&
        IntArray::full(a@pre, n@pre, l)
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
