#include "int_array_def.h"

int array_min_cost_climb(int *cost, int n)
/*@ Require 0 <= n && n < INT_MAX && IntArray::full_shape(cost, n)
    Ensure IntArray::full_shape(cost, n)
*/
{
    int i;
    int prev2;
    int prev1;
    int current;
    prev2 = 0;
    prev1 = 0;
    current = 0;
    i = 2;
    /*@ Inv
        exists v_i v_prev2 v_prev1 v_current,
        2 <= v_i && v_i <= n@pre + 1 &&
        cost == cost@pre && n == n@pre &&
        0 <= n@pre && n@pre < INT_MAX &&
        store(&i, int, v_i) * store(&prev2, int, v_prev2) *
        store(&prev1, int, v_prev1) * store(&current, int, v_current) *
        IntArray::full_shape(cost@pre, n@pre)
    */
    while (i <= n) {
        if (prev1 + cost[i - 1] < prev2 + cost[i - 2]) {
            current = prev1 + cost[i - 1];
        } else {
            current = prev2 + cost[i - 2];
        }
        prev2 = prev1;
        prev1 = current;
        i = i + 1;
    }
    return prev1;
}
