#include "int_array_def.h"

int array_rob_linear(int *a, int n)
/*@ Require 0 <= n && n < INT_MAX && IntArray::full_shape(a, n)
    Ensure IntArray::full_shape(a, n)
*/
{
    int i;
    int skip;
    int take;
    int next_skip;
    int next_take;
    skip = 0;
    take = 0;
    i = 0;
    /*@ Inv Assert
        exists v_skip v_take v_next_skip v_next_take,
        skip == v_skip && take == v_take &&
        next_skip == v_next_skip && next_take == v_next_take &&
        0 <= i && i <= n@pre &&
        a == a@pre && n == n@pre &&
        0 <= n@pre && n@pre < INT_MAX &&
        IntArray::full_shape(a@pre, n@pre)
    */
    while (i < n) {
        if (skip > take) {
            next_skip = skip;
        } else {
            next_skip = take;
        }
        next_take = skip + a[i];
        skip = next_skip;
        take = next_take;
        i = i + 1;
    }
    if (skip > take) {
        return skip;
    }
    return take;
}
