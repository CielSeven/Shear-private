#include "int_array_def.h"

int array_wiggle_max_length(int *a, int n)
/*@ Require 0 <= n && n < INT_MAX && IntArray::full_shape(a, n)
    Ensure IntArray::full_shape(a, n)
*/
{
    int i;
    int up;
    int down;
    if (n <= 0) {
        return 0;
    }
    up = 1;
    down = 1;
    i = 1;
    /*@ Inv
        exists v_i v_up v_down,
        1 <= v_i && v_i <= n@pre &&
        a == a@pre && n == n@pre &&
        0 <= n@pre && n@pre < INT_MAX &&
        1 <= v_up && v_up <= v_i + 1 &&
        1 <= v_down && v_down <= v_i + 1 &&
        store(&i, int, v_i) * store(&up, int, v_up) *
        store(&down, int, v_down) *
        IntArray::full_shape(a@pre, n@pre)
    */
    while (i < n) {
        if (a[i] > a[i - 1]) {
            up = down + 1;
        } else if (a[i] < a[i - 1]) {
            down = up + 1;
        }
        i = i + 1;
    }
    if (up > down) {
        return up;
    }
    return down;
}
