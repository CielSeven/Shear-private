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
    /*@ Inv Assert
        exists v_up v_down,
        up == v_up && down == v_down &&
        1 <= i && i <= n@pre &&
        a == a@pre && n == n@pre &&
        0 <= n@pre && n@pre < INT_MAX &&
        1 <= v_up && v_up <= i + 1 &&
        1 <= v_down && v_down <= i + 1 &&
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
