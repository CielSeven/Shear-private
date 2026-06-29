#include "int_array_def.h"

void array_reverse_range(int *a, int n, int left, int right)
/*@ Require 0 <= n && n < INT_MAX && 0 <= left && left <= right + 1 && right < n &&
            IntArray::full_shape(a, n)
    Ensure IntArray::full_shape(a, n)
*/
{
    int tmp;
    tmp = 0;
    /*@ Inv
        exists v_left v_right v_tmp,
        0 <= v_left && v_left <= v_right + 1 && v_right < n@pre &&
        left@pre <= v_left && v_right <= right@pre &&
        a == a@pre && n == n@pre &&
        0 <= n@pre && n@pre < INT_MAX &&
        store(&left, int, v_left) * store(&right, int, v_right) *
        store(&tmp, int, v_tmp) *
        IntArray::full_shape(a@pre, n@pre)
    */
    while (left < right) {
        tmp = a[left];
        a[left] = a[right];
        a[right] = tmp;
        left = left + 1;
        right = right - 1;
    }
}

void array_rotate_right(int *a, int n, int k)
/*@ Require 0 <= n && n < INT_MAX && IntArray::full_shape(a, n)
    Ensure IntArray::full_shape(a, n)
*/
{
    if (n <= 0) {
        return;
    }
    k = k % n;
    if (k < 0) {
        k = k + n;
    }
    if (k == 0) {
        return;
    }
    array_reverse_range(a, n, 0, n - 1);
    array_reverse_range(a, n, 0, k - 1);
    array_reverse_range(a, n, k, n - 1);
}
