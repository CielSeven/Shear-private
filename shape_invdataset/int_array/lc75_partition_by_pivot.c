#include "int_array_def.h"

int array_partition_by_pivot(int *a, int n, int pivot)
/*@ Require 0 <= n && n < INT_MAX && IntArray::full_shape(a, n)
    Ensure IntArray::full_shape(a, n)
*/
{
    int left;
    int i;
    int right;
    int tmp;
    left = 0;
    i = 0;
    right = n - 1;
    tmp = 0;
    /*@ Inv
        exists v_left v_i v_right v_tmp,
        0 <= v_left && v_left <= v_i && v_i <= v_right + 1 && v_right < n@pre &&
        a == a@pre && n == n@pre && pivot == pivot@pre &&
        0 <= n@pre && n@pre < INT_MAX &&
        store(&left, int, v_left) * store(&i, int, v_i) *
        store(&right, int, v_right) * store(&tmp, int, v_tmp) *
        IntArray::full_shape(a@pre, n@pre)
    */
    while (i <= right) {
        if (a[i] < pivot) {
            tmp = a[left];
            a[left] = a[i];
            a[i] = tmp;
            left = left + 1;
            i = i + 1;
        } else if (a[i] == pivot) {
            i = i + 1;
        } else {
            tmp = a[i];
            a[i] = a[right];
            a[right] = tmp;
            right = right - 1;
        }
    }
    return left;
}
