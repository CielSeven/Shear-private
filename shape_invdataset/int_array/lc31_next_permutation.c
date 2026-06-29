#include "int_array_def.h"

void array_next_permutation(int *a, int n)
/*@ Require IntArray::full_shape(a, n)
    Ensure IntArray::full_shape(a, n)
*/
{
    int i;
    int j;
    int left;
    int right;
    int tmp;
    j = 0;
    left = 0;
    right = 0;
    tmp = 0;
    i = n - 2;
    /*@ Inv
        exists v_i v_j v_left v_right v_tmp,
        -1 <= v_i && v_i <= n@pre - 2 &&
        a == a@pre && n == n@pre &&
        0 <= n@pre && n@pre < INT_MAX &&
        store(&i, int, v_i) * store(&j, int, v_j) *
        store(&left, int, v_left) * store(&right, int, v_right) *
        store(&tmp, int, v_tmp) *
        IntArray::full_shape(a@pre, n@pre)
    */
    while (i >= 0 && a[i] >= a[i + 1]) {
        i = i - 1;
    }
    if (i >= 0) {
        j = n - 1;
        /*@ Inv
            exists v_i v_j v_left v_right v_tmp,
            0 <= v_i && v_i < v_j && v_j < n@pre &&
            a == a@pre && n == n@pre &&
            0 <= n@pre && n@pre < INT_MAX &&
            store(&i, int, v_i) * store(&j, int, v_j) *
            store(&left, int, v_left) * store(&right, int, v_right) *
            store(&tmp, int, v_tmp) *
            IntArray::full_shape(a@pre, n@pre)
        */
        while (a[j] <= a[i]) {
            j = j - 1;
        }
        tmp = a[i];
        a[i] = a[j];
        a[j] = tmp;
    }
    left = i + 1;
    right = n - 1;
    /*@ Inv
        exists v_i v_j v_left v_right v_tmp,
        0 <= v_left && v_left <= v_right + 1 && v_right < n@pre &&
        a == a@pre && n == n@pre &&
        0 <= n@pre && n@pre < INT_MAX &&
        store(&i, int, v_i) * store(&j, int, v_j) *
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
