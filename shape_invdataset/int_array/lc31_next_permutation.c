#include "int_array_def.h"

void array_next_permutation(int *a, int n)
/*@ Require 0 <= n && n < INT_MAX && IntArray::full_shape(a, n)
    Ensure IntArray::full_shape(a, n)
*/
{
    int i;
    int j;
    int left;
    int right;
    int tmp;
    i = n - 2;
    /*@ Inv Assert
        exists v_j v_left v_right v_tmp,
        j == v_j && left == v_left && right == v_right && tmp == v_tmp &&
        -1 <= i && i <= n@pre - 2 &&
        a == a@pre && n == n@pre &&
        0 <= n@pre && n@pre < INT_MAX &&
        IntArray::full_shape(a@pre, n@pre)
    */
    while (i >= 0 && a[i] >= a[i + 1]) {
        i = i - 1;
    }
    if (i >= 0) {
        j = n - 1;
        /*@ Inv Assert
            exists v_left v_right v_tmp,
            left == v_left && right == v_right && tmp == v_tmp &&
            0 <= i && i < j && j < n@pre &&
            a == a@pre && n == n@pre &&
            0 <= n@pre && n@pre < INT_MAX &&
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
    /*@ Inv Assert
        exists v_i v_j v_tmp,
        i == v_i && j == v_j && tmp == v_tmp &&
        0 <= left && left <= right + 1 && right < n@pre &&
        a == a@pre && n == n@pre &&
        0 <= n@pre && n@pre < INT_MAX &&
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
