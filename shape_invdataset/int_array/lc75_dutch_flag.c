#include "int_array_def.h"

void array_dutch_flag_sort(int *a, int n)
/*@ Require 0 <= n && n < INT_MAX && IntArray::full_shape(a, n)
    Ensure IntArray::full_shape(a, n)
*/
{
    int low;
    int mid;
    int high;
    int tmp;
    low = 0;
    mid = 0;
    high = n - 1;
    /*@ Inv Assert
        exists v_tmp,
        tmp == v_tmp &&
        0 <= low && low <= mid && mid <= high + 1 && high < n@pre &&
        a == a@pre && n == n@pre &&
        0 <= n@pre && n@pre < INT_MAX &&
        IntArray::full_shape(a@pre, n@pre)
    */
    while (mid <= high) {
        if (a[mid] == 0) {
            tmp = a[low];
            a[low] = a[mid];
            a[mid] = tmp;
            low = low + 1;
            mid = mid + 1;
        } else if (a[mid] == 1) {
            mid = mid + 1;
        } else {
            tmp = a[mid];
            a[mid] = a[high];
            a[high] = tmp;
            high = high - 1;
        }
    }
}
