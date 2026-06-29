#include "int_array_def.h"

int array_remove_duplicates(int *a, int n)
/*@ Require 0 <= n && n < INT_MAX && IntArray::full_shape(a, n)
    Ensure IntArray::full_shape(a, n)
*/
{
    int read;
    int write;
    if (n <= 0) {
        return 0;
    }
    write = 1;
    read = 1;
    /*@ Inv
        exists v_read v_write,
        1 <= v_write && v_write <= v_read && v_read <= n@pre &&
        a == a@pre && n == n@pre &&
        0 <= n@pre && n@pre < INT_MAX &&
        store(&read, int, v_read) * store(&write, int, v_write) *
        IntArray::full_shape(a@pre, n@pre)
    */
    while (read < n) {
        if (a[read] != a[write - 1]) {
            a[write] = a[read];
            write = write + 1;
        }
        read = read + 1;
    }
    return write;
}
