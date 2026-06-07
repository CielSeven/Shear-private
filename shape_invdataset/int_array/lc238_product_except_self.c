#include "int_array_def.h"

void array_product_except_self(int *a, int n, int *out)
/*@ Require 0 <= n && n < INT_MAX &&
            IntArray::full_shape(a, n) * IntArray::undef_full(out, n)
    Ensure IntArray::full_shape(a, n) * IntArray::full_shape(out, n)
*/
{
    int i;
    int prefix;
    int suffix;
    prefix = 1;
    i = 0;
    /*@ Inv Assert
        exists v_prefix v_suffix,
        prefix == v_prefix && suffix == v_suffix &&
        0 <= i && i <= n@pre &&
        a == a@pre && out == out@pre && n == n@pre &&
        0 <= n@pre && n@pre < INT_MAX &&
        IntArray::seg_shape(out@pre, 0, i) *
        IntArray::undef_seg(out@pre, i, n@pre) *
        IntArray::full_shape(a@pre, n@pre)
    */
    while (i < n) {
        out[i] = prefix;
        prefix = prefix * a[i];
        i = i + 1;
    }
    suffix = 1;
    i = n - 1;
    /*@ Inv Assert
        exists v_prefix v_suffix,
        prefix == v_prefix && suffix == v_suffix &&
        -1 <= i && i < n@pre &&
        a == a@pre && out == out@pre && n == n@pre &&
        0 <= n@pre && n@pre < INT_MAX &&
        IntArray::full_shape(out@pre, n@pre) *
        IntArray::full_shape(a@pre, n@pre)
    */
    while (i >= 0) {
        out[i] = out[i] * suffix;
        suffix = suffix * a[i];
        i = i - 1;
    }
}
