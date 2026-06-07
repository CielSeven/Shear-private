#include "int_array_def.h"

int array_can_jump(int *a, int n)
/*@ With l
    Require 0 <= n && n < 1000000 && IntArray::full(a, n, l) &&
            (forall (k: Z), (0 <= k && k < n) => 0 <= l[k] && l[k] <= n)
    Ensure IntArray::full(a, n, l)
*/
{
    int i;
    int farthest;
    i = 0;
    farthest = 0;
    /*@ Inv Assert
        exists v,
        farthest == v &&
        0 <= i && i <= n@pre &&
        a == a@pre && n == n@pre &&
        0 <= n@pre && n@pre < 1000000 &&
        0 <= v && v <= 2 * n@pre &&
        (forall (k: Z), (0 <= k && k < n@pre) => 0 <= l[k] && l[k] <= n@pre) &&
        IntArray::full(a@pre, n@pre, l)
    */
    while (i < n) {
        if (i > farthest) {
            return 0;
        }
        if (i + a[i] > farthest) {
            farthest = i + a[i];
        }
        i = i + 1;
    }
    return 1;
}
