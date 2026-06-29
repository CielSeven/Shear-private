#include "glibc_slist_clean.h"

long glibc_slist_clean_iter(struct list *x)
/*@ Require listrep(x)
    Ensure  exists v, __return == v && listrep(x@pre)
 */
{
    long sum;

    sum = 0;
    /*@ Inv exists s,
            store(&sum, long, s) *
            lseg(x@pre, x) *
            listrep(x)
    */
    while (x != 0) {
        sum += x->data;
        x = x->next;
    }
    return sum;
}
