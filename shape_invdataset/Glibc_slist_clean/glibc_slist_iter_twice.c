#include "glibc_slist_clean.h"

long glibc_slist_clean_iter_twice(struct list *x)
/*@ Require listrep(x)
    Ensure  listrep(x@pre)
 */
{
    long sum;

    sum = 0;
    /*@ Inv Assert exists s,
            store(&sum, long, s) *
            lseg(x@pre, x) *
            listrep(x)
    */
    while (x != 0) {
        sum += x->data;
        x = x->next;
        if (x != 0) {
            sum += x->data;
            x = x->next;
        }
    }
    return sum;
}
