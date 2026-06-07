#include "glibc_slist_clean.h"

long glibc_slist_clean_iter_back(struct list *x)
/*@ Require listrep(x)
    Ensure  listrep(x@pre)
 */
{
    long sum;

    if (x == 0) {
        return 0;
    }

    sum = glibc_slist_clean_iter_back(x->next);
    return sum + x->data;
}
