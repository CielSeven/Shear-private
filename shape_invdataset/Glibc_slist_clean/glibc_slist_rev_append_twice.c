#include "glibc_slist_clean.h"

struct list *glibc_slist_clean_rev_append_twice(struct list *x, struct list *y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */
{
    struct list *t;

    /*@ Inv Assert undef_data_at(&t, struct list*) * listrep(x) * listrep(y)
     */
    while (x != 0) {
        t = x->next;
        x->next = y;
        y = x;
        x = t;

        if (x != 0) {
            t = x->next;
            x->next = y;
            y = x;
            x = t;
        }
    }
    return y;
}
