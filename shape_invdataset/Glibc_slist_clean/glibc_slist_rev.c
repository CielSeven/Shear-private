#include "glibc_slist_clean.h"

struct list *glibc_slist_clean_rev(struct list *x)
/*@ Require listrep(x)
    Ensure  listrep(__return)
 */
{
    struct list *w;
    struct list *t;

    w = 0;
    /*@ Inv Assert undef_data_at(&t, struct list*) * listrep(w) * listrep(x)
     */
    while (x != 0) {
        t = x->next;
        x->next = w;
        w = x;
        x = t;
    }
    return w;
}
