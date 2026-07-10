#include "glibc_slist_clean.h"

struct list *list_append_raw(struct list *x, struct list *y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */
{
    struct list *tail;

    if (x == 0) {
        return y;
    }

    tail = list_tail(x);
    tail->next = y;
    return x;
}
