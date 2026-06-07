#include "glibc_slist_raw.h"

struct glibc_slist *glibc_slist_app(struct glibc_slist *x,
                                    struct glibc_slist *y)
{
    struct glibc_slist_node *tail;

    if (SLIST_EMPTY(x)) {
        x->slh_first = SLIST_FIRST(y);
        SLIST_INIT(y);
        return x;
    }

    tail = SLIST_FIRST(x);
    while (SLIST_NEXT(tail, link) != NULL) {
        tail = SLIST_NEXT(tail, link);
    }

    tail->link.sle_next = SLIST_FIRST(y);
    SLIST_INIT(y);
    return x;
}
