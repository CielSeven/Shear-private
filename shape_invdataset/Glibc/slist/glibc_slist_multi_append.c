#include "glibc_slist_raw.h"

static struct glibc_slist *glibc_slist_append_local(struct glibc_slist *x,
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

struct glibc_slist *glibc_slist_multi_append(struct glibc_slist *x,
                                             struct glibc_slist *y,
                                             struct glibc_slist *z)
{
    glibc_slist_append_local(x, y);
    glibc_slist_append_local(x, z);
    return x;
}
