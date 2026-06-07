#include "glibc_slist_raw.h"

struct glibc_slist *glibc_slist_merge(struct glibc_slist *x,
                                      struct glibc_slist *y)
{
    struct glibc_slist_node *cursor;
    struct glibc_slist_node *node;

    if (SLIST_EMPTY(x)) {
        x->slh_first = SLIST_FIRST(y);
        SLIST_INIT(y);
        return x;
    }

    cursor = SLIST_FIRST(x);
    while (!SLIST_EMPTY(y)) {
        node = SLIST_FIRST(y);
        SLIST_REMOVE_HEAD(y, link);
        SLIST_INSERT_AFTER(cursor, node, link);
        cursor = node;
        if (SLIST_NEXT(cursor, link) == NULL) {
            cursor->link.sle_next = SLIST_FIRST(y);
            SLIST_INIT(y);
            break;
        }
        cursor = SLIST_NEXT(cursor, link);
    }
    return x;
}
