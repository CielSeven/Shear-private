#include "glibc_slist_raw.h"

struct glibc_slist *glibc_slist_multi_merge(struct glibc_slist *x,
                                            struct glibc_slist *y,
                                            struct glibc_slist *z)
{
    struct glibc_slist_node *cursor;
    struct glibc_slist_node *node;
    int take_y;

    if (SLIST_EMPTY(x)) {
        x->slh_first = SLIST_FIRST(y);
        SLIST_INIT(y);
    }

    if (SLIST_EMPTY(x)) {
        x->slh_first = SLIST_FIRST(z);
        SLIST_INIT(z);
        return x;
    }

    cursor = SLIST_FIRST(x);
    take_y = 1;
    while (!SLIST_EMPTY(y) || !SLIST_EMPTY(z)) {
        if (take_y && !SLIST_EMPTY(y)) {
            node = SLIST_FIRST(y);
            SLIST_REMOVE_HEAD(y, link);
        } else if (!SLIST_EMPTY(z)) {
            node = SLIST_FIRST(z);
            SLIST_REMOVE_HEAD(z, link);
        } else {
            node = SLIST_FIRST(y);
            SLIST_REMOVE_HEAD(y, link);
        }

        SLIST_INSERT_AFTER(cursor, node, link);
        cursor = node;
        take_y = !take_y;

        if (SLIST_NEXT(cursor, link) != NULL) {
            cursor = SLIST_NEXT(cursor, link);
        }
    }
    return x;
}
