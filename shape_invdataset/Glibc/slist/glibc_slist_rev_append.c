#include "glibc_slist_raw.h"

struct glibc_slist *glibc_slist_rev_append(struct glibc_slist *src,
                                           struct glibc_slist *dst)
{
    struct glibc_slist_node *node;

    while (!SLIST_EMPTY(src)) {
        node = SLIST_FIRST(src);
        SLIST_REMOVE_HEAD(src, link);
        SLIST_INSERT_HEAD(dst, node, link);
    }
    return dst;
}
