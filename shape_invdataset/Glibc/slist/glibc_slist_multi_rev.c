#include "glibc_slist_raw.h"

static void glibc_slist_rev_append_local(struct glibc_slist *src,
                                         struct glibc_slist *dst)
{
    struct glibc_slist_node *node;

    while (!SLIST_EMPTY(src)) {
        node = SLIST_FIRST(src);
        SLIST_REMOVE_HEAD(src, link);
        SLIST_INSERT_HEAD(dst, node, link);
    }
}

struct glibc_slist *glibc_slist_multi_rev(struct glibc_slist *x,
                                          struct glibc_slist *y)
{
    struct glibc_slist out;

    SLIST_INIT(&out);
    glibc_slist_rev_append_local(x, &out);
    glibc_slist_rev_append_local(y, &out);
    x->slh_first = SLIST_FIRST(&out);
    return x;
}
