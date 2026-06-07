#include "zephyr_slist_raw.h"

static void zephyr_slist_rev_append_local(sys_slist_t *src, sys_slist_t *dst)
{
    sys_snode_t *node;

    while ((node = sys_slist_get(src)) != NULL) {
        sys_slist_prepend(dst, node);
    }
}

sys_slist_t *zephyr_slist_multi_rev(sys_slist_t *x, sys_slist_t *y)
{
    sys_slist_t out;

    sys_slist_init(&out);
    zephyr_slist_rev_append_local(x, &out);
    zephyr_slist_rev_append_local(y, &out);
    x->head = out.head;
    x->tail = out.tail;
    return x;
}
