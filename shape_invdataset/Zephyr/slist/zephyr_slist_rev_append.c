#include "zephyr_slist_raw.h"

sys_slist_t *zephyr_slist_rev_append(sys_slist_t *src, sys_slist_t *dst)
{
    sys_snode_t *node;

    while ((node = sys_slist_get(src)) != NULL) {
        sys_slist_prepend(dst, node);
    }
    return dst;
}
