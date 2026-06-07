#include "zephyr_slist_raw.h"

static long zephyr_slist_iter_back_from(sys_snode_t *node)
{
    long sum;

    if (node == NULL) {
        return 0;
    }

    sum = zephyr_slist_iter_back_from(sys_slist_peek_next(node));
    return sum + zephyr_slist_item_from_node(node)->data;
}

long zephyr_slist_iter_back(sys_slist_t *list)
{
    return zephyr_slist_iter_back_from(sys_slist_peek_head(list));
}
