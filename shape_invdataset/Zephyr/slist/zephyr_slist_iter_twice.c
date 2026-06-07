#include "zephyr_slist_raw.h"

long zephyr_slist_iter_twice(sys_slist_t *list)
{
    sys_snode_t *node;
    long sum;

    sum = 0;
    node = sys_slist_peek_head(list);
    while (node != NULL) {
        sum += zephyr_slist_item_from_node(node)->data;
        node = sys_slist_peek_next(node);
        if (node != NULL) {
            sum += zephyr_slist_item_from_node(node)->data;
            node = sys_slist_peek_next(node);
        }
    }
    return sum;
}
