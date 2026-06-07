#include "zephyr_slist_raw.h"

long zephyr_slist_iter_back_2(sys_slist_t *list)
{
    sys_snode_t *stop;
    sys_snode_t *prev;
    sys_snode_t *node;
    long sum;

    stop = NULL;
    sum = 0;
    while (sys_slist_peek_head(list) != stop) {
        prev = NULL;
        node = sys_slist_peek_head(list);
        while (sys_slist_peek_next(node) != stop) {
            prev = node;
            node = sys_slist_peek_next(node);
        }
        sum += zephyr_slist_item_from_node(node)->data;
        stop = node;
        if (prev == NULL) {
            break;
        }
    }
    return sum;
}
