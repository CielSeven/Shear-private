#include "zephyr_slist_raw.h"

long zephyr_slist_iter(sys_slist_t *list)
{
    sys_snode_t *node;
    long sum;

    sum = 0;
    SYS_SLIST_FOR_EACH_NODE(list, node) {
        sum += zephyr_slist_item_from_node(node)->data;
    }
    return sum;
}
