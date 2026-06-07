#include "zephyr_slist_raw.h"

void zephyr_slist_free(sys_slist_t *list)
{
    sys_snode_t *node;

    while ((node = sys_slist_get(list)) != NULL) {
        free(zephyr_slist_item_from_node(node));
    }
}
