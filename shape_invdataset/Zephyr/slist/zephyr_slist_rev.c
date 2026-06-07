#include "zephyr_slist_raw.h"

sys_slist_t *zephyr_slist_rev(sys_slist_t *list)
{
    sys_slist_t reversed;
    sys_snode_t *node;

    sys_slist_init(&reversed);
    while ((node = sys_slist_get(list)) != NULL) {
        sys_slist_prepend(&reversed, node);
    }

    list->head = reversed.head;
    list->tail = reversed.tail;
    return list;
}
