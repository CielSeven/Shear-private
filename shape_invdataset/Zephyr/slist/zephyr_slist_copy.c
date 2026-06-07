#include "zephyr_slist_raw.h"

sys_slist_t *zephyr_slist_copy(sys_slist_t *src)
{
    sys_slist_t *dst;
    sys_snode_t *node;
    struct zephyr_slist_item *item;
    struct zephyr_slist_item *copy;

    dst = malloc(sizeof(*dst));
    if (dst == NULL) {
        return NULL;
    }

    sys_slist_init(dst);
    SYS_SLIST_FOR_EACH_NODE(src, node) {
        item = zephyr_slist_item_from_node(node);
        copy = zephyr_slist_new_item(item->data);
        if (copy == NULL) {
            while ((node = sys_slist_get(dst)) != NULL) {
                free(zephyr_slist_item_from_node(node));
            }
            free(dst);
            return NULL;
        }
        sys_slist_append(dst, &copy->node);
    }
    return dst;
}
