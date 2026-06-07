#include "zephyr_slist_raw.h"

sys_slist_t *zephyr_slist_multi_merge(sys_slist_t *x, sys_slist_t *y,
                                      sys_slist_t *z)
{
    sys_snode_t *cursor;
    sys_snode_t *node;
    int take_y;

    if (sys_slist_is_empty(x)) {
        sys_slist_merge_slist(x, y);
    }

    if (sys_slist_is_empty(x)) {
        sys_slist_merge_slist(x, z);
        return x;
    }

    cursor = sys_slist_peek_head(x);
    take_y = 1;
    while (!sys_slist_is_empty(y) || !sys_slist_is_empty(z)) {
        if (take_y && !sys_slist_is_empty(y)) {
            node = sys_slist_get(y);
        } else if (!sys_slist_is_empty(z)) {
            node = sys_slist_get(z);
        } else {
            node = sys_slist_get(y);
        }

        sys_slist_insert(x, cursor, node);
        cursor = node;
        take_y = !take_y;
        if (sys_slist_peek_next(cursor) != NULL) {
            cursor = sys_slist_peek_next(cursor);
        }
    }
    return x;
}
