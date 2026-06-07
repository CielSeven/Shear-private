#include "zephyr_slist_raw.h"

sys_slist_t *zephyr_slist_merge(sys_slist_t *x, sys_slist_t *y)
{
    sys_snode_t *cursor;
    sys_snode_t *node;

    if (sys_slist_is_empty(x)) {
        sys_slist_merge_slist(x, y);
        return x;
    }

    cursor = sys_slist_peek_head(x);
    while ((node = sys_slist_get(y)) != NULL) {
        sys_slist_insert(x, cursor, node);
        cursor = node;
        if (sys_slist_peek_next(cursor) == NULL) {
            sys_slist_merge_slist(x, y);
            break;
        }
        cursor = sys_slist_peek_next(cursor);
    }
    return x;
}
