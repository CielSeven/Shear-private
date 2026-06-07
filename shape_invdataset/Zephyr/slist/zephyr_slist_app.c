#include "zephyr_slist_raw.h"

sys_slist_t *zephyr_slist_app(sys_slist_t *x, sys_slist_t *y)
{
    sys_slist_merge_slist(x, y);
    return x;
}
