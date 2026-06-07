#include "glibc_slist_clean.h"

struct list *glibc_slist_clean_multi_merge(struct list *x, struct list *y,
                                           struct list *z)
/*@ Require listrep(x) * listrep(y) * listrep(z)
    Ensure  listrep(__return)
 */
{
    struct list *cursor;
    struct list *node;
    int take_y;

    if (x == 0) {
        x = y;
        y = 0;
    }

    if (x == 0) {
        x = z;
        z = 0;
        return x;
    }

    cursor = x;
    take_y = 1;
    /*@ Inv exists ty,
            cursor != 0 &&
            take_y == ty &&
            undef_data_at(&node, struct list*) *
            lseg(x, cursor) *
            listrep(cursor) *
            listrep(y) *
            listrep(z)
     */
    while (y != 0 || z != 0) {
        if (take_y && y != 0) {
            node = y;
            y = y->next;
        } else if (z != 0) {
            node = z;
            z = z->next;
        } else {
            node = y;
            y = y->next;
        }

        node->next = cursor->next;
        cursor->next = node;
        cursor = node;
        take_y = !take_y;

        if (cursor->next != 0) {
            cursor = cursor->next;
        }
    }
    return x;
}
