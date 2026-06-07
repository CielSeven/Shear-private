#include "glibc_slist_clean.h"

struct list *glibc_slist_clean_merge(struct list *x, struct list *y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */
{
    struct list *head;
    struct list *cursor;
    struct list *node;

    if (x == 0) {
        return y;
    }

    head = x;
    cursor = x;
    /*@ Inv Assert
            x == x@pre &&
            cursor != 0 &&
            undef_data_at(&node, struct list*) *
            lseg(head, cursor) *
            listrep(cursor) *
            listrep(y)
     */
    while (y != 0) {
        node = y;
        y = y->next;
        node->next = cursor->next;
        cursor->next = node;
        cursor = node;
        if (cursor->next == 0) {
            cursor->next = y;
            return head;
        }
        cursor = cursor->next;
    }
    return head;
}
