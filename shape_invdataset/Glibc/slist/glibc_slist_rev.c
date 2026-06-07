#include "glibc_slist_raw.h"

struct glibc_slist *glibc_slist_rev(struct glibc_slist *head)
{
    struct glibc_slist reversed;
    struct glibc_slist_node *node;

    SLIST_INIT(&reversed);
    while (!SLIST_EMPTY(head)) {
        node = SLIST_FIRST(head);
        SLIST_REMOVE_HEAD(head, link);
        SLIST_INSERT_HEAD(&reversed, node, link);
    }

    head->slh_first = SLIST_FIRST(&reversed);
    return head;
}
