#include "glibc_slist_raw.h"

void glibc_slist_free(struct glibc_slist *head)
{
    struct glibc_slist_node *node;

    while (!SLIST_EMPTY(head)) {
        node = SLIST_FIRST(head);
        SLIST_REMOVE_HEAD(head, link);
        free(node);
    }
}
