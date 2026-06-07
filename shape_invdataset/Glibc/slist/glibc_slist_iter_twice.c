#include "glibc_slist_raw.h"

long glibc_slist_iter_twice(struct glibc_slist *head)
{
    struct glibc_slist_node *node;
    long sum;

    sum = 0;
    node = SLIST_FIRST(head);
    while (node != NULL) {
        sum += node->data;
        node = SLIST_NEXT(node, link);
        if (node != NULL) {
            sum += node->data;
            node = SLIST_NEXT(node, link);
        }
    }
    return sum;
}
