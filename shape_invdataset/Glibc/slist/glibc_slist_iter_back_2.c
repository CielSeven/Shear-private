#include "glibc_slist_raw.h"

long glibc_slist_iter_back_2(struct glibc_slist *head)
{
    struct glibc_slist_node *stop;
    struct glibc_slist_node *prev;
    struct glibc_slist_node *node;
    long sum;

    stop = NULL;
    sum = 0;
    while (SLIST_FIRST(head) != stop) {
        prev = NULL;
        node = SLIST_FIRST(head);
        while (SLIST_NEXT(node, link) != stop) {
            prev = node;
            node = SLIST_NEXT(node, link);
        }
        sum += node->data;
        stop = node;
        if (prev == NULL) {
            break;
        }
    }
    return sum;
}
