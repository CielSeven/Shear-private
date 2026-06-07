#include "glibc_slist_raw.h"

long glibc_slist_iter(struct glibc_slist *head)
{
    struct glibc_slist_node *node;
    long sum;

    sum = 0;
    SLIST_FOREACH(node, head, link) {
        sum += node->data;
    }
    return sum;
}
