#include "glibc_slist_raw.h"

static long glibc_slist_iter_back_from(struct glibc_slist_node *node)
{
    long sum;

    if (node == NULL) {
        return 0;
    }

    sum = glibc_slist_iter_back_from(SLIST_NEXT(node, link));
    return sum + node->data;
}

long glibc_slist_iter_back(struct glibc_slist *head)
{
    return glibc_slist_iter_back_from(SLIST_FIRST(head));
}
