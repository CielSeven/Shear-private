#include "glibc_slist_clean.h"

struct list *glibc_slist_clean_copy(struct list *src)
/*@ Require listrep(src)
    Ensure  listrep(src@pre) * listrep(__return)
 */
{
    struct list *dst;
    struct list *node;
    struct list *copy;

    dst = 0;
    node = src;
    /*@ Inv
            src == src@pre &&
            undef_data_at(&copy, struct list*) *
            lseg(src@pre, node) *
            listrep(node) *
            listrep(dst)
     */
    while (node != 0) {
        copy = malloc_list_node(node->data);

        dst = list_append_raw(dst, copy);
        node = node->next;
    }
    return dst;
}
