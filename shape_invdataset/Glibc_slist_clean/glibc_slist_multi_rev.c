#include "glibc_slist_clean.h"

static struct list *rev_append_local(struct list *src, struct list *dst)
/*@ Require listrep(src) * listrep(dst)
    Ensure  listrep(__return)
 */
{
    struct list *node;

    /*@ Inv undef_data_at(&node, struct list*) * listrep(src) * listrep(dst)
     */
    while (src != 0) {
        node = src;
        src = src->next;
        node->next = dst;
        dst = node;
    }
    return dst;
}

struct list *glibc_slist_clean_multi_rev(struct list *x, struct list *y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */
{
    struct list *out;

    out = 0;
    out = rev_append_local(x, out);
    out = rev_append_local(y, out);
    return out;
}
