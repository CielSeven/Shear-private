#include "glibc_slist_clean.h"

struct list *glibc_slist_clean_multi_append(struct list *x, struct list *y,
                                            struct list *z)
/*@ Require listrep(x) * listrep(y) * listrep(z)
    Ensure  listrep(__return)
 */
{
    x = list_append_raw(x, y);
    x = list_append_raw(x, z);
    return x;
}
