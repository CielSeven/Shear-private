#include "glibc_slist_clean.h"

struct list *glibc_slist_clean_app(struct list *x, struct list *y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */
{
    return list_append_raw(x, y);
}
