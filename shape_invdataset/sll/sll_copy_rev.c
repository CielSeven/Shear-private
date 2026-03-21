#include "verification_stdlib.h"
#include "verification_list.h"
#include "sll_shape_def.h"
#include "sll_runtime_def.h"

struct list * sll_copy_rev(struct list * x)
/*@ Require listrep(x)
    Ensure  listrep(__return) * listrep(x)
 */
{
    struct list *p, *y, *t;
    p = x;
    y = (struct list *) 0;
    /*@ Inv lseg(x@pre, p) * listrep(p) * listrep(y) */
    while (p) {
        t = malloc_list(p->data);
        t->next = y;
        y = t;
        p = p->next;
    }
    return y;
}
