#include "verification_stdlib.h"
#include "verification_list.h"
#include "dll_shape_def.h"


struct list * dll_copy_rev_append(struct list * x, struct list * y)
/*@ Require dlistrep_shape(x, 0) * dlistrep_shape(y, 0)
    Ensure  dlistrep_shape(__return, 0) * dlistrep_shape(x, 0)
 */
{
    struct list *p, *acc, *t;
    p = x;
    acc = y;
    /*@ Inv exists p_prev,
            dllseg_shape(x@pre, 0, p_prev, p) *
            dlistrep_shape(p, p_prev) *
            dlistrep_shape(acc, 0)
    */
    while (p) {
        t = malloc_dlist(p->data);
        t->next = acc;
        if (acc) {
            acc->prev = t;
        }
        acc = t;
        p = p->next;
    }
    return acc;
}
