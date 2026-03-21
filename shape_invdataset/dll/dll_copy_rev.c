#include "verification_stdlib.h"
#include "verification_list.h"
#include "dll_shape_def.h"


struct list * dll_copy_rev(struct list * x)
/*@ Require dlistrep_shape(x, 0)
    Ensure  dlistrep_shape(__return, 0) * dlistrep_shape(x, 0)
 */
{
    struct list *p, *y, *t;
    p = x;
    y = (struct list *) 0;
    /*@ Inv exists p_prev,
            dllseg_shape(x@pre, 0, p_prev, p) *
            dlistrep_shape(p, p_prev) *
            dlistrep_shape(y, 0)
    */
    while (p) {
        t = malloc_dlist(p->data);
        t->next = y;
        if (y) {
            y->prev = t;
        }
        y = t;
        p = p->next;
    }
    return y;
}
