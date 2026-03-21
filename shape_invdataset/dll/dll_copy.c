#include "verification_stdlib.h"
#include "verification_list.h"
#include "dll_shape_def.h"


struct list * dll_copy(struct list * x)
/*@ Require dlistrep_shape(x, 0)
    Ensure  dlistrep_shape(__return, 0) * dlistrep_shape(x, 0)
 */
{
    struct list *y, *p, *t;
    y = malloc_dlist(0);
    t = y;
    p = x;
    /*@ Inv exists p_prev, 
            t != 0 && t -> next == 0 && t -> data == 0 && dllseg_shape(x@pre,0, p_prev,p) * dlistrep_shape(p, p_prev) * dllseg_shape(y, 0, t->prev, t) */
    while (p) {
      t -> data = p -> data;
      t -> next = malloc_dlist(0);
      t -> next -> prev = t;
      p = p -> next;
      t = t -> next;
    }
    return y;
}
