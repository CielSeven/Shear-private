#include "verification_stdlib.h"
#include "verification_list.h"
#include "dll_shape_def.h"

struct list * append(struct list * x, struct list * y)
/*@ Require dlistrep_shape(x, 0) * dlistrep_shape(y, 0)
    Ensure  dlistrep_shape(__return, 0)
 */
{
    struct list *t, *u;
    if (x == 0) {
        return y;
    } else {
        t = x;
        u = t->next;
        /*@ Inv exists v, t->data == v &&
            u == t->next && t != 0 &&
            dlistrep_shape(u, t) *
            dllseg_shape(x@pre, 0, t->prev, t)
         */
        while (u) {
            t = u;
            u = t->next;
        }
        t->next = y;
        if (y) {
            y->prev = t;
        }
        return x;
    }
}
