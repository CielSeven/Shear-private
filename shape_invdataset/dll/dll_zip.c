#include "verification_stdlib.h"
#include "verification_list.h"
#include "dll_shape_def.h"

struct list * dll_zip(struct list * x, struct list * y)
/*@ Require dlistrep_shape(x, 0) * dlistrep_shape(y, 0)
    Ensure  dlistrep_shape(__return, 0)
 */
{
    struct list *p, *q, *np, *nq;
    if (x == (struct list *) 0) {
        return y;
    }
    if (y == (struct list *) 0) {
        return x;
    }
    p = x;
    q = y;
    /*@ Inv exists w, p != 0 && p -> data == w &&
            dllseg_shape(x@pre, 0, p -> prev, p) *
            dlistrep_shape(p, p -> prev) *
            dlistrep_shape(q, 0)
    */
    while (q) {
        np = p->next;
        nq = q->next;
        p->next = q;
        q->prev = p;
        q->next = np;
        if (np) {
            np->prev = q;
        }
        if (np == (struct list *) 0) {
            break;
        }
        if (nq) {
            nq->prev = 0;
        }
        p = np;
        q = nq;
    }
    return x;
}
