#include "verification_stdlib.h"
#include "verification_list.h"
#include "sll_shape_def.h"

struct list * sll_zip(struct list * x, struct list * y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
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
            lseg(x@pre, p) * listrep(p -> next) * listrep(q) */
    while (q) {
        np = p->next;
        nq = q->next;
        p->next = q;
        q->next = np;
        if (np == (struct list *) 0) {
            break;
        }
        p = np;
        q = nq;
    }
    return x;
}
