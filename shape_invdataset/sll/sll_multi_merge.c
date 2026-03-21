#include "verification_stdlib.h"
#include "verification_list.h"
#include "sll_shape_def.h"

struct list * sll_merge(struct list * x, struct list * y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */;

struct list * sll_multi_merge(struct list * x, struct list * y, struct list * z)
/*@ Require listrep(x) * listrep(y) * listrep(z)
    Ensure  listrep(__return)
 */
{
    struct list *t, *u;
    if (x == (struct list *) 0) {
        t = sll_merge(y, z);
        return t;
    }
    t = x;
    u = t->next;
    /*@ Inv exists v, v == t -> data && u == t -> next && t != 0 &&
            listrep(y) * listrep(z) * listrep(u) * lseg(x@pre, t) */
    while (u) {
        if (y) {
            t->next = y;
            t = y;
            y = y->next;
        } else {
            u = sll_merge(u, z);
            t->next = u;
            return x;
        }
        if (z) {
            t->next = z;
            t = z;
            z = z->next;
        } else {
            u = sll_merge(u, y);
            t->next = u;
            return x;
        }
        t->next = u;
        t = u;
        u = u->next;
    }
    u = sll_merge(y, z);
    t->next = u;
    return x;
}
