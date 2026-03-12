#include "verification_stdlib.h"
#include "verification_list.h"
#include "sll_shape_def.h"


struct list * sll_append(struct list * x, struct list * y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */
{
    struct list *t, *u;
    if (x == (struct list*) 0) {
        return y;
    } else {
        t = x;
        u = t->next;
        /*@ Inv  exists w, t != 0 && 
            t -> next == u && t -> data == w &&
            listrep(y) *
            listrep(u) *
            lseg(x, t)
         */
        while (u) {
            t = u;
            u = t->next;
        }
        t->next = y;
        return x;
    }
}