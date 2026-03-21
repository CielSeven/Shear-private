#include "verification_stdlib.h"
#include "verification_list.h"
#include "sll_shape_def.h"
#include "sll_runtime_def.h"


struct list * sll_copy_double(struct list * x)
/*@ Require listrep(x)
    Ensure  listrep(__return) * listrep(x)
 */
{
    struct list *p, *y, *t1, *t2;
    p = x;
    y = (struct list *) 0;
    /*@ Inv lseg(x@pre, p) * listrep(p) * listrep(y) */
    while (p) {
        t1 = malloc_list(p->data);
        t2 = malloc_list(p->data);
        t1->next = t2;
        t2->next = y;
        y = t1;
        p = p->next;
    }
    return y;
}
