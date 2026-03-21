#include "verification_stdlib.h"
#include "verification_list.h"
#include "sll_shape_def.h"
#include "sll_runtime_def.h"


struct list * sll_copy(struct list * x)
/*@ Require listrep(x)
    Ensure  listrep(__return) * listrep(x)
 */
{
    struct list *y, *p, *t;
    y = malloc_list(0);
    t = y;
    p = x;
    /*@ Inv t != 0 && t -> next == 0 && t -> data == 0 && lseg(x@pre,p) * listrep(p) * lseg(y, t) */
    while (p) {
      t -> data = p -> data;
      t -> next = malloc_list(0);
      p = p -> next;
      t = t -> next;
    }
    free_list(t);
    return y;
}
