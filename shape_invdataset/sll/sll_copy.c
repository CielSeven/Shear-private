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
    if (x == 0) {
      return 0;
    }
    y = malloc_list(x -> data);
    t = y;
    p = x -> next;
    /*@ Inv exists v, t != 0 && t -> next == 0 && t -> data == v && lseg(x@pre,p) * listrep(p) * lseg(y, t) */
    while (p) {
      t -> next = malloc_list(p -> data);
      t = t -> next;
      p = p -> next;
    }
    return y;
}
