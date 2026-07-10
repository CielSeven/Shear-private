#include "dll_shape_def.h"

struct list *dll_copy(struct list *x)
/*@ Require dlistrep_shape(x, 0)
    Ensure  dlistrep_shape(__return, 0) * dlistrep_shape(x, 0)
 */
{
  struct list *y, *p, *t;
  if (x == 0) {
    return 0;
  }
  y = malloc_dlist(x -> data);
  t = y;
  p = x -> next;
  /*@ Inv exists p_prev v,
            x == x@pre && t != 0 && t -> next == 0 && t -> data == v && dllseg_shape(x,0, p_prev,p) * dlistrep_shape(p, p_prev) * dllseg_shape(y, 0, t->prev, t) */
  while (p) {
    t->next = malloc_dlist(p->data);
    t->next->prev = t;
    p = p->next;
    t = t->next;
  }
  return y;
}