#include "dll_shape_def.h"

struct list *append(struct list *x, struct list *y)
/*@ Require dlistrep_shape(x, 0) * dlistrep_shape(y, 0)
    Ensure  dlistrep_shape(__return, 0)
 */
{
  struct list *t, *u;
  if (x == 0) {
    return y;
  } 
  t = x;
  u = t->next;
  /*@ Inv exists v,
        x == x@pre && y == y@pre && t->data == v &&
        u == t->next && t != 0 &&
        dlistrep_shape(y@pre, 0) *
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
