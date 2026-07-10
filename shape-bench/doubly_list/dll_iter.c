#include "dll_shape_def.h"

struct list *iter(struct list *l)
/*@ Require dlistrep_shape(l, 0)
    Ensure  dlistrep_shape(__return, 0)
 */
{
  struct list *p;
  p = l;
  /*@ Inv exists p_prev,
        l == l@pre &&
        dllseg_shape(l@pre, 0, p_prev, p) *
        dlistrep_shape(p, p_prev)
      */
  while (p) {
    p = p->next;
  }
  return l;
}
