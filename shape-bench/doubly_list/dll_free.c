#include "dll_shape_def.h"

void dll_free(struct list *x)
/*@ Require dlistrep_shape(x, 0)
    Ensure emp
 */
{
  struct list *y;
  /*@ Inv has_permission(&y) * exists prev, dlistrep_shape(x, prev) */
  while (x) {
    y = x->next;
    free_dlist(x);
    x = y;
  }
}