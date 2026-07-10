#include "dll_shape_def.h"

struct list *iter_back(struct list *l, struct list *head)
/*@ With l_prev
    Require head != 0 && dllseg_shape(head, 0, l_prev, l) * dlistrep_shape(l, l_prev)
    Ensure  dlistrep_shape(__return, 0)
 */
{
  struct list *p;
  if (l == 0) {
    return head;
  } else {
    p = l;
    /*@ Inv exists v,
          head == head@pre && l == l@pre &&
          p != 0 && p->data == v &&
          dllseg_shape(head@pre, 0, p->prev, p) * dlistrep_shape(p->next, p)
        */
    while (p != head) {
      p = p->prev;
    }
  }
  return p;
}
