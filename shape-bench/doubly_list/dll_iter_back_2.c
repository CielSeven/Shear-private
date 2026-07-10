#include "dll_shape_def.h"

struct list *iter_back_2(struct list **head, struct list **tail)
/*@ With head_node tail_node tail_prev
    Require *head == head_node && *tail == tail_node && head_node != 0 && tail_node != 0 && dllseg_shape(head_node, 0, tail_prev, tail_node) * dlistrep_shape(tail_node, tail_prev)
    Ensure *head == head_node && *tail == tail_node && dlistrep_shape(__return, 0)
 */
{
  struct list *p;
  p = *tail;
  if (*head == *tail) {
    return p;
  } else {
    /*@ Inv exists v,
          head == head@pre && tail == tail@pre &&
          *head == head_node && *tail == tail_node &&
          p != 0 && p->data == v &&
          dllseg_shape(head_node, 0, p->prev, p) * dlistrep_shape(p->next, p)
        */
    while (p != *head) {
      p = p->prev;
    }
    return p;
  }
}
