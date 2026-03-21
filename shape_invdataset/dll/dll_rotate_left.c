#include "verification_stdlib.h"
#include "verification_list.h"
#include "dll_shape_def.h"

struct list * dll_rotate_left(struct list * x)
/*@ Require dlistrep_shape(x, 0)
    Ensure  dlistrep_shape(__return, 0)
 */
{
    struct list *head, *new_head, *t, *u;
    if (x == (struct list *) 0 || x->next == (struct list *) 0) {
        return x;
    }
    head = x;
    new_head = x->next;
    new_head->prev = 0;
    head->next = 0;
    head->prev = 0;
    t = new_head;
    u = t->next;
    /*@ Inv exists w, head != 0 && t != 0 && t -> data == w && t -> next == u &&
            dlistrep_shape(head, 0) *
            dlistrep_shape(u, t) *
            dllseg_shape(new_head, 0, t -> prev, t)
    */
    while (u) {
        t = u;
        u = t->next;
    }
    t->next = head;
    head->prev = t;
    return new_head;
}
