#include "verification_stdlib.h"
#include "verification_list.h"
#include "sll_shape_def.h"

struct list * sll_rotate_left(struct list * x)
/*@ Require listrep(x)
    Ensure  listrep(__return)
 */
{
    struct list *t, *u;
    if (x == (struct list *) 0 || x->next == (struct list *) 0) {
        return x;
    }
    t = x;
    u = t->next;
    /*@ Inv exists w, t != 0 && t -> data == w && t -> next == u && u != 0 &&
            listrep(u -> next) * lseg(x@pre, t) */
    while (u->next) {
        t = u;
        u = u->next;
    }
    t->next = 0;
    u->next = x;
    return u;
}

struct list * sll_rotate_right(struct list * x)
/*@ Require listrep(x)
    Ensure  listrep(__return)
 */
{
    struct list *head, *new_head, *t, *u;
    if (x == (struct list *) 0 || x->next == (struct list *) 0) {
        return x;
    }
    head = x;
    new_head = x->next;
    head->next = 0;
    t = new_head;
    u = t->next;
    /*@ Inv exists w, t != 0 && t -> data == w && t -> next == u &&
            listrep(head) * listrep(u) * lseg(new_head, t) */
    while (u) {
        t = u;
        u = t->next;
    }
    t->next = head;
    return new_head;
}
