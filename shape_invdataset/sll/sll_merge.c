#include "verification_stdlib.h"
#include "verification_list.h"
#include "sll_shape_def.h"

struct list * sll_merge(struct list * x, struct list * y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */
{
    struct list *result, *t;
    if (x == (struct list *) 0) {
        return y;
    }
    if (y == (struct list *) 0) {
        return x;
    }
    if (x->data <= y->data) {
        result = x;
        x = x->next;
        result->next = 0;
    } else {
        result = y;
        y = y->next;
        result->next = 0;
    }
    t = result;
    /*@ Inv exists w, t != 0 && t -> next == 0 && t -> data == w &&
            listrep(x) * listrep(y) * lseg(result, t) */
    while (x && y) {
        if (x->data <= y->data) {
            t->next = x;
            t = x;
            x = x->next;
            t->next = 0;
        } else {
            t->next = y;
            t = y;
            y = y->next;
            t->next = 0;
        }
    }
    if (x) {
        t->next = x;
    } else {
        t->next = y;
    }
    return result;
}
