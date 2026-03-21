#include "verification_stdlib.h"
#include "verification_list.h"
#include "sll_shape_def.h"

struct list * sll_append_rev(struct list * x, struct list * y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */
{
    struct list *curr, *next;
    curr = x;
    /*@ Inv listrep(curr) * listrep(y) */
    while (curr) {
        next = curr->next;
        curr->next = y;
        y = curr;
        curr = next;
    }
    return y;
}
