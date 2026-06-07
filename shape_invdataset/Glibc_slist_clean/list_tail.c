#include "glibc_slist_clean.h"

struct list *list_tail(struct list *x)
/*@ Require x != 0 && listrep(x)
    Ensure  exists v, __return != 0 &&
            __return -> next == 0 &&
            __return -> data == v &&
            lseg(x, __return)
*/
{
    if (x == 0) {
        return 0;
    }

    /*@ Inv Assert
            x != 0 &&
            lseg(x@pre, x) *
            listrep(x)
     */
    while (x->next != 0) {
        x = x->next;
    }
    return x;
}
