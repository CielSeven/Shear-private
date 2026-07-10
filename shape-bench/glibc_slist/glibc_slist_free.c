#include "glibc_slist_clean.h"

void glibc_slist_clean_free(struct list *x)
/*@ Require listrep(x)
    Ensure  emp
 */
{
    struct list *next;

    /*@ Inv undef_data_at(&next, struct list*) * listrep(x)
     */
    while (x != 0) {
        next = x->next;
        free_list_node(x);
        x = next;
    }
}
