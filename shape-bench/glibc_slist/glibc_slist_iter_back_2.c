#include "glibc_slist_clean.h"

long glibc_slist_clean_iter_back_2(struct list *x)
/*@ Require listrep(x)
    Ensure  exists v, __return == v && listrep(x@pre)
 */
{
    struct list *stop;
    struct list *prev;
    struct list *node;
    long sum;

    stop = 0;
    sum = 0;
    if (x == 0) {
        return sum;
    }
    /*@ Inv exists s,
            x == x@pre &&
            x != 0 &&
            store(&sum, long, s) *
            undef_data_at(&prev, struct list*) *
            undef_data_at(&node, struct list*) *
            lseg(x, stop) * listrep(stop)
     */
    while (x != stop) {
        prev = 0;
        node = x;
        /*@ Inv exists p s nxt v,
                x == x@pre &&
                x != 0 &&
                node != 0 &&
                node -> next == nxt &&
                node -> data == v &&
                store(&prev, struct list*, p) *
                store(&sum, long, s) *
                lseg(x, node) * lseg(nxt, stop) *
                listrep(stop)
         */
        while (node->next != stop && node->next != 0) {
            prev = node;
            node = node->next;
        }
        sum += node->data;
        stop = node;
        if (prev == 0) {
            break;
        }
    }
    return sum;
}
