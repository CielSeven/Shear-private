#include "glibc_slist_clean.h"

long glibc_slist_clean_iter_back_2(struct list *x)
/*@ Require listrep(x)
    Ensure  listrep(x@pre)
 */
{
    struct list *stop;
    struct list *prev;
    struct list *node;
    long sum;

    stop = 0;
    sum = 0;
    /*@ Inv exists st s,
            store(&stop, struct list*, st) *
            store(&sum, long, s) *
            undef_data_at(&prev, struct list*) *
            undef_data_at(&node, struct list*) *
            listrep(x)
     */
    while (x != stop) {
        prev = 0;
        node = x;
        /*@ Inv exists p st s,
                node != 0 &&
                store(&prev, struct list*, p) *
                store(&stop, struct list*, st) *
                store(&sum, long, s) *
                listrep(node)
         */
        while (node->next != stop) {
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
