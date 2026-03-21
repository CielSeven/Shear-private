#include "verification_stdlib.h"
#include "verification_list.h"

struct list {
    int data;
    struct list *next;
};

/*@  With X
    Require safeExec(ATrue, func1_M(?l1), X) && sll(x, ?l1)
    Ensure safeExec(ATrue, return(?l2), X) && sll(__return, ?l2)
 */
struct list * func1(struct list * x) {
    struct list * p = x;
    struct list * y = 0;
    
    /*@ Inv exists l1 l2 l3, safeExec(ATrue, bind(func1_M_loop(l1,l2,l3), func1_M_loop_end), X) && sllseg(x, p, l1) * sll(p, l2) * sll(y, l3) */
    while (p) {
        struct list * t = p->next;
        p->next = y;
        y = p;
        p = t;
    }
    return y;
}

/*@  With X
    Require safeExec(ATrue, func2_M(?l1, ?l2), X) && sll(x, ?l1) * sll(y, ?l2)
    Ensure safeExec(ATrue, return(?l3), X) && sll(__return, ?l3)
 */
struct list * func2(struct list * x, struct list * y) {
    struct list * p = x;
    
    /*@ Inv exists l1_1 l1_2 l1_3, safeExec(ATrue, bind(func2_M_loop(l1_1,l1_2,l1_3), func2_M_loop_end), X) && sllseg(x, p, l1_1) * sll(p, l1_2) * sll(y, l1_3) */
    while (p->next) {
        p = p->next;
    }
    
    p->next = y;
    
    struct list * curr = x;
    /*@ Inv exists l2_1 l2_2, safeExec(ATrue, bind(func2_M_loop(l2_1,l2_2), func2_M_loop_end), X) && sllseg(x, curr, l2_1) * sll(curr, l2_2) */
    while (curr) {
        curr = curr->next;
    }
    
    return x;
}
