#include "verification_stdlib.h"
#include "verification_list.h"

struct list {
    int data;
    struct list *next;
};

/*@ Require listrep(x)
    Ensure  listrep(__return)
 */
struct list * func1(struct list * x) {
    struct list * p = x;
    struct list * y = 0;
    
    /*@ Inv lseg(x, p) * listrep(p) * listrep(y) */
    while (p) {
        struct list * t = p->next;
        p->next = y;
        y = p;
        p = t;
    }
    return y;
}

/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */
struct list * func2(struct list * x, struct list * y) {
    struct list * p = x;
    
    /*@ Inv lseg(x, p) * listrep(p) * listrep(y) */
    while (p->next) {
        p = p->next;
    }
    
    p->next = y;
    
    struct list * curr = x;
    /*@ Inv lseg(x, curr) * listrep(curr) */
    while (curr) {
        curr = curr->next;
    }
    
    return x;
}
