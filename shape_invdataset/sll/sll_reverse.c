#include "verification_stdlib.h"
#include "verification_list.h"
#include "sll_shape_def.h"



struct list* sll_reverse(struct list* head) 
/*@ 
      Require listrep(head)
      Ensure listrep(__return)
*/
{
    struct list* prev = (void *)0;
    struct list* curr = head;
    /*@ Inv listrep(prev) * listrep(curr) 
      */
    while (curr != (void *) 0) {
        struct list* next = curr->next;
        curr->next = prev;
        prev = curr;
        curr = next;
    }
    return prev;
}

