struct list {
    struct list *next;
    struct list *prev;
    int data;
};

/*@ Extern Coq (dlistrep_shape : Z -> Z -> Assertion)
               (dllseg_shape: Z -> Z -> Z -> Z -> Assertion)
               (dll_tag : Z -> Z -> Prop)
 */

/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.dll_shape_lib */

/*@ include strategies "dll_shape.strategies" */


struct list *malloc_dlist(int data)
    /*@ With data0 
    Require data == data0 && emp
    Ensure __return != 0 && __return -> data == data0 && __return -> next == 0 && __return -> prev == 0
*/
    ;

void free_dlist(struct list *x)
    /*@ With d n p
    Require x -> data == d && x -> next == n && x -> prev == p
    Ensure emp
*/
    ;

struct list *merge(struct list *x, struct list *y)
    /*@ With x_prev
    Require dlistrep_shape(x, x_prev) * dlistrep_shape(y, 0)
    Ensure  dlistrep_shape(__return, x_prev)
 */
    ;
