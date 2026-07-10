struct list {
    int data;
    struct list *next;
};

/*@ Extern Coq (listrep : Z -> Assertion)
               (lseg: Z -> Z -> Assertion)
               (listboxseg: Z -> Z -> Assertion)
               (sll_tag : Z -> Prop)
 */

/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.sll_shape_lib */

/*@ include strategies "sll_shape.strategies" */

struct list *malloc_list_node(int data)
/*@ With data0 
    Require data == data0 && emp
    Ensure __return != 0 && __return -> data == data0 && __return -> next == 0
*/;
void free_list_node(struct list *x)
/*@ With d n 
    Require x -> data == d && x -> next == n
    Ensure emp
*/;
void glibc_slist_clean_free(struct list *x)
/*@ Require listrep(x)
    Ensure  emp
 */;
struct list *list_tail(struct list *x)
/*@ Require x != 0 && listrep(x)
    Ensure  exists v, __return != 0 &&
            __return -> next == 0 &&
            __return -> data == v &&
            lseg(x, __return)
*/;
struct list *list_append_raw(struct list *x, struct list *y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */;
struct list *glibc_slist_clean_copy(struct list *src)
/*@ Require listrep(src)
    Ensure  listrep(src@pre) * listrep(__return)
 */;
