struct list {
    struct list *next;
    struct list *prev;
    int data;
};

/*@ Extern Coq (dlistrep_shape : Z -> Z -> Assertion)
               (dllseg_shape: Z -> Z -> Z -> Z -> Assertion)
               (dll_tag : Z -> Z -> Prop)
 */

/*@ Import Coq Require Import dll_shape_lib */

/*@ include strategies "dll_shape.strategies" */