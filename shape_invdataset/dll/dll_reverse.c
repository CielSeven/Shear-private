#include "verification_stdlib.h"
#include "verification_list.h"
#include "dll_shape_def.h"

struct list *dll_reverse(struct list *p)
/*@ Require dlistrep_shape(p, 0)
    Ensure  dlistrep_shape(__return, 0)
 */
{
    struct list *w, *t, *v;
    w = (void *)0;
    v = p;
    /*@ Inv dlistrep_shape(w, v) *
        dlistrep_shape(v, w)
     */
    while (v) {
        t = v->next;
        v->next = w;
        v->prev = t;
        w = v;
        v = t;
    }
    return w;
}
