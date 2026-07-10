#include "glibc_slist_clean.h"

/* two_call_reuse — the residual-generation stress case.
 *
 *   a = copy(x);            call 1: a is fresh; x preserved (borrowing copy)
 *   b = copy(a);            call 2: b is fresh; a preserved. a is call-1's RESULT
 *   return append(a, b);    uses a AGAIN, after call 2, alongside b
 *
 * The key property: a — the result of call 1 — flows past call 2 (it is both
 * call-2's input and is consumed again afterwards).  For call 2's residual
 * (continuation append(a, b)), a is an arbitrary earlier call result, not a
 * With/carrier var nor a cons-split of one — the chained-call residual case.
 *
 * glibc_slist_clean_copy is exactly the borrowing copy we need: it preserves its
 * argument (sll(src@pre, _)) and returns a fresh list.  Expected: la ++ lb. */
struct list *two_call_reuse(struct list *x)
/*@ Require listrep(x)
    Ensure  listrep(x@pre) * listrep(__return)
 */
{
    struct list *a;
    struct list *b;

    a = glibc_slist_clean_copy(x);
    b = glibc_slist_clean_copy(a);
    return list_append_raw(a, b);
}
