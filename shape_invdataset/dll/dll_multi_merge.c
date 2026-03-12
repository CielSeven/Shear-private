#include "verification_stdlib.h"
#include "verification_list.h"
#include "dll_shape_def.h"

struct list *merge(struct list *x , struct list *y)
/*@ With x_prev 
    Require dlistrep_shape(x,x_prev) * dlistrep_shape(y,0)
    Ensure  dlistrep_shape(__return,x_prev)
 */;

struct list *dll_multi_merge(struct list *x , struct list *y, struct list *z)
/*@ Require dlistrep_shape(x,0) * dlistrep_shape(y,0) * dlistrep_shape(z,0)
    Ensure  dlistrep_shape(__return,0)
 */
{
    struct list *t,*u;
    if (x == 0) {
      t = merge(y,z);
      return t; 
    }
    else {
      t = x;
      u = t->next;
      /*@ Inv exists v, v == t -> data && u == t -> next && t != 0 &&
          dlistrep_shape(y,0) *
          dlistrep_shape(z,0) * 
          dlistrep_shape(u,t) *
          dllseg_shape(x@pre, 0, t->prev, t)
      */
      while (u) {
        if (y) {
          t -> next = y;
          y -> prev = t;
          t = y;
          u -> prev = t;
          y = y -> next;
          if (y) {
            y -> prev = 0;
          }    
        }
        else {
          u = merge(u , z);
          t -> next = u;
          return x;   
        }
        if (z) {
          t -> next = z;
          z -> prev = t;
          t = z;
          u -> prev = t;
          z = z -> next;
          if (z) {
            z -> prev = 0;
          }
        }
        else {
          u = merge(u , y);
          t -> next = u;
          return x;
        }
        t -> next = u;
        u -> prev = t;
        t = u;
        u = u -> next;
      }
  }
  u = merge(y,z);
  t -> next = u;
  if (u) {
    u -> prev = t;
  }
  return x;
}
