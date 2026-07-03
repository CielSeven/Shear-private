"""Tests for the segcodegen module (filling rel_lib holes from data-VC proofs)."""

import re

import pytest

from GenMonads.absprog.segcodegen import fill_template
from GenMonads.absprog.segcodegen.terms import (
    Op, Var, collect_var_types, parse_term, render,
)
from GenMonads.absprog.segcodegen.synth import referenced_funccalls
from GenMonads.absprog.segcodegen.vcparse import parse_blocks, parse_spec


def _vc(blocks, suffix):
    return next(b for b in blocks if b.name.endswith(suffix))


COPY_AUTOVC = '''#include "glibc_slist_clean_data.h"

struct list *glibc_slist_clean_copy(struct list *src)
/*@
    With l1
    Require sll(src, l1)
    Ensure exists l2 l3, sll(src@pre, l2) * sll(__return, l3)
 */
{
    /*@ Inv exists l1 l2 l3,
            src == src@pre && sllseg(src@pre, node, l1) * sll(node, l2) * sll(dst, l3) */
    while (node != 0) {
/* !!!
VC: glibc_slist_clean_copy_entail_wit_1
Precondition existentials (in context for this VC):
  l1_384_free
NestedSolver first solve exist_mapping:
l3_416 -> nil(Z)
l2_417 -> l1_384_free
l1_419 -> nil(Z)
Leftover left Props after solve:
(empty)
!!! */
/* !!!
VC: glibc_slist_clean_copy_entail_wit_2
Precondition existentials (in context for this VC):
  l3_421
  l2_422
  l1_424
NestedSolver first solve exist_mapping:
l3_416 -> l3_445
    [l3_445: from call to list_append_raw]
l2_417 -> l0_429_free
l1_419 -> app(Z, l1_424, cons(Z, x_427_free, nil(Z)))
Leftover left Props after solve:
PROP[
 retval_435 != (Ez_val 0);
 l2_422 == cons(Z, x_427_free, l0_429_free);
 node_423_value != (Ez_val 0) ]
!!! */
        copy = malloc_list_node(node->data);
        dst = list_append_raw(dst, copy);
/* !!!
VC: glibc_slist_clean_copy_funccall_wit_2   (call to list_append_raw)
Callee With-variable instantiation:
  l1_438_free -> l3_421
  l2_439_free -> cons(Z, x_427_free, nil(Z))
Postcondition existentials introduced:
  l3_445
  retval_446
Residual side-condition (partial solve) exist_mapping:
(empty)
!!! */
        node = node->next;
    }
    return dst;
/* !!!
VC: glibc_slist_clean_copy_return_wit_1
Precondition existentials (in context for this VC):
  l3_421
  l2_422
  l1_424
NestedSolver first solve exist_mapping:
l3_386 -> l3_421
l2_385 -> app(Z, l1_424, nil(Z))
Leftover left Props after solve:
PROP[
 l2_422 == nil(Z);
 node_423_value == (Ez_val 0) ]
!!! */
}
'''

COPY_TEMPLATE = '''Require Import list_append_raw_rel_lib.

Parameter MretTy : Type.

Parameter glibc_slist_clean_copy_M_loop_M1 : (list Z * list Z * list Z) -> MONAD MretTy.
Parameter glibc_slist_clean_copy_M_loop_M2 : (list Z * list Z * list Z) -> MONAD (list Z * list Z * list Z).

Parameter glibc_slist_clean_copy_M_loop_end : MretTy -> MONAD ((list Z * list Z)).

Parameter glibc_slist_clean_copy_M_loop_before : list Z -> MONAD (list Z * list Z * list Z).
'''


def _norm(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()


# ---- term parsing/rendering -------------------------------------------------

def test_parse_term_nil():
    assert parse_term("nil(Z)") == Op("nil", "Z", ())


def test_parse_term_cons_app():
    t = parse_term("app(Z, l1_424, cons(Z, x_427_free, nil(Z)))")
    assert t == Op("app", "Z", (
        Var("l1_424"),
        Op("cons", "Z", (Var("x_427_free"), Op("nil", "Z", ()))),
    ))


def test_render_substitutes_and_parenthesizes():
    t = parse_term("app(Z, l1_424, cons(Z, x_427_free, nil(Z)))")
    out = render(t, {"l1_424": "l1", "x_427_free": "x"})
    assert out == "l1 ++ (x :: nil)"


def test_collect_var_types_from_cons_signature():
    # types are inferred from the operator signature, not hardcoded
    t = parse_term("cons(Z, x_427_free, l0_429_free)")
    assert collect_var_types(t) == [("x_427_free", "Z"), ("l0_429_free", "list Z")]


# ---- spec / block parsing ---------------------------------------------------

def test_parse_spec():
    spec = parse_spec(COPY_AUTOVC)
    assert spec.with_vars == ["l1"]
    assert spec.carrier_vars == ["l1", "l2", "l3"]
    assert spec.ensure_vars == ["l2", "l3"]


def test_referenced_funccalls_scoping():
    blocks = parse_blocks(COPY_AUTOVC)
    # loop-entry and post-loop entailments consume no call results -> empty deps
    assert referenced_funccalls(_vc(blocks, "entail_wit_1"), blocks) == []
    assert referenced_funccalls(_vc(blocks, "return_wit_1"), blocks) == []
    # the loop-step VC depends only on list_append_raw (not malloc, a pointer call)
    step_deps = referenced_funccalls(_vc(blocks, "entail_wit_2"), blocks)
    assert [fb.call_target for fb in step_deps] == ["list_append_raw"]


def test_parse_blocks_provenance_and_funccall():
    blocks = parse_blocks(COPY_AUTOVC)
    step = next(b for b in blocks if b.name.endswith("entail_wit_2"))
    prov = {m.lhs: m.provenance for m in step.exist_mapping}
    assert prov["l3_416"] == "list_append_raw"
    fc = next(b for b in blocks if b.kind == "funccall")
    assert fc.with_instantiation["l1_438_free"] == "l3_421"
    assert "l3_445" in fc.post_exists


# ---- end-to-end fill --------------------------------------------------------

def test_fill_copy_all_holes():
    out = fill_template(COPY_TEMPLATE, COPY_AUTOVC)
    n = _norm(out)

    assert "Definition MretTy : Type := (list Z * list Z * list Z)." in n
    assert "fun r => return r." in n

    assert _norm(
        "fun l1 => return (nil, l1, nil)."
    ) in n  # M_loop_before

    assert _norm(
        "fun '(l1, l2, l3) => "
        "x <- any Z;; l2' <- any (list Z);; assume!! (l2 = x :: l2');; "
        "r <- list_append_raw_M l3 (x :: nil);; "
        "return (l1 ++ (x :: nil), l2', r)."
    ) in n  # M_loop_M2

    assert _norm(
        "fun '(l1, l2, l3) => assume!! (l2 = nil);; return (l1 ++ nil, l3)."
    ) in n  # M_loop_end — pure guard `l2 = nil` kept globally

    # holes are now Definitions, not Parameters
    assert "Parameter glibc_slist_clean_copy" not in out


def test_emit_order_follows_dependencies():
    # In copy, the call to list_append_raw consumes `x` (from the constraint),
    # so the constraint's `assume` must precede the call.
    out = fill_template(COPY_TEMPLATE, COPY_AUTOVC)
    body = out[out.index("M_loop_M2"):]
    assume_pos = body.index("assume!! (l2 = x :: l2')")
    call_pos = body.index("list_append_raw_M")
    assert assume_pos < call_pos


# A synthetic VC where the constraint destructs the *result* of a call: the
# call must now be emitted before the constraint (reverse of the copy order).
CALL_THEN_DESTRUCT_AUTOVC = '''
struct list *f(struct list *src)
/*@
    With l1
    Require sll(src, l1)
    Ensure exists l2 l3, emp
 */
{
    /*@ Inv exists l1 l2 l3, emp */
    while (cond) {
/* !!!
VC: f_entail_wit_1
Precondition existentials (in context for this VC):
  l1_4_free
NestedSolver first solve exist_mapping:
l3_16 -> nil(Z)
l2_17 -> l1_4_free
l1_19 -> nil(Z)
Leftover left Props after solve:
(empty)
!!! */
/* !!!
VC: f_entail_wit_2
Precondition existentials (in context for this VC):
  l3_21
  l2_22
  l1_24
NestedSolver first solve exist_mapping:
l3_16 -> nil(Z)
l2_17 -> tl_99_free
l1_19 -> app(Z, l1_24, cons(Z, hd_98_free, nil(Z)))
Leftover left Props after solve:
PROP[
 res_50 == cons(Z, hd_98_free, tl_99_free) ]
!!! */
        x = g(src);
/* !!!
VC: f_funccall_wit_2   (call to g)
Callee With-variable instantiation:
  a_30_free -> l1_24
Postcondition existentials introduced:
  res_50
Residual side-condition (partial solve) exist_mapping:
(empty)
!!! */
    }
    return dst;
/* !!!
VC: f_return_wit_1
Precondition existentials (in context for this VC):
  l3_21
  l2_22
  l1_24
NestedSolver first solve exist_mapping:
l3_16 -> l3_21
l2_15 -> l1_24
Leftover left Props after solve:
(empty)
!!! */
}
'''

CALL_THEN_DESTRUCT_TEMPLATE = '''
Parameter MretTy : Type.
Parameter f_M_loop_M1 : (list Z * list Z * list Z) -> MONAD MretTy.
Parameter f_M_loop_M2 : (list Z * list Z * list Z) -> MONAD (list Z * list Z * list Z).
Parameter f_M_loop_end : MretTy -> MONAD ((list Z * list Z)).
Parameter f_M_loop_before : list Z -> MONAD (list Z * list Z * list Z).
'''


APP_AUTOVC = '''#include "glibc_slist_clean_data.h"

struct list *glibc_slist_clean_app(struct list *x, struct list *y)
/*@
    With l1 l2
    Require sll(x, l1) * sll(y, l2)
    Ensure exists l3, sll(__return, l3)
 */
{
    return list_append_raw(x, y);
/* !!!
VC: glibc_slist_clean_app_return_wit_1
Precondition existentials (in context for this VC):
  l3_401
NestedSolver first solve exist_mapping:
l3_389 -> l3_401
    [l3_401: from call to list_append_raw]
Leftover left Props after solve:
(empty)
!!! */
/* !!!
VC: glibc_slist_clean_app_funccall_wit_1   (call to list_append_raw)
Callee With-variable instantiation:
  l1_397_free -> l1_388_free
  l2_398_free -> l2_387_free
Postcondition existentials introduced:
  l3_401
  retval_402
Residual side-condition (partial solve) exist_mapping:
(empty)
!!! */
}
'''

APP_TEMPLATE = '''Require Import list_append_raw_rel_lib.

Parameter glibc_slist_clean_app_M : list Z -> list Z -> MONAD (list Z).
'''


# A borrowing multi-result callee `dup` whose two list results carry *distinct*
# values (a preserved input `lp` and a fresh result `lq`).  The autovc lists the
# "Postcondition existentials introduced" in a DIFFERENT order (q before p) than
# the "Postcondition contributed by call" SEP, which reproduces the callee's
# Ensure order `sll(x@pre, lp) * sll(__return, lq)` == its result-tuple order.
# The `'(a, b)` destructure binds `fst`/`snd` positionally, so the projection
# must follow the SEP order, NOT the post_exists list order — otherwise every
# component is bound to the wrong logical value.
DUP_AUTOVC = '''#include "glibc_slist_clean_data.h"

struct list *dup_reuse(struct list *x)
/*@
    With l1
    Require sll(x, l1)
    Ensure exists lp lq, sll(x@pre, lp) * sll(__return, lq)
 */
{
    return dup(x);
/* !!!
VC: dup_reuse_funccall_wit_1   (call to dup)
Callee With-variable instantiation:
  a_30_free -> l1_10_free
Frame:
SEP[
 store(x_1_addr , x_1_pre , struct list*) ]
Postcondition existentials introduced:
  q_20
  p_21
  retval_22
Postcondition contributed by call (SEP, new existentials in place):
SEP[
 sll(x_1_pre, p_21);
 sll(retval_22, q_20) ]
Residual side-condition (partial solve) exist_mapping:
(empty)
!!! */
/* !!!
VC: dup_reuse_return_wit_1
Precondition existentials (in context for this VC):
  p_21
  q_20
NestedSolver first solve exist_mapping:
lp_8 -> p_21
lq_9 -> q_20
Leftover left Props after solve:
(empty)
!!! */
}
'''

DUP_TEMPLATE = "Parameter dup_reuse_M : list Z -> MONAD (list Z * list Z).\n"


def test_multi_result_projection_follows_post_sep_order():
    out = fill_template(DUP_TEMPLATE, DUP_AUTOVC)
    n = _norm(out)
    # p_21 is the SEP-first value (callee tuple slot 0 = `fst`), q_20 is slot 1.
    # The destructure binds `r=fst`, `r0=snd`, so the returned tuple must be
    # (r, r0): x@pre-preserved (lp=p_21=r) then __return (lq=q_20=r0).  With the
    # buggy post_exists ordering this would come out reversed as `(r0, r)`.
    assert _norm("'(r, r0) <- dup_M l1;; return (r, r0).") in n
    assert "return (r0, r)" not in n


def test_post_sep_parsed_and_orders_results():
    blocks = parse_blocks(DUP_AUTOVC)
    fc = next(b for b in blocks if b.kind == "funccall")
    # the introduced-existentials list is q,p (reversed) ...
    assert fc.post_exists[:2] == ["q_20", "p_21"]
    # ... but the contributed SEP puts p before q (the real tuple order).
    assert fc.post_sep == ["sll(x_1_pre, p_21)", "sll(retval_22, q_20)"]
    from GenMonads.absprog.segcodegen.synth import _post_sep_order
    rank = _post_sep_order(fc)
    assert rank["p_21"] < rank["q_20"]


def test_post_sep_order_appends_scalar_witness_last():
    # A callee like `list_tail` returns (prefix : list Z, last : Z).  Its
    # postcondition SEP lists the scalar `data == v` conjunct BEFORE the list
    # `sllseg(..., l2)`, yet `addabstract` appends the scalar data-witness LAST in
    # the result tuple `(l2, v)`.  So the faithful order is list-first even though
    # the scalar appears first in the SEP text.
    from GenMonads.absprog.segcodegen.vcparse import VCBlock
    from GenMonads.absprog.segcodegen.synth import _post_sep_order, _scalar_result_vars
    fb = VCBlock(name="f_funccall_wit_1", kind="funccall", call_target="pop")
    fb.post_exists = ["l2_20", "v_21", "retval_22"]
    fb.post_sep = [
        "store(&(retval_22->data) , v_21 , signed int)",
        "sllseg(x_1_pre, retval_22, l2_20)",
    ]
    # `v_21` is a scalar (non-pointer field store); the list `l2_20` is not.
    assert _scalar_result_vars(fb.post_sep) == {"v_21"}
    rank = _post_sep_order(fb)
    # list ranked before scalar, despite the scalar appearing first in the SEP.
    assert rank["l2_20"] < rank["v_21"]


def test_fill_app_no_loop():
    out = fill_template(APP_TEMPLATE, APP_AUTOVC)
    n = _norm(out)
    # curried binder over the two With-vars; the result of the call is returned
    assert _norm(
        "Definition glibc_slist_clean_app_M : list Z -> list Z -> MONAD (list Z) := "
        "fun l1 l2 => r <- list_append_raw_M l1 l2;; return r."
    ) in n
    assert "Parameter glibc_slist_clean_app_M" not in out


# A no-loop function with NO call: the With var sits directly in the context
# (nothing introduces it), so it is the root/input. No funccall tracing needed.
IDENTITY_AUTOVC = '''
struct list *idf(struct list *x)
/*@
    With l1
    Require sll(x, l1)
    Ensure exists l2, sll(__return, l2)
 */
{
    return x;
/* !!!
VC: idf_return_wit_1
Precondition existentials (in context for this VC):
  l1_10_free
NestedSolver first solve exist_mapping:
l2_8 -> l1_10_free
Leftover left Props after solve:
(empty)
!!! */
}
'''

IDENTITY_TEMPLATE = "Parameter idf_M : list Z -> MONAD (list Z).\n"


def test_no_loop_no_call_input_is_context_root():
    out = fill_template(IDENTITY_TEMPLATE, IDENTITY_AUTOVC)
    n = _norm(out)
    assert _norm("fun l1 => return l1.") in n


def test_call_before_constraint_when_constraint_destructs_result():
    out = fill_template(CALL_THEN_DESTRUCT_TEMPLATE, CALL_THEN_DESTRUCT_AUTOVC)
    body = out[out.index("f_M_loop_M2"):out.index("f_M_loop_end")]
    n = _norm(body)
    # `res_50` is produced by g_M and then destructed; the call precedes the assume
    assert n.index("g_M l1") < n.index("assume!!")
    # output uses the destructured components
    assert "return (l1 ++ (x :: nil), r', nil)" in n


# A branched loop body (outer step + inner `if`): two entail_wit_2_* VCs that
# share the first destructure and diverge on whether the tail is cons or nil.
REV2_AUTOVC = '''
struct list *f(struct list *x, struct list *y)
/*@
    With l1 l2
    Require sll(x, l1) * sll(y, l2)
    Ensure exists l3, sll(__return, l3)
 */
{
    /*@ Inv exists l1 l2, sll(x, l1) * sll(y, l2) */
    while (x != 0) {
/* !!!
VC: f_entail_wit_1
Precondition existentials (in context for this VC):
  l1_388_free
  l2_387_free
NestedSolver first solve exist_mapping:
l2_409 -> l2_387_free
l1_411 -> l1_388_free
Leftover left Props after solve:
(empty)
!!! */
/* !!!
VC: f_entail_wit_2_1
Precondition existentials (in context for this VC):
  l2_413
  l1_415
NestedSolver first solve exist_mapping:
l2_409 -> cons(Z, x_423_free, cons(Z, x_418_free, l2_413))
l1_411 -> l0_425_free
Leftover left Props after solve:
PROP[
 l0_420_free == cons(Z, x_423_free, l0_425_free);
 l1_415 == cons(Z, x_418_free, l0_420_free) ]
!!! */
/* !!!
VC: f_entail_wit_2_2
Precondition existentials (in context for this VC):
  l2_413
  l1_415
NestedSolver first solve exist_mapping:
l2_409 -> cons(Z, x_418_free, l2_413)
l1_411 -> nil(Z)
Leftover left Props after solve:
PROP[
 l0_420_free == nil(Z);
 l1_415 == cons(Z, x_418_free, l0_420_free) ]
!!! */
    }
    return y;
/* !!!
VC: f_return_wit_1
Precondition existentials (in context for this VC):
  l2_413
  l1_415
NestedSolver first solve exist_mapping:
l3_389 -> l2_413
Leftover left Props after solve:
PROP[
 l1_415 == nil(Z) ]
!!! */
}
'''

REV2_TEMPLATE = '''
Parameter MretTy : Type.
Parameter f_M_loop_M1 : (list Z * list Z) -> MONAD MretTy.
Parameter f_M_loop_M2 : (list Z * list Z) -> MONAD (list Z * list Z).
Parameter f_M_loop_end : MretTy -> MONAD (list Z).
Parameter f_M_loop_before : list Z -> list Z -> MONAD (list Z * list Z).
'''


def test_branched_loop_body_choice():
    out = fill_template(REV2_TEMPLATE, REV2_AUTOVC)
    m2 = out[out.index("f_M_loop_M2"):out.index("f_M_loop_end")]
    n = _norm(m2)
    # common prefix factored once
    assert n.count("assume!! (l1 = x :: l1')") == 1
    # composed with choice
    assert "choice" in n
    # arm 1: tail is a cons (destructure); arm 2: tail is nil (pure guard)
    assert "assume!! (l1' = x0 :: l1'')" in n
    assert "assume!! (l1' = nil)" in n
    assert "return (l1'', x0 :: (x :: l2))" in n
    assert "return (nil, x :: l2)" in n


def test_branched_arms_are_after_common_prefix():
    out = fill_template(REV2_TEMPLATE, REV2_AUTOVC)
    m2 = _norm(out[out.index("f_M_loop_M2"):out.index("f_M_loop_end")])
    # the shared destructure precedes the choice; the discriminators follow it
    assert m2.index("assume!! (l1 = x :: l1')") < m2.index("choice")
    assert m2.index("choice") < m2.index("assume!! (l1' = nil)")


# Chained calls: the first call's result is consumed *only* as the second
# call's argument (it never appears in the VC's own mappings/props).  It must
# still be recognized as a list result and bound, not leaked.
CHAINED_AUTOVC = '''
struct list *f(struct list *x, struct list *y, struct list *z)
/*@
    With l1 l2 l3
    Require sll(x, l1) * sll(y, l2) * sll(z, l3)
    Ensure exists l4, sll(__return, l4)
 */
{
    x = g(x, y);
/* !!!
VC: f_funccall_wit_1   (call to g)
Callee With-variable instantiation:
  a_1_free -> l1_92_free
  b_2_free -> l2_91_free
Postcondition existentials introduced:
  l3_405
  retval_406
Residual side-condition (partial solve) exist_mapping:
(empty)
!!! */
    x = g(x, z);
/* !!!
VC: f_funccall_wit_2   (call to g)
Callee With-variable instantiation:
  a_3_free -> l3_405
  b_4_free -> l3_90_free
Postcondition existentials introduced:
  l3_413
  retval_414
Residual side-condition (partial solve) exist_mapping:
(empty)
!!! */
    return x;
/* !!!
VC: f_return_wit_1
Precondition existentials (in context for this VC):
  l3_413
NestedSolver first solve exist_mapping:
l4_393 -> l3_413
    [l3_413: from call to g]
Leftover left Props after solve:
(empty)
!!! */
}
'''

CHAINED_TEMPLATE = "Parameter f_M : list Z -> list Z -> list Z -> MONAD (list Z).\n"


def test_chained_calls_first_result_not_leaked():
    out = fill_template(CHAINED_TEMPLATE, CHAINED_AUTOVC)
    n = _norm(out)
    # both calls emitted, second consuming the first's bound result
    assert _norm(
        "fun l1 l2 l3 => r <- g_M l1 l2;; r0 <- g_M r l3;; return r0."
    ) in n
    # no raw VC variable leaked into the body
    assert "l3_405" not in out and "l3_413" not in out


# --- region classification & loop-exit selection (early-return prelude) ------
from GenMonads.absprog.segcodegen import regions
from GenMonads.absprog.segcodegen.vcparse import VCBlock

EARLY_AUTOVC = '''
struct list *f(struct list *x, struct list *y)
/*@
    With l1 l2
    Require sll(x, l1) * sll(y, l2)
    Ensure exists l3, sll(__return, l3)
 */
{
    if (x == 0) { return y; }
/* !!!
VC: f_return_wit_3
Precondition existentials (in context for this VC):
  l1_8_free
  l2_9_free
NestedSolver first solve exist_mapping:
l3_389 -> l2_9_free
Leftover left Props after solve:
PROP[
 l1_8_free == nil(Z);
 x_385_pre == (Ez_val 0) ]
!!! */
/* !!!
VC: f_entail_wit_1
Precondition existentials (in context for this VC):
  l1_8_free
  l2_9_free
NestedSolver first solve exist_mapping:
l3_22 -> l2_9_free
l2_23 -> l1_8_free
l1_25 -> nil(Z)
Leftover left Props after solve:
PROP[
 x_385_pre != (Ez_val 0) ]
!!! */
    /*@ Inv exists l1 l2 l3, emp */
    while (y != 0) {
/* !!!
VC: f_entail_wit_2
Precondition existentials (in context for this VC):
  l3_20
  l2_21
  l1_22
NestedSolver first solve exist_mapping:
l3_22 -> l0_37
l2_23 -> l0_42
l1_25 -> l1_22
Leftover left Props after solve:
PROP[
 l3_20 == cons(Z, x_35, l0_37) ]
!!! */
/* !!!
VC: f_return_wit_2
Precondition existentials (in context for this VC):
  l3_20
  l2_21
  l1_22
NestedSolver first solve exist_mapping:
l3_389 -> app(Z, l1_22, l2_21)
Leftover left Props after solve:
PROP[
 l3_20 == cons(Z, x_35, l0_37);
 cursor_value != (Ez_val 0) ]
!!! */
    }
    return head;
/* !!!
VC: f_return_wit_1
Precondition existentials (in context for this VC):
  l3_20
  l2_21
  l1_22
NestedSolver first solve exist_mapping:
l3_389 -> app(Z, l1_22, l2_21)
Leftover left Props after solve:
PROP[
 l3_20 == nil(Z) ]
!!! */
}
'''


def test_region_classification():
    blocks = parse_blocks(EARLY_AUTOVC)
    assert regions.region(_vc(blocks, "return_wit_3")) == "before"
    assert regions.region(_vc(blocks, "entail_wit_1")) == "before"
    assert regions.region(_vc(blocks, "entail_wit_2")) == "loop"
    assert regions.region(_vc(blocks, "return_wit_2")) == "loop"
    assert regions.region(_vc(blocks, "return_wit_1")) == "loop"


def test_parse_guard():
    # a guard is a disjunction of atoms (single atom -> singleton list)
    assert regions.parse_guard("(*@ guard-struct: (atom l3 ne) @*)") == [("l3", "ne")]
    assert regions.parse_guard(
        "(*@ guard-struct: (or (atom l3 ne) (atom l4 ne)) @*)"
    ) == [("l3", "ne"), ("l4", "ne")]
    assert regions.parse_guard("no guard here") is None


def test_guard_is_false_disjunction():
    # the disjunctive guard is false only when BOTH atoms are pinned empty
    both = VCBlock(name="f_return_wit", kind="return",
                   leftover_props=["l3_1 == nil(Z)", "l4_1 == nil(Z)"])
    one = VCBlock(name="f_return_wit", kind="return",
                  leftover_props=["l3_1 == nil(Z)"])
    guard = [("l3", "ne"), ("l4", "ne")]
    assert regions.guard_is_false(both, guard)
    assert not regions.guard_is_false(one, guard)


def test_select_end_return_picks_loop_exit():
    blocks = parse_blocks(EARLY_AUTOVC)
    guard = [("l3", "ne")]
    end = regions.select_end_return(blocks, guard)
    # the loop-exit return (guard false: l3 == nil), NOT the before-loop early
    # return (return_wit_3) nor the in-loop early return (return_wit_2)
    assert end.name.endswith("return_wit_1")
    assert regions.guard_is_false(end, guard)
    assert not regions.guard_is_false(_vc(blocks, "return_wit_2"), guard)


def test_select_end_return_single_return_loop():
    # a plain loop function (one loop-region return) selects that return
    blocks = parse_blocks(COPY_AUTOVC)
    end = regions.select_end_return(blocks, regions.parse_guard("(atom l2 ne)"))
    assert end.name.endswith("return_wit_1")


# --- fact augmentation from the SEP antecedent --------------------------------
from GenMonads.absprog.segcodegen import facts

SEP_AUTOVC = '''
struct list *f(struct list *x, struct list *y)
/*@ With l1 l2 Require sll(x, l1) * sll(y, l2) Ensure exists l3, emp */
{
/* !!!
VC: f_entail_wit_1
Precondition existentials (in context for this VC):
  l1_8_free
  l2_9_free
Separation-logic state (antecedent P):
SEP[
 sll(x_385_pre, l1_8_free);
 sll(y_382_pre, l2_9_free) ]
NestedSolver first solve exist_mapping:
l3_22 -> l2_9_free
Leftover left Props after solve:
PROP[
 x_385_pre != (Ez_val 0) ]
!!! */
/* !!!
VC: f_return_wit_3
Precondition existentials (in context for this VC):
  l1_8_free
  l2_9_free
Separation-logic state (antecedent P):
SEP[
 sll(x_385_pre, l1_8_free);
 sll(y_382_pre, l2_9_free) ]
NestedSolver first solve exist_mapping:
l3_389 -> l2_9_free
Leftover left Props after solve:
PROP[
 l1_8_free == nil(Z);
 x_385_pre == (Ez_val 0) ]
!!! */
}
'''


def test_sep_parsed():
    blocks = parse_blocks(SEP_AUTOVC)
    assert _vc(blocks, "entail_wit_1").sep_state == [
        "sll(x_385_pre, l1_8_free)", "sll(y_382_pre, l2_9_free)"]


def test_derive_fact_continue_gets_non_nil():
    # sll(x, l1) + x != 0  =>  l1 != nil  (the Continue arm's list discriminator)
    blocks = parse_blocks(SEP_AUTOVC)
    assert facts.derive_facts(_vc(blocks, "entail_wit_1")) == ["l1_8_free != nil(Z)"]


def test_derive_fact_dedup_already_present():
    # sll(x, l1) + x == 0  =>  l1 == nil, but it's already in PROP -> nothing new
    blocks = parse_blocks(SEP_AUTOVC)
    assert facts.derive_facts(_vc(blocks, "return_wit_3")) == []


def test_augment_appends_in_place():
    blocks = parse_blocks(SEP_AUTOVC)
    facts.augment(blocks)
    assert "l1_8_free != nil(Z)" in _vc(blocks, "entail_wit_1").leftover_props


# An `early_result` function (cf. glibc_slist_merge): an early return before the
# loop (`if (x==0) return y`) and an early return inside it, plus the normal
# fall-through paths.  before/M2 are `MONAD (early_result carrier result)`.
EARLY_FILL_AUTOVC = '''
struct list *f(struct list *x, struct list *y)
/*@
    With l1 l2
    Require sll(x, l1) * sll(y, l2)
    Ensure exists l3, sll(__return, l3)
 */
{
    if (x == 0) {
        return y;
/* !!!
VC: f_return_wit_2
Precondition existentials (in context for this VC):
  l1_388_free
  l2_387_free
NestedSolver first solve exist_mapping:
l3_389 -> l2_387_free
Leftover left Props after solve:
PROP[
 l1_388_free == nil(Z) ]
!!! */
    }
    /*@ Inv exists l1 l2 l3, sll(x, l1) * sll(y, l2) * sll(head, l3) */
    while (y != 0) {
/* !!!
VC: f_entail_wit_1
Precondition existentials (in context for this VC):
  l1_388_free
  l2_387_free
NestedSolver first solve exist_mapping:
l1_500 -> l1_388_free
l2_501 -> l2_387_free
l3_502 -> nil(Z)
Leftover left Props after solve:
PROP[
 l1_388_free != nil(Z) ]
!!! */
/* !!!
VC: f_entail_wit_2
Precondition existentials (in context for this VC):
  l1_510
  l2_511
  l3_512
NestedSolver first solve exist_mapping:
l1_500 -> l0_520_free
l2_501 -> l2_511
l3_502 -> cons(Z, x_515_free, l3_512)
Leftover left Props after solve:
PROP[
 l1_510 == cons(Z, x_515_free, l0_520_free);
 l0_520_free != nil(Z) ]
!!! */
            return head;
/* !!!
VC: f_return_wit_3
Precondition existentials (in context for this VC):
  l1_510
  l2_511
  l3_512
NestedSolver first solve exist_mapping:
l3_389 -> l3_512
Leftover left Props after solve:
PROP[
 l1_510 == cons(Z, x_515_free, l0_520_free);
 l0_520_free == nil(Z) ]
!!! */
    }
    return head;
/* !!!
VC: f_return_wit_1
Precondition existentials (in context for this VC):
  l1_510
  l2_511
  l3_512
NestedSolver first solve exist_mapping:
l3_389 -> l3_512
Leftover left Props after solve:
PROP[
 l2_511 == nil(Z) ]
!!! */
}
'''

EARLY_TEMPLATE = '''
Parameter MretTy : Type.
Parameter f_M_loop_M1 : (list Z * list Z * list Z) -> MONAD MretTy.
Parameter f_M_loop_M2 : (list Z * list Z * list Z) -> MONAD (early_result (list Z * list Z * list Z) (list Z)).
(*@ guard-struct: (atom l2 ne) @*)
Parameter f_M_loop_end : MretTy -> MONAD (list Z).
Parameter f_M_loop_before : list Z -> list Z -> MONAD (early_result (list Z * list Z * list Z) (list Z)).
'''


def test_early_before_continue_and_returnnow():
    out = fill_template(EARLY_TEMPLATE, EARLY_FILL_AUTOVC)
    before = _norm(out[out.index("f_M_loop_before"):])
    # two complementary arms composed with choice
    assert "choice" in before
    assert "assume!! (l1 <> nil)" in before     # fall-through guard (from !=)
    assert "assume!! (l1 = nil)" in before       # early-return guard
    # Continue carries the carrier, ReturnNow the result `y` (= l2)
    assert "return Continue ((l1, l2, nil))" in before
    assert "return ReturnNow (l2)" in before


def test_early_m2_shares_prefix_then_continue_returnnow():
    out = fill_template(EARLY_TEMPLATE, EARLY_FILL_AUTOVC)
    m2 = _norm(out[out.index("f_M_loop_M2"):out.index("f_M_loop_end")])
    # the shared destructure of the carrier list is factored once, before choice
    assert m2.count("assume!! (l1 = x :: l1')") == 1
    assert m2.index("assume!! (l1 = x :: l1')") < m2.index("choice")
    # divergent, complementary guards -> Continue (carrier) vs ReturnNow (result)
    assert "assume!! (l1' <> nil)" in m2
    assert "assume!! (l1' = nil)" in m2
    assert "return Continue ((l1', l2, x :: l3))" in m2
    assert "return ReturnNow (l3)" in m2


def test_early_returns_unwrapped_end_and_m1():
    # M_loop_end (plain MONAD (list Z)) and M1 are unaffected by early_result.
    out = fill_template(EARLY_TEMPLATE, EARLY_FILL_AUTOVC)
    end = _norm(out[out.index("f_M_loop_end"):out.index("f_M_loop_before")])
    assert "Continue" not in end and "ReturnNow" not in end
    assert "assume!! (l2 = nil)" in end           # the guard-false loop exit


# --- witness / carrier refinement (Z data witness, pointer dropping) ----------
from GenMonads.absprog.segcodegen import witness as _witness
from GenMonads.absprog.segcodegen.vcparse import VCBlock as _VCBlock, Mapping as _Mapping


def _mkblk(name, mapping, props=None):
    b = _VCBlock(name=name, kind="entail")
    b.exist_mapping = [_Mapping(l, r) for l, r in mapping]
    b.leftover_props = list(props or [])
    return b


def test_tuple_kinds():
    assert _witness.tuple_kinds("(list Z * list Z * Z)") == ["list", "list", "witness"]
    assert _witness.tuple_kinds("((list Z * Z))") == ["list", "witness"]
    assert _witness.tuple_kinds("(list Z)") == ["list"]


def test_refine_drops_pointer_and_orders_witness_last():
    # Inv exists x_next x_v l1 l2, carrier (list Z * list Z * Z):
    # x_v is a `cons` element (Z witness); x_next only ever a pointer (dropped).
    b = _mkblk("f_entail_wit_1",
               [("l2_1", "l0_9_free"), ("l1_1", "nil(Z)"),
                ("x_v_1", "x_8_free"), ("x_next_1", "y_7_free")],
               props=["l1_5 == cons(Z, x_8_free, l0_9_free)"])
    out = _witness.refine(["x_next", "x_v", "l1", "l2"], [b], "(list Z * list Z * Z)")
    assert out == ["l1", "l2", "x_v"]


def test_refine_identity_for_all_lists():
    # a list var with no operator evidence (mapped to a bare var) keeps its slot
    b = _mkblk("f_entail_wit_1", [("l1_1", "nil(Z)"), ("l2_1", "l9_free")])
    assert _witness.refine(["l1", "l2"], [b], "(list Z * list Z)") == ["l1", "l2"]


# --- arithmetic data witness: registered infix `+`, EliminateLocal source -----
from GenMonads.absprog import segcodegen as _seg_init


def test_parse_and_render_registered_infix_add():
    t = parse_term("(s_410 + x_413_free)")
    assert t == Op("add", "Z", (Var("s_410"), Var("x_413_free")))
    assert render(t, {"s_410": "s", "x_413_free": "x"}) == "s + x"


def test_add_operands_typed_scalar_from_registry():
    # both operands of `+` are inferred `Z` (the registered scalar elem type)
    assert collect_var_types(parse_term("(s_410 + x_413_free)")) == [
        ("s_410", "Z"), ("x_413_free", "Z")]


def test_strip_ezval_in_scalar_context():
    assert _seg_init._strip_ezval("(Ez_val 0)") == "0"
    assert _seg_init._strip_ezval("(Ez_val 7)") == "7"
    assert _seg_init._strip_ezval("nil(Z)") == "nil(Z)"   # untouched otherwise


def test_eliminate_local_witness_merged_and_classified_scalar():
    b = _mkblk("f_entail_wit_2", [("l1_5", "nil(Z)"), ("l2_5", "l0_9_free")])
    b.eliminate_local = {"s_6": "(s_3 + x_8_free)", "ptr_value": "y_9"}
    _seg_init._merge_witness_substitutions([b], {"s", "l1", "l2"})
    merged = {m.lhs: m.rhs for m in b.exist_mapping}
    assert merged["s_6"] == "(s_3 + x_8_free)"   # witness lifted in
    assert "ptr_value" not in merged              # non-logical base left out
    # and it now classifies as a witness (add -> scalar result)
    assert _witness.refine(["s", "l1", "l2"], [b], "(list Z * list Z * Z)") == \
        ["l1", "l2", "s"]


# --- Z flag witness: scalar classification from an int store type -------------
from GenMonads.absprog.segcodegen import synth as _synth
from GenMonads.absprog.segcodegen.vcparse import scalar_witness_bases
from GenMonads.absprog.segcodegen.template import parse_template, Hole


def test_scalar_witness_bases_from_int_store():
    text = ("store(&take_y, int, ty) * store(&sum, long, s) * "
            "store(&stop, struct list*, st)")
    # int/long stores carry scalars; a `struct list*` store carries a pointer
    assert scalar_witness_bases(text) == {"ty", "s"}


def test_refine_flag_witness_via_store_type_orders_last():
    # `ty` is mapped only to a literal (no operator/type evidence), but it is a
    # scalar by its int store -> it must land in the trailing Z slot
    b = _mkblk("f_entail_wit_1", [("ty_4", "1"), ("l1_4", "nil(Z)")])
    assert _witness.refine(["ty", "l1"], [b], "(list Z * Z)", {"ty"}) == ["l1", "ty"]


# --- multi-result calls: destructure the callee's tuple result with a pattern -
def test_multi_result_call_destructures_components():
    fc = _VCBlock(name="f_funccall_wit_1", kind="funccall", call_target="g")
    fc.post_exists = ["p_1", "e_2", "ptr_3"]          # list, elem, pointer
    fc.with_instantiation = {"a_1": "l1_9"}
    vc = _VCBlock(name="f_return_wit_1", kind="return")
    vc.exist_mapping = [_Mapping("l2_1", "app(Z, p_1, cons(Z, e_2, nil(Z)))")]
    _binder, binds, ret = _synth.synth_parts(vc, [fc], ["l1"], ["l2"])
    joined = " ".join(binds + [ret])
    assert joined.count("g_M") == 1                     # one call, not twice
    # the tuple result is destructured with a pattern bind (no fst/snd)
    assert "'(r, r0) <- g_M l1" in _norm(joined)
    assert "fst" not in joined and "snd" not in joined
    assert _norm(ret) == "return (r ++ (r0 :: nil))"


# --- choice over >=3 arms must parenthesize the nested choice -----------------
def test_choice_chain_parenthesizes_nested():
    arms = [(["a;;"], "return x"), (["b;;"], "return y"), (["c;;"], "return z")]
    text = "\n".join(_synth._choice_lines(arms, ""))
    assert text.count("choice") == 2                    # two binary choices for 3 arms
    assert text.count("(") == text.count(")")           # balanced (nested wrapped)


# --- no-loop early-return shape: M_before / M_normal --------------------------
NOLOOP_TEMPLATE = '''Parameter MretTy : Type.
Parameter ap_M_before : list Z -> list Z -> MONAD (early_result MretTy (list Z)).
Parameter ap_M_normal : MretTy -> MONAD (list Z).
Definition ap_M : list Z -> list Z -> MONAD (list Z) := fun l1 l2 => return l1.
'''

NOLOOP_AUTOVC = '''
struct list *ap(struct list *x, struct list *y)
/*@
    With l1 l2
    Require sll(x, l1) * sll(y, l2)
    Ensure exists l3, sll(__return, l3)
 */
{
    if (x == 0) { return y;
/* !!!
VC: ap_return_wit_2
Precondition existentials (in context for this VC):
  l1_2_free
  l2_1_free
Separation-logic state (antecedent P):
SEP[
 sll(x_3_pre, l1_2_free);
 sll(y_4_pre, l2_1_free) ]
NestedSolver first solve exist_mapping:
l3_5 -> l2_1_free
Leftover left Props after solve:
PROP[
 l1_2_free == nil(Z);
 x_3_pre == (Ez_val 0) ]
!!! */
    }
    tail = lt(x);
/* !!!
VC: ap_funccall_wit_1   (call to lt)
Callee With-variable instantiation:
  a_9_free -> l1_2_free
Postcondition existentials introduced:
  p_10
  e_11
  rn_12
  rv_13
Residual side-condition (partial solve) exist_mapping:
(empty)
!!! */
    return x;
/* !!!
VC: ap_return_wit_1
Precondition existentials (in context for this VC):
  e_11
  p_10
  l2_1_free
Separation-logic state (antecedent P):
SEP[
 sllseg(x_3_pre, rv_13, p_10);
 sll(y_4_pre, l2_1_free) ]
NestedSolver first solve exist_mapping:
l3_5 -> app(Z, p_10, cons(Z, e_11, l2_1_free))
    [p_10: from call to lt]
    [e_11: from call to lt]
Leftover left Props after solve:
PROP[
 x_3_pre != (Ez_val 0) ]
!!! */
}
'''


def test_noloop_early_before_and_normal():
    out = fill_template(NOLOOP_TEMPLATE, NOLOOP_AUTOVC)
    n = _norm(out)
    # MretTy is the With-var tuple
    assert _norm("Definition MretTy : Type := (list Z * list Z).") in n
    # M_before: Continue threads inputs (guarded l1 <> nil), ReturnNow l2 on l1 = nil
    assert "Continue ((l1, l2))" in n
    assert "ReturnNow (l2)" in n
    assert "assume!! (l1 <> nil)" in n and "assume!! (l1 = nil)" in n
    # M_normal: the call's tuple result is destructured and appended
    assert "'(r, r0) <- lt_M l1" in n
    assert "return (r ++ (r0 :: l2))" in n


# --- loop forest: role recognition + identity glue ----------------------------
FOREST_TEMPLATE = '''Parameter MretTy : Type.
Parameter g_M_loop2_M1 : (list Z * Z) -> MONAD MretTy.
Parameter g_M_loop2_M2 : (list Z * Z) -> MONAD (list Z * Z).
Parameter g_M_loop1_M1 : (list Z * Z) -> MONAD MretTy.
Parameter g_M_loop1_to_inner_2 : (list Z * Z) -> MONAD (list Z * Z).
Parameter g_M_loop1_after_inner_2 : (list Z * Z) -> MretTy -> MONAD (list Z * Z).
Parameter g_M_loop1_before : list Z -> MONAD (list Z * Z).
Parameter g_M_loop1_end : MretTy -> MONAD (list Z * Z).
'''


def test_template_recognizes_forest_roles_and_carrier():
    tmpl = parse_template(FOREST_TEMPLATE)
    roles = {h.role for h in tmpl.holes}
    assert {"fM1", "fM2", "to_inner", "after_inner", "fbefore", "fend"} <= roles
    assert tmpl.func == "g"
    assert tmpl.carrier_type == "(list Z * Z)"


def test_loop_and_child_index():
    assert _seg_init._loop_index("f_M_loop2_M1") == 2
    assert _seg_init._loop_index("f_M_loop1_after_inner_2") == 1   # the *parent* loop
    assert _seg_init._loop_index("f_M") is None
    assert _seg_init._child_index("f_M_loop1_to_inner_2") == 2     # the *child* loop
    assert _seg_init._child_index("f_M_loop1_after_inner_2") == 2
    assert _seg_init._child_index("f_M_loop1_M2") is None


# end-to-end forest synthesis on the real two-loop case (skip if the bench file
# is not present) — the per-loop VC routing fills every glue hole faithfully.
import os as _os

_IB2_TMPL = "bench-gen/glibc_slist/libs/glibc_slist_iter_back_2_rel_lib.v"
_IB2_AVC = "bench-gen/glibc_slist/datac/autovc/glibc_slist_iter_back_2_data_autovc.c"


@pytest.mark.skipif(not (_os.path.exists(_IB2_TMPL) and _os.path.exists(_IB2_AVC)),
                    reason="iter_back_2 bench files not present")
def test_forest_fill_routes_per_loop_vcs():
    from GenMonads.absprog.segcodegen import fill_from_paths
    # the loop holes are `Parameter …_M_loop{k}_…`; once filled in place they are
    # `Definition`s, so there is nothing to synthesize — skip rather than error
    if not re.search(r"Parameter\s+\w+_M_loop\d+_", open(_IB2_TMPL).read()):
        pytest.skip("iter_back_2 lib already filled in place (no holes)")
    n = _norm(fill_from_paths(_IB2_TMPL, _IB2_AVC))
    # per-loop result types defined (not the single shared MretTy); the outer
    # invariant `lseg(x, stop) * listrep(stop)` gives loop1 a two-list carrier
    assert "_M_loop1_MretTy : Type := (list Z * list Z * Z)" in n
    assert "_M_loop2_MretTy : Type := (list Z * list Z * Z)" in n
    # to_inner: outer (l1_1, l1_2, s) -> inner (nil, whole list, s)
    assert "return (nil, l1_1 ++ l1_2, s)" in n
    # after_inner: with the strengthened outer invariant the continue-path
    # entailment is closed trivially (no VC), so the resume is the identity —
    # pass the inner result through as the new outer carrier
    assert "fun a r => return r." in n
    # loop1_end projects the list result (witness dropped) — not a tuple
    assert _norm("return (l1_1 ++ l1_2).") in n
    # break branches stay the fixed identity
    assert "fun r => return r." in n


# --- recursion: a self-call yields a structural Fixpoint over a match ----------
RECURSIVE_TEMPLATE = "Parameter rf_M : list Z -> MONAD (list Z).\n"

RECURSIVE_AUTOVC = '''
long rf(struct list *x)
/*@
    With l1
    Require sll(x, l1)
    Ensure exists l2 v, __return == v && sll(x@pre, l2)
 */
{
    if (x == 0) { return 0;
/* !!!
VC: rf_return_wit_2
Precondition existentials (in context for this VC):
  l1_4_free
Separation-logic state (antecedent P):
SEP[
 sll(x_2_pre, l1_4_free) ]
NestedSolver first solve exist_mapping:
l2_5 -> nil(Z)
v_6 -> (Ez_val 0)
Leftover left Props after solve:
PROP[
 l1_4_free == nil(Z);
 x_2_pre == (Ez_val 0) ]
!!! */
    }
    sum = rf(x->next);
/* !!!
VC: rf_funccall_wit_1   (call to rf)
Callee With-variable instantiation:
  l1_11_free -> l0_9_free
Postcondition existentials introduced:
  l2_15
  v_16
  retval_17
Residual side-condition (partial solve) exist_mapping:
(empty)
!!! */
    return sum + x->data;
/* !!!
VC: rf_return_wit_1
Precondition existentials (in context for this VC):
  x_7_free
  l2_15
  v_16
  l1_4_free
  l0_9_free
Separation-logic state (antecedent P):
SEP[
 sll(y_8_free, l2_15) ]
NestedSolver first solve exist_mapping:
l2_5 -> cons(Z, x_7_free, l2_15)
    [l2_15: from call to rf]
v_6 -> (retval_17 + x_7_free)
Leftover left Props after solve:
PROP[
 retval_17 == v_16;
 l1_4_free == cons(Z, x_7_free, l0_9_free);
 x_2_pre != (Ez_val 0) ]
!!! */
}
'''


def test_recursion_emits_structural_fixpoint():
    out = fill_template(RECURSIVE_TEMPLATE, RECURSIVE_AUTOVC)
    n = _norm(out)
    assert "Fixpoint rf_M (l1 : list Z) : MONAD (list Z)" in n
    assert "match l1 with" in n
    assert "| nil => return nil" in n
    # the recursion is on the matched tail (structural), result rebuilds the list;
    # the numeric return feeds only the dropped witness, so `r` is NOT projected
    assert "| x :: l1' =>" in n
    assert "r <- rf_M l1'" in n
    assert "return (x :: r)" in n
    assert "fst r" not in n and "snd r" not in n


# ---------------------------------------------------------------------------
# Frame-based function-call residual (continuation) generation.
# The inner-loop tail is the degenerate empty-frame case of this same splice;
# a real function call differs only by carrying a non-empty, mandatory frame.

_APPEND_AVC = "bench-gen/glibc_slist/datac/autovc/list_append_raw_data_autovc.c"
_COPY_AVC = "bench-gen/glibc_slist/datac/autovc/glibc_slist_copy_data_autovc.c"


@pytest.mark.skipif(not _os.path.exists(_APPEND_AVC),
                    reason="list_append_raw autovc not present")
def test_residual_list_tail_threads_frame_list():
    from GenMonads.absprog.segcodegen.residual import build_all_residuals
    rds = build_all_residuals(open(_APPEND_AVC).read())
    assert len(rds) == 1
    rd = rds[0]
    # the callee `list_tail` returns (prefix, last); the frame carries `l2` (the
    # appended list, the With-var) untouched, so the residual closes over `l2`.
    assert rd.callee == "list_tail"
    assert rd.params == ["l2"]
    assert ": (list Z * Z) -> MONAD (list Z) :=" in rd.definition
    body = _norm(rd.definition)
    # result tuple destructured, frame `l2` re-appended after the popped element
    assert "fun '(r0, v) =>" in body
    assert "return (r0 ++ (v :: l2))" in body


# A CHAINED list_tail residual where the scalar `v` (the popped element) is used
# only inside a DOWNSTREAM call's argument (`list_append_raw(prefix ++ (v::y), z)`),
# never in the owner's own output.  So `_type_map` (owner output only) can't type
# `v`, and `scalar_witness_bases` (simple `&name` stores only) misses the field
# store `store(&(_->data), v, int)`.  Without pulling the scalar from the call's
# post_sep the residual mistypes `v` as `list Z` and `v :: l2` is ill-typed.
TAIL_CHAIN_AVC = '''#include "glibc_slist_clean_data.h"

struct list *tail_chain(struct list *x, struct list *y, struct list *z)
/*@ With l1 l2 l3
    Require x != 0 && sll(x, l1) * sll(y, l2) * sll(z, l3)
    Ensure exists l4, sll(__return, l4)
 */
{
    tail = list_tail(x);
/* !!!
VC: tail_chain_funccall_wit_1   (call to list_tail)
Callee With-variable instantiation:
  l1_417_free -> l1_403_free
Frame:
SEP[
 sll(y_396_pre, l2_402_free);
 sll(z_393_pre, l3_401_free) ]
Postcondition existentials introduced:
  l2_422
  v_423
  retval_next_424
  retval_425
Postcondition contributed by call (SEP, new existentials in place):
SEP[
 store(&(retval_425->next) , retval_next_424 , struct list*);
 store(&(retval_425->data) , v_423 , signed int);
 sllseg(x_399_pre, retval_425, l2_422) ]
Residual side-condition (partial solve) exist_mapping:
(empty)
!!! */
    r = list_append_raw(x, z);
/* !!!
VC: tail_chain_funccall_wit_2   (call to list_append_raw)
Callee With-variable instantiation:
  l1_428_free -> app(Z, l2_422, cons(Z, v_423, l2_402_free))
  l2_429_free -> l3_401_free
Frame:
SEP[
 store(x_400_addr , x_399_pre , struct list*) ]
Postcondition existentials introduced:
  l3_436
  retval_437
Postcondition contributed by call (SEP, new existentials in place):
SEP[
 sll(retval_437, l3_436) ]
Residual side-condition (partial solve) exist_mapping:
(empty)
!!! */
    return r;
/* !!!
VC: tail_chain_return_wit_1
Precondition existentials (in context for this VC):
  l3_436
NestedSolver first solve exist_mapping:
l4_404 -> l3_436
    [l3_436: from call to list_append_raw]
Leftover left Props after solve:
(empty)
!!! */
}
'''


def test_residual_chained_list_tail_scalar_typed_Z():
    from GenMonads.absprog.segcodegen.residual import build_all_residuals
    rds = build_all_residuals(TAIL_CHAIN_AVC)
    rd = next(r for r in rds if r.callee == "list_tail")
    # the popped element `v` is a scalar (field store, int) -> the callee-result
    # tuple must be (list Z * Z), NOT (list Z * list Z); and the downstream append
    # is re-emitted with `v :: l2` (needs `v : Z`).
    assert ": (list Z * Z) -> MONAD (list Z) :=" in rd.definition
    body = _norm(rd.definition)
    assert "fun '(r0, v) =>" in body
    assert "(r0 ++ (v :: l2))" in body


@pytest.mark.skipif(not _os.path.exists(_COPY_AVC),
                    reason="glibc_slist_copy autovc not present")
def test_residual_copy_loop_body_call():
    from GenMonads.absprog.segcodegen.residual import build_all_residuals
    rds = build_all_residuals(open(_COPY_AVC).read())
    # malloc has no logical (list) result -> no residual; only the
    # list_append_raw call produces a continuation.
    assert [rd.callee for rd in rds] == ["list_append_raw"]
    rd = rds[0]
    # FAITHFUL residual: the parameters are the SE fresh variables the loop body
    # already unfolded at the call site (the frame `store(&node->data, x) *
    # sll(y, l0) * sllseg(.., l1)`), captured verbatim — the head/tail (x, l0) are
    # NOT re-derived inside via any+assume, and the whole list `l2` is NOT a param.
    assert rd.params == ["x", "l0", "l1"]
    assert "l2" not in rd.params
    body = _norm(rd.definition)
    assert "fun r0 =>" in body
    assert "any" not in body                       # nothing re-derived
    assert "assume" not in body
    # all three params are loop-scoped (Inv carrier / unfold pieces), so each needs
    # a call-site `/*@ Given … */`; none is a `With` precondition var.
    assert rd.given_params == ["x", "l0", "l1"]
    # the residual is the continuation of the *whole function*: after computing
    # the next carrier (l1 ++ [x], l0, dst') it resumes the loop and applies the
    # post-loop tail, so it yields the function result `MONAD (list Z * list Z)`.
    assert ": list Z -> MONAD (list Z * list Z) :=" in rd.definition
    assert "re <- glibc_slist_clean_copy_M_loop_aux (l1 ++ (x :: nil), l0, r0);;" in body
    assert "glibc_slist_clean_copy_M_loop_end re" in body


@pytest.mark.skipif(not _os.path.exists(_COPY_AVC),
                    reason="glibc_slist_copy autovc not present")
def test_fill_template_appends_residual_to_rel_lib():
    # a frame-enriched funccall block makes fill_template append the residual
    # Definition after the filled holes (self-recursion / frameless calls do not).
    tmpl = (
        "Parameter MretTy : Type.\n"
        "Parameter glibc_slist_clean_copy_M_loop_before : list Z -> MONAD MretTy.\n"
        "Parameter glibc_slist_clean_copy_M_loop_M1 : MretTy -> MONAD MretTy.\n"
        "Parameter glibc_slist_clean_copy_M_loop_M2 : (list Z * list Z * list Z) -> MONAD MretTy.\n"
        "Parameter glibc_slist_clean_copy_M_loop_end : (list Z * list Z * list Z) -> MONAD (list Z * list Z).\n"
    )
    out = fill_template(tmpl, open(_COPY_AVC).read())
    n = _norm(out)
    # the holes are still filled as before (call inlined in the loop body) ...
    assert "Definition glibc_slist_clean_copy_M_loop_M2" in n
    assert "r <- list_append_raw_M l3 (x :: nil);;" in n
    # ... and the residual continuation is appended as its own Definition that
    # resumes the loop and runs to the function result (M_loop_end appears).
    assert ("Definition residual_prog_in_glibc_slist_clean_copy_M_call_2 "
            "(x : Z) (l0 : list Z) (l1 : list Z)") in n
    assert "re <- glibc_slist_clean_copy_M_loop_aux (l1 ++ (x :: nil), l0, r0);;" in n
    assert "glibc_slist_clean_copy_M_loop_end re" in n


# ---- frame_sep: proof-block frame -> `/*@ exists …, … */` C assertion ---------

def test_translate_frame_sep_copy_reference():
    # exactly the hand-written assertion in glibc_slist_copy_rel_try.c: field
    # stores + heap preds kept, local-var cells dropped, vars renamed, store args
    # reordered to (addr, type, value), `signed int` -> `int`, existentials bound.
    from GenMonads.absprog.segcodegen.frame_sep import translate_frame_sep
    frame = [
        "store(&(node_423_value->data) , x_427_free , signed int)",
        "sll(y_428_free, l0_429_free)",
        "store(&(node_423_value->next) , y_428_free , struct list*)",
        "store(src_383_addr , src_382_pre , struct list*)",
        "store(copy_400_addr , retval_435 , struct list*)",
        "store(node_397_addr , node_423_value , struct list*)",
        "sllseg(src_382_pre, node_423_value, l1_424)",
        "store(dst_394_addr , dst_420_value , struct list*)",
    ]
    assert translate_frame_sep(frame) == (
        "/*@ exists x y l0 l1,\n"
        "    store(&(node->data), int, x) *\n"
        "    sll(y, l0) *\n"
        "    store(&(node->next), struct list*, y) *\n"
        "    sllseg(src@pre, node, l1) */"
    )


def test_translate_frame_sep_drops_noise_and_renames():
    from GenMonads.absprog.segcodegen.frame_sep import translate_frame_sep
    frame = [
        "has_permission( copy_400_addr , struct list*)",   # dropped
        "undef_data_at(&copy, struct list*)",              # dropped
        "store(x_372_addr , x_371_pre , struct list*)",    # dropped: local cell
        "sll(y_368_pre, l2_381_free)",                     # kept: `_pre` in scope
    ]
    # `y_368_pre` is a program pre-value (in scope) -> not bound; only `l2` is.
    assert translate_frame_sep(frame) == "/*@ exists l2,\n    sll(y@pre, l2) */"


def test_translate_frame_sep_strips_only_leading_signed():
    from GenMonads.absprog.segcodegen.frame_sep import translate_frame_sep
    out = translate_frame_sep([
        "store(&(p_1_value->c), a_2_free, signed char)",
        "store(&(p_1_value->n), b_3_free, unsigned int)",
    ])
    assert "store(&(p->c), char, a)" in out       # signed char -> char
    assert "store(&(p->n), unsigned int, b)" in out  # unsigned int untouched


def test_translate_frame_sep_empty_when_nothing_kept():
    from GenMonads.absprog.segcodegen.frame_sep import translate_frame_sep
    assert translate_frame_sep([
        "store(a_1_addr , b_2_pre , struct list*)",
        "has_permission( c_3_addr , int)",
    ]) == ""


def test_translate_frame_sep_with_vars_not_rebound():
    # a `With` precondition var in the frame (`l2_381_free`, base `l2` in With) is
    # already in scope -> rendered but NOT existentially re-bound.
    from GenMonads.absprog.segcodegen.frame_sep import translate_frame_sep
    frame = ["sll(y_368_pre, l2_381_free)"]
    assert translate_frame_sep(frame, with_vars=["l1", "l2"]) == "/*@ sll(y@pre, l2) */"
    # but a bare `_<id>` carrier (l1_424) whose base also names a With var IS bound
    frame2 = ["sllseg(src_382_pre, node_423_value, l1_424)"]
    assert translate_frame_sep(frame2, with_vars=["l1"]) == \
        "/*@ exists l1,\n    sllseg(src@pre, node, l1) */"


@pytest.mark.skipif(not _os.path.exists(_COPY_AVC),
                    reason="glibc_slist_copy autovc not present")
def test_residual_copy_carries_frame_sep():
    from GenMonads.absprog.segcodegen.residual import build_all_residuals
    rd = build_all_residuals(open(_COPY_AVC).read())[0]
    assert rd.frame_sep == (
        "/*@ exists x y l0 l1,\n"
        "    store(&(node->data), int, x) *\n"
        "    sll(y, l0) *\n"
        "    store(&(node->next), struct list*, y) *\n"
        "    sllseg(src@pre, node, l1) */"
    )


@pytest.mark.skipif(not _os.path.exists(_COPY_AVC),
                    reason="glibc_slist_copy autovc not present")
def test_inject_emits_frame_block_then_given_then_cont():
    from GenMonads.absprog.segcodegen.residual import inject_residual_annotations
    relc = (
        '/*@ Import Coq Require Import glibc_slist_copy_rel_lib */\n'
        '/*@ Extern Coq (maketuple: {A} {B} -> A -> B -> (A * B)) */\n'
        '    while (node != 0) {\n'
        '        copy = malloc_list_node(node->data);\n'
        '        dst = list_append_raw(dst, copy) '
        '/*@ where(low_level_spec_aux) X = X; B = (list Z * list Z) */;\n'
        '        node = node->next;\n'
        '    }\n'
    )
    out = inject_residual_annotations(relc, open(_COPY_AVC).read())
    # frame existentials get the distinct `_frame` spelling (so a function-scoped
    # `Given` can't clash across calls); ambient vars/program vars are untouched.
    # The frame assertion precedes the Given, which precedes the call+cont.
    assert "/*@ Extern Coq (residual_prog_in_glibc_slist_clean_copy_M_call_2:" in out
    assert "        /*@ exists x_frame y_frame l0_frame l1_frame,\n" in out
    assert "            store(&(node->data), int, x_frame) *\n" in out
    assert "            sllseg(src@pre, node, l1_frame) */\n" in out       # program var `node`/`src@pre` untouched
    assert "        /*@ Given x_frame l0_frame l1_frame */\n" in out
    assert "cont = residual_prog_in_glibc_slist_clean_copy_M_call_2(x_frame, l0_frame, l1_frame);" in out
    # ordering: exists block -> Given -> call
    assert out.index("exists x_frame") < out.index("/*@ Given x_frame") \
        < out.index("cont = residual_prog_in_glibc_slist_clean_copy_M_call_2")


def test_frame_rename_maps_disambiguates_per_caller():
    # two calls in one caller both frame-introduce `l2` -> first `l2_frame`, second
    # `l2_2_frame`, so the function-scoped `Given`s don't collide.  A different
    # caller restarts the counter.
    from GenMonads.absprog.segcodegen.residual import _frame_rename_maps, ResidualDef

    def mk(caller, idx):
        return ResidualDef(
            name=f"residual_prog_in_{caller}_call_{idx}", definition="", params=["l2"],
            result_binder="r", callee="c", call_index=idx, given_params=["l2"],
            frame_sep="/*@ exists l2,\n    sll(x@pre, l2) */")

    r2, r3, other = mk("f_M", 2), mk("f_M", 3), mk("g_M", 1)
    maps = _frame_rename_maps([r2, r3, other])
    assert maps[id(r2)] == {"l2": "l2_frame"}
    assert maps[id(r3)] == {"l2": "l2_2_frame"}      # second use in same caller
    assert maps[id(other)] == {"l2": "l2_frame"}     # different caller -> counter resets
