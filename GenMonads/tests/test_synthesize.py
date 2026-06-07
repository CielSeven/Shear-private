import json
import os
import subprocess

import pytest

from GenMonads.absprog.assemble import assemble_rel_lib_from_blocks
from GenMonads.absprog.context import collect_synthesis_context
from GenMonads.absprog.parse_coq import parse_synthesized_components
from GenMonads.absprog.synthesize import (
    _append_missing_residual_decls_to_rel_c,
    _eliminate_mretty_in_rel_c,
    _extract_mretty_type,
    _promote_rel_lib_if_accepted,
    _sync_residual_artifacts,
    _validate_opaque_callee_usage,
    generate_candidate_response,
    run_synthesis_pipeline,
)
from GenMonads.absprog.templates import render_prompt, render_repair_prompt


_GOLD_DATA = {
    "MretTy": "list Z",
    "components": {
        "M_loop_before": (
            "Definition sll_reverse_M_loop_before : list Z -> MONAD (list Z * list Z) :=\n"
            "  fun l => return (nil, l)."
        ),
        "M_1": (
            "Definition sll_reverse_M_loop_M1 : (list Z * list Z) -> MONAD MretTy:=\n"
            "  fun '(l1,l2) => return l1."
        ),
        "M_2": (
            "Definition sll_reverse_M_loop_M2 : (list Z * list Z) -> MONAD (list Z * list Z) :=\n"
            "  fun '(l1,l2) =>\n"
            "    match l2 with\n"
            "    | nil => return (l1,l2)\n"
            "    | v :: l2' => return (v :: l1, l2')\n"
            "    end."
        ),
        "M_loop_end": (
            "Definition sll_reverse_M_loop_end : MretTy -> MONAD (list Z):=\n"
            "  fun l => return l."
        ),
    },
}


# Synthetic in-test C sources mirroring the shapes used by the synthesis
# pipeline tests.  Kept in the test module so the suite is self-contained.
_SLL_REVERSE_SRC = (
    '#include "verification_list.h"\n'
    '#include "sll_shape_def.h"\n'
    '\n'
    'struct list* sll_reverse(struct list* head)\n'
    '/*@\n'
    '      Require listrep(head)\n'
    '      Ensure  listrep(__return)\n'
    '*/\n'
    '{\n'
    '    struct list* prev = (void *)0;\n'
    '    struct list* curr = head;\n'
    '    /*@ Inv listrep(prev) * listrep(curr) */\n'
    '    while (curr != (void *) 0) {\n'
    '        struct list* next = curr->next;\n'
    '        curr->next = prev;\n'
    '        prev = curr;\n'
    '        curr = next;\n'
    '    }\n'
    '    return prev;\n'
    '}\n'
)

_SLL_MULTI_MERGE_SRC = (
    '#include "verification_list.h"\n'
    '#include "sll_shape_def.h"\n'
    '\n'
    'struct list { int data; struct list *next; };\n'
    '\n'
    'struct list * sll_merge(struct list * x, struct list * y)\n'
    '/*@ Require listrep(x) * listrep(y)\n'
    '    Ensure  listrep(__return)\n'
    ' */;\n'
    '\n'
    'struct list * sll_multi_merge(struct list * x, struct list * y, struct list * z)\n'
    '/*@ Require listrep(x) * listrep(y) * listrep(z)\n'
    '    Ensure  listrep(__return)\n'
    ' */\n'
    '{\n'
    '    struct list *t, *u;\n'
    '    if (x == (struct list *) 0) {\n'
    '        t = sll_merge(y, z);\n'
    '        return t;\n'
    '    }\n'
    '    t = x;\n'
    '    u = t->next;\n'
    '    /*@ Inv exists v, v == t -> data && u == t -> next && t != 0 &&\n'
    '            listrep(y) * listrep(z) * listrep(u) * lseg(x@pre, t) */\n'
    '    while (u) {\n'
    '        if (y) {\n'
    '            t->next = y;\n'
    '            t = y;\n'
    '            y = y->next;\n'
    '        } else {\n'
    '            u = sll_merge(u, z);\n'
    '            t->next = u;\n'
    '            return x;\n'
    '        }\n'
    '        if (z) {\n'
    '            t->next = z;\n'
    '            t = z;\n'
    '            z = z->next;\n'
    '        } else {\n'
    '            u = sll_merge(u, y);\n'
    '            t->next = u;\n'
    '            return x;\n'
    '        }\n'
    '        t->next = u;\n'
    '        t = u;\n'
    '        u = u->next;\n'
    '    }\n'
    '    u = sll_merge(y, z);\n'
    '    t->next = u;\n'
    '    return x;\n'
    '}\n'
)


def _write_sll_reverse_c(tmp_path):
    path = tmp_path / "sll_reverse.c"
    path.write_text(_SLL_REVERSE_SRC, encoding="utf-8")
    return str(path)


def _write_sll_multi_merge_c(tmp_path):
    path = tmp_path / "sll_multi_merge.c"
    path.write_text(_SLL_MULTI_MERGE_SRC, encoding="utf-8")
    return str(path)


def _load_example(tmp_path):
    """Build a synthesis-context dict for the ``sll_reverse`` shape from a
    synthetic in-tmp_path C file.  Replaces reading the checked-in
    ``few-shot-examples/absprog/sll_reverse.auto.json``.
    """
    c_file = _write_sll_reverse_c(tmp_path)
    return collect_synthesis_context(c_file)


def _load_example_with_gold(tmp_path):
    example = _load_example(tmp_path)
    example["gold"] = _GOLD_DATA
    return example


def test_render_prompt_uses_actual_context_schema(tmp_path):
    example = _load_example_with_gold(tmp_path)

    prompt = render_prompt(example, [example])

    assert "Function: sll_reverse" in prompt
    assert "Require with safeExec: safeExec(ATrue, sll_reverse_M(l1), X) && sll(head, l1)" in prompt
    assert "M_loop_before: list Z -> MONAD (list Z * list Z)" in prompt
    assert "### Example: sll_reverse" in prompt
    assert "Definition MretTy : Type := list Z." in prompt


def test_render_prompt_mentions_available_callees_when_present(tmp_path):
    """The slim workdir-mode prompt still surfaces the dynamic per-function
    content (Available Callees, Opaque Call Obligations call sites, Required
    Signatures).  Static rule text (monad primitives, "use plain return",
    "do not bind to `_`") was moved to AGENTS.md and must NOT appear here."""
    c_file = _write_sll_multi_merge_c(tmp_path)
    context = collect_synthesis_context(c_file, func_name="sll_multi_merge")

    prompt = render_prompt(context)

    # Dynamic per-function content is present.
    assert "## Available Callees" in prompt
    assert "`sll_merge_M` (same-file): list Z -> list Z -> MONAD (list Z)" in prompt
    assert "Same-file opaque programs you may invoke: sll_merge_M" in prompt
    assert "## Selected Scaffold" in prompt
    assert "Template case: both" in prompt
    assert "early_result" in prompt
    assert "sll_multi_merge_M_after_loop" in prompt
    assert "Already generated by the scaffold — do NOT redefine: sll_multi_merge_M_after_loop" in prompt
    assert "## Opaque Call Obligations" in prompt
    assert "`t = sll_merge(y, z);` must use `sll_merge_M`" in prompt
    assert "M_loop_M1: (list Z * list Z * list Z * list Z * Z) -> MONAD MretTy" in prompt
    assert "M_loop_M2: (list Z * list Z * list Z * list Z * Z) -> MONAD (early_result (list Z * list Z * list Z * list Z * Z) (list Z))" in prompt
    # New: skeleton pointer line replaces the verbose per-call scaffold sketch.
    assert "skeleton/<basename>_rel_lib.v" in prompt
    # Static AGENTS.md content does NOT leak back into stdin.
    assert "You are generating Coq monadic abstract programs" not in prompt
    assert "## QCP Monad Primitives" not in prompt
    assert "Do not replace helper-call results with `any`." not in prompt
    assert "Use plain `return EXPR`" not in prompt
    assert "Use the Selected Scaffold above as the authoritative composition rule" not in prompt
    # Per-call branch / early-return sketches are gone (agent reads the
    # actual skeleton file instead).
    assert "break (Continue r)" not in prompt
    assert "| Continue a'' => continue a''" not in prompt


def test_render_repair_prompt_includes_failure_feedback(tmp_path):
    example = _load_example(tmp_path)

    prompt = render_repair_prompt(
        example,
        previous_response="Definition broken := True.",
        failure_kind="parse",
        failure_message="Could not find Definition 'foo'",
        few_shot_examples=[example],
    )

    assert "## Repair Feedback" in prompt
    assert "Failure kind: parse" in prompt
    assert "Could not find Definition 'foo'" in prompt
    assert "Definition broken := True." in prompt


def test_parse_synthesized_components_extracts_blocks_from_response():
    response = """```coq
Definition MretTy : Type := list Z.
Definition sll_reverse_M_loop_before : list Z -> MONAD (list Z * list Z) :=
  fun l => return (nil, l).
Definition sll_reverse_M_loop_M1 : (list Z * list Z) -> MONAD MretTy:=
  fun '(l1,l2) => return l1.
Definition sll_reverse_M_loop_M2 : (list Z * list Z) -> MONAD (list Z * list Z) :=
  fun '(l1,l2) =>
    match l2 with
    | nil => return (l1,l2)
    | v :: l2' => return (v :: l1, l2')
    end.
Definition sll_reverse_M_loop_end : MretTy -> MONAD (list Z):=
  fun l => return l.
```"""

    blocks = parse_synthesized_components(response, "sll_reverse")

    assert blocks["MretTy"] == "Definition MretTy : Type := list Z."
    assert "Definition sll_reverse_M_loop_before" in blocks["M_loop_before"]
    assert "Definition sll_reverse_M_loop_M1" in blocks["M_1"]
    assert "Definition sll_reverse_M_loop_M2" in blocks["M_2"]
    assert "Definition sll_reverse_M_loop_end" in blocks["M_loop_end"]


def test_parse_synthesized_components_accepts_multiline_definition_headers():
    response = """```coq
Definition MretTy : Type := (list Z * list Z)%type.

Definition sll_copy_double_M_loop_before
  : list Z -> MONAD (list Z * list Z * list Z) :=
  fun l => return (nil, l, nil).

Definition sll_copy_double_M_loop_M1
  : (list Z * list Z * list Z) -> MONAD MretTy :=
  fun '(l1, l2, l3) => return (l3, l1).

Definition sll_copy_double_M_loop_M2
  : (list Z * list Z * list Z) -> MONAD (list Z * list Z * list Z) :=
  fun '(l1, l2, l3) => return (l1, l2, l3).

Definition sll_copy_double_M_loop_end
  : MretTy -> MONAD (list Z * list Z) :=
  fun r => return r.
```"""

    blocks = parse_synthesized_components(response, "sll_copy_double")

    assert "Definition sll_copy_double_M_loop_before" in blocks["M_loop_before"]
    assert "Definition sll_copy_double_M_loop_M1" in blocks["M_1"]
    assert "Definition sll_copy_double_M_loop_M2" in blocks["M_2"]
    assert "Definition sll_copy_double_M_loop_end" in blocks["M_loop_end"]


def test_parse_synthesized_components_stops_at_depth_zero_dot_not_inside_match():
    # A '.' inside a match/end block must not terminate early
    response = """```coq
Definition MretTy : Type := list Z.
Definition foo_M_loop_before (l : list Z) : MONAD (list Z * list Z) :=
  fun sigma => ret (nil, l).
Definition foo_M_loop_M1 (s : list Z * list Z) : MONAD MretTy :=
  fun sigma =>
    match s with
    | (l1, nil) => ret l1
    | (l1, v :: l2) => ret l1
    end.
Definition foo_M_loop_M2 (s : list Z * list Z) : MONAD (list Z * list Z) :=
  fun sigma => ret s.
Definition foo_M_loop_end (r : MretTy) : MONAD (list Z) :=
  fun sigma => ret r.
```"""

    blocks = parse_synthesized_components(response, "foo")

    assert blocks["M_1"].startswith("Definition foo_M_loop_M1")
    assert blocks["M_1"].endswith("end.")
    assert "| (l1, nil) => ret l1" in blocks["M_1"]
    assert "| (l1, v :: l2) => ret l1" in blocks["M_1"]


def test_parse_synthesized_components_stops_at_depth_zero_dot_not_inside_comment():
    # A '.' inside a comment must not terminate early
    response = """```coq
Definition MretTy : Type := list Z.
Definition foo_M_loop_before (l : list Z) : MONAD (list Z * list Z) :=
  (* initialise with empty acc. *)
  fun sigma => ret (nil, l).
Definition foo_M_loop_M1 (s : list Z * list Z) : MONAD MretTy :=
  fun '(l1, _) => ret l1.
Definition foo_M_loop_M2 (s : list Z * list Z) : MONAD (list Z * list Z) :=
  fun s => ret s.
Definition foo_M_loop_end (r : MretTy) : MONAD (list Z) :=
  fun sigma => ret r.
```"""

    blocks = parse_synthesized_components(response, "foo")

    assert blocks["M_loop_before"].startswith("Definition foo_M_loop_before")
    assert blocks["M_loop_before"].endswith("ret (nil, l).")
    assert "(* initialise with empty acc. *)" in blocks["M_loop_before"]


def test_parse_synthesized_components_stops_at_depth_zero_dot_not_inside_parens():
    # A '.' inside parentheses must not terminate early
    response = """```coq
Definition MretTy : Type := list Z.
Definition foo_M_loop_before (l : list Z) : MONAD (list Z * list Z) :=
  fun sigma => ret (SomeModule.helper l, l).
Definition foo_M_loop_M1 (s : list Z * list Z) : MONAD MretTy :=
  fun '(l1, _) => ret l1.
Definition foo_M_loop_M2 (s : list Z * list Z) : MONAD (list Z * list Z) :=
  fun s => ret s.
Definition foo_M_loop_end (r : MretTy) : MONAD (list Z) :=
  fun sigma => ret r.
```"""

    blocks = parse_synthesized_components(response, "foo")

    assert blocks["M_loop_before"].startswith("Definition foo_M_loop_before")
    assert blocks["M_loop_before"].endswith("ret (SomeModule.helper l, l).")
    assert "SomeModule.helper" in blocks["M_loop_before"]


def test_assemble_rel_lib_from_blocks_replaces_parameters(tmp_path):
    example = _load_example_with_gold(tmp_path)
    blocks = {"MretTy": f"Definition MretTy : Type := {example['gold']['MretTy']}."}
    blocks.update(example["gold"]["components"])

    c_file = _write_sll_reverse_c(tmp_path)
    content = assemble_rel_lib_from_blocks(c_file, "sll_reverse", blocks)

    assert "Parameter MretTy : Type." not in content
    assert "Parameter sll_reverse_M_loop_before" not in content
    assert "Definition MretTy : Type := list Z." in content
    assert "Definition sll_reverse_M_loop_before : list Z -> MONAD (list Z * list Z) :=" in content
    assert "Definition sll_reverse_M_loop_M1 : (list Z * list Z) -> MONAD MretTy:=" in content


def test_assemble_rel_lib_from_blocks_preserves_callee_declarations(tmp_path):
    blocks = {
        "MretTy": "Definition MretTy : Type := list Z.",
        "M_loop_before": """Definition sll_multi_merge_M_loop_before
  : list Z -> list Z -> list Z -> MONAD (list Z * list Z * list Z * list Z) :=
  fun l1 l2 l3 => return (l1, l2, l3, nil).""",
        "M_1": """Definition sll_multi_merge_M_loop_M1
  : (list Z * list Z * list Z * list Z) -> MONAD MretTy :=
  fun '(_, _, _, l4) => return l4.""",
        "M_2": """Definition sll_multi_merge_M_loop_M2
  : (list Z * list Z * list Z * list Z) -> MONAD (list Z * list Z * list Z * list Z) :=
  fun s => return s.""",
        "M_loop_end": """Definition sll_multi_merge_M_loop_end
  : MretTy -> MONAD (list Z) :=
  fun l => return l.""",
    }

    c_file = _write_sll_multi_merge_c(tmp_path)
    content = assemble_rel_lib_from_blocks(c_file, "sll_multi_merge", blocks)

    assert "Parameter sll_merge_M : list Z -> list Z -> MONAD (list Z)." in content
    assert "Definition sll_multi_merge_M_loop_before" in content


def test_append_missing_residual_decls_to_rel_c_is_idempotent(tmp_path):
    rel_c = tmp_path / "demo_rel.c"
    rel_c.write_text(
        """#include "safeexec_def.h"

/*@ Import Coq Require Import demo_rel_lib */
/*@ Extern Coq (MretTy :: *) */
/*@ Extern Coq 
               (demo_M: list Z -> program unit (list Z))
               */
""",
        encoding="utf-8",
    )

    decl = "(residual_prog_in_demo_M_call_1: list Z -> list Z -> program unit (list Z))"
    patched = _append_missing_residual_decls_to_rel_c(str(rel_c), [decl])
    assert patched == str(rel_c)
    content = rel_c.read_text(encoding="utf-8")
    assert decl in content

    _append_missing_residual_decls_to_rel_c(str(rel_c), [decl])
    content = rel_c.read_text(encoding="utf-8")
    assert content.count("residual_prog_in_demo_M_call_1") == 1


def test_sync_residual_artifacts_appends_rel_lib_and_patches_rel_c(monkeypatch, tmp_path):
    monkeypatch.setenv("REL_DIR", str(tmp_path / "rel"))
    rel_c_dir = tmp_path / "rel" / "sll"
    rel_c_dir.mkdir(parents=True)
    rel_c = rel_c_dir / "sll_multi_merge_rel.c"
    rel_c.write_text(
        """#include "safeexec_def.h"

/*@ Import Coq Require Import sll_multi_merge_rel_lib */
/*@ Extern Coq (MretTy :: *) */
/*@ Extern Coq (early_result :: * => * => *) */
/*@ Extern Coq 
               (sll_multi_merge_M: list Z -> list Z -> list Z -> program unit (list Z))
               (sll_multi_merge_M_loop: list Z -> list Z -> list Z -> list Z -> program unit (early_result MretTy (list Z)))
               (sll_multi_merge_M_loop_end: MretTy -> program unit (list Z))
               (sll_multi_merge_M_after_loop: early_result MretTy (list Z) -> program unit (list Z))
               */
""",
        encoding="utf-8",
    )

    rel_lib = tmp_path / "sll_multi_merge_rel_lib.v"
    rel_lib.write_text(
        """Definition MretTy : Type := list Z.

Inductive early_result (S Ret : Type) :=
| Continue : S -> early_result S Ret
| ReturnNow : Ret -> early_result S Ret.
Arguments Continue {S Ret} _.
Arguments ReturnNow {S Ret} _.

Parameter sll_merge_M : list Z -> list Z -> MONAD (list Z).

Definition sll_multi_merge_M_loop_M1
  : (list Z * list Z * list Z * list Z) -> MONAD MretTy :=
  fun '(l1, l2, l3, l4) =>
    r <- sll_merge_M l1 l2;;
    return (l4 ++ r).

Definition sll_multi_merge_M_loop_M2
  : (list Z * list Z * list Z * list Z)
    -> MONAD (early_result (list Z * list Z * list Z * list Z) (list Z)) :=
  fun '(l1, l2, l3, l4) =>
    match l3 with
    | nil =>
        return (Continue (l1, l2, l3, l4))
    | u0 :: u' =>
        match l1 with
        | nil =>
            r <- sll_merge_M l3 l2;;
            return (ReturnNow (l4 ++ r))
        | y0 :: y' =>
            match l2 with
            | nil =>
                r <- sll_merge_M l3 y';;
                return (ReturnNow (l4 ++ (y0 :: r)))
            | z0 :: z' =>
                return (Continue (y', z', u', l4 ++ (y0 :: z0 :: u0 :: nil)))
            end
        end
    end.

Definition sll_multi_merge_M_loop_body : (list Z * list Z * list Z * list Z) -> MONAD (CntOrBrk (list Z * list Z * list Z * list Z) (early_result MretTy (list Z))) :=
  fun a =>
    choice (assume!! (~ guard);; r <- sll_multi_merge_M_loop_M1 a ;; break (Continue r))
           (assume!! guard;;
            a' <- sll_multi_merge_M_loop_M2 a ;;
            match a' with
            | Continue a'' => continue a''
            | ReturnNow r' => break (ReturnNow r')
            end).

Definition sll_multi_merge_M_loop_aux :=
  repeat_break sll_multi_merge_M_loop_body.

Definition sll_multi_merge_M_loop_before
  : list Z -> list Z -> list Z -> MONAD (early_result (list Z * list Z * list Z * list Z) (list Z)) :=
  fun l1 l2 l3 =>
    match l1 with
    | nil =>
        r <- sll_merge_M l2 l3;;
        return (ReturnNow r)
    | xh :: xt =>
        return (Continue (l2, l3, xt, xh :: nil))
    end.

Definition sll_multi_merge_M_after_loop : early_result MretTy (list Z) -> MONAD (list Z) :=
  fun re =>
    match re with
    | Continue r => sll_multi_merge_M_loop_end r
    | ReturnNow r => return r
    end.

Definition sll_multi_merge_M : list Z -> list Z -> list Z -> MONAD (list Z) :=
  fun l1 l2 l3 =>
    e <- sll_multi_merge_M_loop_before l1 l2 l3;;
    match e with
    | Continue s =>
        re <- sll_multi_merge_M_loop_aux s;;
        sll_multi_merge_M_after_loop re
    | ReturnNow r =>
        return r
    end.
""",
        encoding="utf-8",
    )

    c_file = _write_sll_multi_merge_c(tmp_path)
    context = collect_synthesis_context(c_file, func_name="sll_multi_merge")

    files = _sync_residual_artifacts(context, str(rel_lib), rel_c_path=str(rel_c))

    assert files["rel_lib"] == str(rel_lib)
    assert files["rel_c"] == str(rel_c)
    rel_lib_content = rel_lib.read_text(encoding="utf-8")
    assert "Definition residual_prog_in_sll_multi_merge_M_call_2 (l4 : list Z) : list Z -> MONAD (list Z) :=" in rel_lib_content
    rel_c_content = rel_c.read_text(encoding="utf-8")
    assert "(residual_prog_in_sll_multi_merge_M_call_2: list Z -> list Z -> program unit (list Z))" in rel_c_content
    assert "MretTy" not in rel_c_content
    assert "program unit (early_result (list Z) (list Z))" in rel_c_content
    assert "(sll_multi_merge_M_loop_end: (list Z) -> program unit (list Z))" in rel_c_content


def test_eliminate_mretty_in_rel_c_replaces_and_removes_declaration(tmp_path):
    rel_c = tmp_path / "demo_rel.c"
    rel_c.write_text(
        """#include "safeexec_def.h"

/*@ Import Coq Require Import demo_rel_lib */
/*@ Extern Coq (MretTy :: *) */
/*@ Extern Coq
               (demo_M_loop: list Z -> program unit MretTy)
               (demo_M_loop_end: MretTy -> program unit (list Z))
               */
""",
        encoding="utf-8",
    )

    result = _eliminate_mretty_in_rel_c(str(rel_c), "list Z")
    assert result == str(rel_c)
    content = rel_c.read_text(encoding="utf-8")
    assert "MretTy" not in content
    assert "/*@ Extern Coq (MretTy :: *) */" not in content
    assert "(demo_M_loop: list Z -> program unit (list Z))" in content
    assert "(demo_M_loop_end: (list Z) -> program unit (list Z))" in content


def test_extract_mretty_type_reads_definition(tmp_path):
    rel_lib = tmp_path / "x_rel_lib.v"
    rel_lib.write_text(
        "Parameter foo : nat.\nDefinition MretTy : Type := list Z.\n",
        encoding="utf-8",
    )
    assert _extract_mretty_type(str(rel_lib)) == "list Z"


def test_extract_mretty_type_strips_percent_type_notation(tmp_path):
    rel_lib = tmp_path / "x_rel_lib.v"
    rel_lib.write_text(
        "Definition MretTy : Type := (list Z * list Z * Z)%type.\n",
        encoding="utf-8",
    )
    assert _extract_mretty_type(str(rel_lib)) == "(list Z * list Z * Z)"


def test_eliminate_mretty_in_rel_c_handles_tuple_concrete_type(tmp_path):
    rel_c = tmp_path / "demo_rel.c"
    rel_c.write_text(
        """/*@ Extern Coq (MretTy :: *) */
/*@ Extern Coq
               (demo_M_loop: list Z -> program unit MretTy)
               (demo_M_loop_end: MretTy -> program unit (list Z))
               */
""",
        encoding="utf-8",
    )

    _eliminate_mretty_in_rel_c(str(rel_c), "(list Z * list Z * Z)")
    content = rel_c.read_text(encoding="utf-8")
    assert "MretTy" not in content
    assert "%type" not in content
    assert "(demo_M_loop: list Z -> program unit (list Z * list Z * Z))" in content
    assert "(demo_M_loop_end: (list Z * list Z * Z) -> program unit (list Z))" in content


def test_eliminate_mretty_in_rel_c_handles_per_function_mapping(tmp_path):
    """Multi-function ``_rel.c`` files emit ``{func}_MretTy`` per function;
    the patcher accepts a mapping and substitutes each independently."""
    rel_c = tmp_path / "two_funcs_rel.c"
    rel_c.write_text(
        """/*@ Extern Coq (f1_MretTy :: *) */
/*@ Extern Coq (f2_MretTy :: *) */
/*@ Extern Coq
               (f1_M_loop: list Z -> program unit f1_MretTy)
               (f1_M_loop_end: f1_MretTy -> program unit (list Z))
               (f2_M_loop: list Z -> program unit f2_MretTy)
               (f2_M_loop_end: f2_MretTy -> program unit (list Z))
               */
""",
        encoding="utf-8",
    )

    _eliminate_mretty_in_rel_c(str(rel_c), {"f1": "list Z", "f2": "(list Z * Z)"})
    content = rel_c.read_text(encoding="utf-8")

    # All MretTy tokens are gone, both per-function extern decls stripped.
    assert "MretTy" not in content
    assert "(f1_M_loop: list Z -> program unit (list Z))" in content
    assert "(f1_M_loop_end: (list Z) -> program unit (list Z))" in content
    assert "(f2_M_loop: list Z -> program unit (list Z * Z))" in content
    assert "(f2_M_loop_end: (list Z * Z) -> program unit (list Z))" in content


def _write_example_with_gold(tmp_path):
    """Write a temporary example JSON that includes inline gold data."""
    example = _load_example_with_gold(tmp_path)
    path = tmp_path / "sll_reverse_with_gold.json"
    path.write_text(json.dumps(example), encoding="utf-8")
    return str(path)


def test_run_synthesis_pipeline_replay_backend_writes_artifacts(tmp_path):
    output_dir = tmp_path / "synth"
    example_path = _write_example_with_gold(tmp_path)

    summary = run_synthesis_pipeline(
        input_path=example_path,
        output_dir=str(output_dir),
        backend="gold-example",
        few_shot_paths=[example_path],
        run_check=False,
    )

    assert summary["status"] == "assembled"
    files = summary["files"]
    assert (output_dir / "sll_reverse.prompt.txt").exists()
    assert (output_dir / "sll_reverse.response.txt").exists()
    assert (output_dir / "sll_reverse.parsed.json").exists()
    assert (output_dir / "sll_reverse_rel_lib.v").exists()
    assert files["context"] == example_path

    assembled = (output_dir / "sll_reverse_rel_lib.v").read_text(encoding="utf-8")
    assert "Definition MretTy : Type := list Z." in assembled
    assert "Definition sll_reverse_M_loop_M2 : (list Z * list Z) -> MONAD (list Z * list Z) :=" in assembled

    summary_json = json.loads((output_dir / "sll_reverse.summary.json").read_text(encoding="utf-8"))
    assert summary_json["check"]["status"] == "skipped"


def _fake_codex_writes_filled_skeleton(filled_text: str):
    """Build a monkeypatch ``subprocess.run`` that emulates codex completing
    successfully, having written *filled_text* to the workdir's
    ``skeleton/{basename}_rel_lib.v`` (the path is recovered from the codex
    command's ``-C <workdir>`` arg)."""
    import subprocess as _subprocess

    def _fake(cmd, **kwargs):
        # Extract the workdir from ``-C <workdir>`` to locate the skeleton.
        try:
            cd_idx = cmd.index("-C")
            workdir = cmd[cd_idx + 1]
        except (ValueError, IndexError):  # pragma: no cover — sanity guard
            return _subprocess.CompletedProcess(args=cmd, returncode=1, stdout="", stderr="bad cmd")
        skeleton_dir = os.path.join(workdir, "skeleton")
        # There's exactly one *.v file in skeleton/ per design.
        entries = [n for n in os.listdir(skeleton_dir) if n.endswith(".v")]
        assert entries, f"prepare_workdir didn't create a skeleton: {skeleton_dir}"
        with open(os.path.join(skeleton_dir, entries[0]), "w", encoding="utf-8") as f:
            f.write(filled_text)
        # The agent's transcript also gets written by codex's
        # --output-last-message — emulate that.
        try:
            t_idx = cmd.index("--output-last-message")
            with open(cmd[t_idx + 1], "w", encoding="utf-8") as f:
                f.write("done")
        except (ValueError, IndexError):
            pass
        return _subprocess.CompletedProcess(args=cmd, returncode=0, stdout="", stderr="")

    return _fake


def _ensure_coq_project(tmp_path) -> None:
    """Drop a minimal ``_CoqProject`` so workdir prep finds one."""
    (tmp_path / "_CoqProject").write_text("-Q . X\n", encoding="utf-8")


def test_generate_candidate_response_invokes_codex_in_workdir(monkeypatch, tmp_path):
    """Workdir-mode rewire — verify the codex command carries the right
    sandbox / workdir flags and that the filled-skeleton text is returned
    as the response."""
    _ensure_coq_project(tmp_path)
    example = _load_example(tmp_path)

    seen = {}
    monkeypatch.setattr("GenMonads.absprog.synthesize.shutil.which",
                        lambda name: "/usr/local/bin/codex" if name == "codex" else None)
    # Pre-compute the filled skeleton from the gold example so validate_attempt
    # accepts it.  The skeleton is generated inside _run_command_backend; we
    # can replay it deterministically because generate_rel_lib_skeleton_for_file
    # is deterministic given the same C source.
    from GenMonads.absprog.assemble import (
        assemble_rel_lib_from_blocks, generate_rel_lib_skeleton_for_file,
    )
    skeleton_text = generate_rel_lib_skeleton_for_file(example["source"]["c_file"])
    filled_text = assemble_rel_lib_from_blocks(
        example["source"]["c_file"], example["summary"]["func_name"],
        blocks={
            "MretTy": f"Definition MretTy : Type := {_GOLD_DATA['MretTy']}.",
            "M_loop_before": _GOLD_DATA["components"]["M_loop_before"],
            "M_1": _GOLD_DATA["components"]["M_1"],
            "M_2": _GOLD_DATA["components"]["M_2"],
            "M_loop_end": _GOLD_DATA["components"]["M_loop_end"],
        },
    )

    def fake_run(cmd, **kwargs):
        seen["cmd"] = cmd
        seen["input"] = kwargs.get("input")
        return _fake_codex_writes_filled_skeleton(filled_text)(cmd, **kwargs)

    monkeypatch.setattr("GenMonads.absprog.synthesize.subprocess.run", fake_run)
    # Workdir prep needs a _CoqProject SOMEWHERE upward — point its locator
    # at our test tmp_path.
    monkeypatch.setattr(
        "GenMonads.absprog.workdir.locate_coq_project",
        lambda start_dir: str(tmp_path / "_CoqProject"),
    )

    response = generate_candidate_response(
        example,
        backend="command",
        prompt_text="PROMPT CONTENT",
        prompt_file=str(tmp_path / "prompt.txt"),
        context_file=str(tmp_path / "context.json"),
        output_dir=str(tmp_path / "synth_out"),
        backend_response_file=str(tmp_path / "backend.txt"),
        command=None,  # ignored under workdir mode
    )

    assert seen["input"] == "PROMPT CONTENT"
    assert "-s" in seen["cmd"] and "workspace-write" in seen["cmd"]
    assert "-C" in seen["cmd"]
    assert "--skip-git-repo-check" in seen["cmd"]
    # Returned response is the filled skeleton text.
    assert "Definition sll_reverse_M_loop_before" in response


def test_command_backend_timeout_surfaces_as_value_error(monkeypatch, tmp_path):
    """A stuck codex must be killed at the ``command_timeout`` and surface
    as ``ValueError`` so the synthesis loop treats the attempt as a failure."""
    import subprocess as _subprocess
    _ensure_coq_project(tmp_path)

    monkeypatch.setattr("GenMonads.absprog.synthesize.shutil.which",
                        lambda name: "/usr/local/bin/codex" if name == "codex" else None)
    monkeypatch.setattr(
        "GenMonads.absprog.workdir.locate_coq_project",
        lambda start_dir: str(tmp_path / "_CoqProject"),
    )

    def fake_run(cmd, **kwargs):
        raise _subprocess.TimeoutExpired(cmd=cmd, timeout=kwargs.get("timeout"))

    monkeypatch.setattr("GenMonads.absprog.synthesize.subprocess.run", fake_run)

    example = _load_example(tmp_path)
    with pytest.raises(ValueError, match="timed out"):
        generate_candidate_response(
            example,
            backend="command",
            prompt_text="anything",
            prompt_file=str(tmp_path / "p.txt"),
            context_file=str(tmp_path / "c.json"),
            output_dir=str(tmp_path / "synth_out"),
            backend_response_file=str(tmp_path / "r.txt"),
            command=None,
            command_timeout=1,
        )


def test_run_synthesis_pipeline_writes_artifacts_under_workdir_backend(monkeypatch, tmp_path):
    """End-to-end: codex is mocked to write a complete filled skeleton; the
    pipeline assembles, validates, and persists artifacts."""
    _ensure_coq_project(tmp_path)
    output_dir = tmp_path / "synth"

    monkeypatch.setattr("GenMonads.absprog.synthesize.shutil.which",
                        lambda name: "/usr/local/bin/codex" if name == "codex" else None)
    monkeypatch.setattr(
        "GenMonads.absprog.workdir.locate_coq_project",
        lambda start_dir: str(tmp_path / "_CoqProject"),
    )

    example_path = _write_example_with_gold(tmp_path)
    # The mock writes the gold-derived filled skeleton; recover it the same
    # way the assembler would, so the strict skeleton-diff validator accepts it.
    from GenMonads.absprog.assemble import (
        assemble_rel_lib_from_blocks,
    )
    gold = _GOLD_DATA
    c_file = str(tmp_path / "sll_reverse.c")  # _write_example_with_gold drops the C file here
    func_name = "sll_reverse"
    filled_text = assemble_rel_lib_from_blocks(
        c_file, func_name,
        blocks={
            "MretTy": f"Definition MretTy : Type := {gold['MretTy']}.",
            "M_loop_before": gold["components"]["M_loop_before"],
            "M_1": gold["components"]["M_1"],
            "M_2": gold["components"]["M_2"],
            "M_loop_end": gold["components"]["M_loop_end"],
        },
    )
    monkeypatch.setattr(
        "GenMonads.absprog.synthesize.subprocess.run",
        _fake_codex_writes_filled_skeleton(filled_text),
    )

    summary = run_synthesis_pipeline(
        input_path=example_path,
        output_dir=str(output_dir),
        backend="command",
        command=None,
        run_check=False,
    )

    assert summary["status"] == "assembled"
    assembled = (output_dir / "sll_reverse_rel_lib.v").read_text(encoding="utf-8")
    assert "Definition sll_reverse_M_loop_before" in assembled


def test_run_synthesis_pipeline_rejects_missing_opaque_callee_usage(tmp_path):
    output_dir = tmp_path / "synth"
    response_path = tmp_path / "response.txt"
    response_path.write_text(
        "\n".join(
            [
                "```coq",
                "Definition MretTy : Type := list Z.",
                "Definition sll_multi_merge_M_loop_before : list Z -> list Z -> list Z -> MONAD (list Z * list Z * list Z * list Z) :=",
                "  fun l1 l2 l3 => return (l1, l2, l3, nil).",
                "Definition sll_multi_merge_M_loop_M1 : (list Z * list Z * list Z * list Z) -> MONAD MretTy :=",
                "  fun '(_, _, _, l4) => return l4.",
                "Definition sll_multi_merge_M_loop_M2 : (list Z * list Z * list Z * list Z) -> MONAD (list Z * list Z * list Z * list Z) :=",
                "  fun s => any (list Z * list Z * list Z * list Z).",
                "Definition sll_multi_merge_M_loop_end : MretTy -> MONAD (list Z) :=",
                "  fun l => return l.",
                "```",
                "",
            ]
        ),
        encoding="utf-8",
    )

    c_file = _write_sll_multi_merge_c(tmp_path)
    summary = run_synthesis_pipeline(
        input_path=c_file,
        output_dir=str(output_dir),
        func_name="sll_multi_merge",
        backend="response-file",
        response_file=str(response_path),
        run_check=False,
    )

    assert summary["status"] == "failed"
    assert summary["attempts"][0]["failure_kind"] == "validation"
    assert "sll_merge_M" in summary["attempts"][0]["failure_message"]


def test_run_synthesis_pipeline_rejects_missing_early_return_scaffold(tmp_path):
    output_dir = tmp_path / "synth"
    response_path = tmp_path / "response.txt"
    response_path.write_text(
        "\n".join(
            [
                "```coq",
                "(* sll_merge_M *)",
                "Definition MretTy : Type := list Z.",
                "Definition sll_multi_merge_M_loop_before : list Z -> list Z -> list Z -> MONAD (list Z * list Z * list Z * list Z) :=",
                "  fun l1 l2 l3 => return (l1, l2, l3, nil).",
                "Definition sll_multi_merge_M_loop_M1 : (list Z * list Z * list Z * list Z) -> MONAD MretTy :=",
                "  fun '(_, _, _, l4) => return l4.",
                "Definition sll_multi_merge_M_loop_M2 : (list Z * list Z * list Z * list Z) -> MONAD (list Z * list Z * list Z * list Z) :=",
                "  fun s => any (list Z * list Z * list Z * list Z).",
                "Definition sll_multi_merge_M_loop_end : MretTy -> MONAD (list Z) :=",
                "  fun l => return l.",
                "```",
                "",
            ]
        ),
        encoding="utf-8",
    )

    c_file = _write_sll_multi_merge_c(tmp_path)
    summary = run_synthesis_pipeline(
        input_path=c_file,
        output_dir=str(output_dir),
        func_name="sll_multi_merge",
        backend="response-file",
        response_file=str(response_path),
        run_check=False,
    )

    assert summary["status"] == "failed"
    assert summary["attempts"][0]["failure_kind"] == "validation"
    assert "early_result" in summary["attempts"][0]["failure_message"]


def test_run_synthesis_pipeline_retries_after_parse_failure(monkeypatch, tmp_path):
    gold = _GOLD_DATA
    output_dir = tmp_path / "repair-parse"
    responses = iter(
        [
            "```coq\nDefinition MretTy : Type := list Z.\n```",
            "\n".join(
                [
                    "```coq",
                    f"Definition MretTy : Type := {gold['MretTy']}.",
                    gold["components"]["M_loop_before"],
                    gold["components"]["M_1"],
                    gold["components"]["M_2"],
                    gold["components"]["M_loop_end"],
                    "```",
                    "",
                ]
            ),
        ]
    )

    def fake_generate(*_args, **_kwargs):
        return next(responses)

    monkeypatch.setattr("GenMonads.absprog.synthesize.generate_candidate_response", fake_generate)

    example_path = _write_example_with_gold(tmp_path)
    summary = run_synthesis_pipeline(
        input_path=example_path,
        output_dir=str(output_dir),
        backend="command",
        command="codex exec",
        run_check=False,
        max_retries=1,
    )

    assert summary["status"] == "assembled"
    assert summary["attempt_count"] == 2
    assert summary["attempts"][0]["failure_kind"] == "parse"
    assert summary["attempts"][1]["status"] == "assembled"

    repair_prompt = (output_dir / "attempt-1" / "sll_reverse.prompt.txt").read_text(encoding="utf-8")
    assert "## Repair Feedback" in repair_prompt
    assert "Failure kind: parse" in repair_prompt


def test_run_synthesis_pipeline_retries_after_rocq_failure(monkeypatch, tmp_path):
    gold = _GOLD_DATA
    output_dir = tmp_path / "repair-rocq"
    response_text = "\n".join(
        [
            "```coq",
            f"Definition MretTy : Type := {gold['MretTy']}.",
            gold["components"]["M_loop_before"],
            gold["components"]["M_1"],
            gold["components"]["M_2"],
            gold["components"]["M_loop_end"],
            "```",
            "",
        ]
    )
    # Two attempt-dir checks (fail then pass) followed by an unbounded stream
    # of "passed" results so the promotion-time recompile in
    # `_promote_rel_lib_if_accepted` also succeeds.
    primary_checks = iter(
        [
            {
                "status": "failed",
                "passed": False,
                "reason": "",
                "stdout": "",
                "stderr": "Syntax error on line 12",
                "returncode": 1,
            },
            {
                "status": "passed",
                "passed": True,
                "reason": "",
                "stdout": "",
                "stderr": "",
                "returncode": 0,
            },
        ]
    )

    def fake_check(_path):
        return next(primary_checks, {"status": "passed", "passed": True, "reason": "",
                                     "stdout": "", "stderr": "", "returncode": 0})

    monkeypatch.setattr(
        "GenMonads.absprog.synthesize.generate_candidate_response",
        lambda *_args, **_kwargs: response_text,
    )
    monkeypatch.setattr(
        "GenMonads.absprog.synthesize.check_rocq_file",
        fake_check,
    )

    example_path = _write_example_with_gold(tmp_path)
    summary = run_synthesis_pipeline(
        input_path=example_path,
        output_dir=str(output_dir),
        backend="command",
        command="codex exec",
        run_check=True,
        max_retries=1,
    )

    assert summary["status"] == "passed"
    assert summary["attempt_count"] == 2
    assert summary["attempts"][0]["failure_kind"] == "rocq"
    assert summary["attempts"][1]["status"] == "passed"

    repair_prompt = (output_dir / "attempt-1" / "sll_reverse.prompt.txt").read_text(encoding="utf-8")
    assert "Failure kind: rocq" in repair_prompt
    assert "Syntax error on line 12" in repair_prompt


def test_run_synthesis_pipeline_promotes_passed_lib_to_coq_lib_dir(monkeypatch, tmp_path):
    gold = _GOLD_DATA
    output_dir = tmp_path / "promote"
    coq_lib_dir = tmp_path / "libs"
    response_text = "\n".join(
        [
            "```coq",
            f"Definition MretTy : Type := {gold['MretTy']}.",
            gold["components"]["M_loop_before"],
            gold["components"]["M_1"],
            gold["components"]["M_2"],
            gold["components"]["M_loop_end"],
            "```",
            "",
        ]
    )

    monkeypatch.setenv("COQ_LIB_DIR", str(coq_lib_dir))
    monkeypatch.setattr(
        "GenMonads.absprog.synthesize.generate_candidate_response",
        lambda *_args, **_kwargs: response_text,
    )
    monkeypatch.setattr(
        "GenMonads.absprog.synthesize.check_rocq_file",
        lambda _path: {
            "status": "passed",
            "passed": True,
            "reason": "",
            "stdout": "",
            "stderr": "",
            "returncode": 0,
        },
    )

    example_path = _write_example_with_gold(tmp_path)
    summary = run_synthesis_pipeline(
        input_path=example_path,
        output_dir=str(output_dir),
        backend="command",
        command="codex exec",
        run_check=True,
    )

    promoted = coq_lib_dir / "sll_reverse_rel_lib.v"
    assert summary["status"] == "passed"
    assert summary["files"]["promoted_rel_lib"] == str(promoted)
    assert promoted.exists()
    assert promoted.read_text(encoding="utf-8") == (
        output_dir / "sll_reverse_rel_lib.v"
    ).read_text(encoding="utf-8")


def test_run_synthesis_pipeline_parse_failure_does_not_require_assembled_file(monkeypatch, tmp_path):
    output_dir = tmp_path / "parse-fail"
    monkeypatch.setattr(
        "GenMonads.absprog.synthesize.generate_candidate_response",
        lambda *_args, **_kwargs: "```coq\nDefinition MretTy : Type := list Z.\n```",
    )

    example_path = _write_example_with_gold(tmp_path)
    summary = run_synthesis_pipeline(
        input_path=example_path,
        output_dir=str(output_dir),
        backend="command",
        command="codex exec",
        run_check=False,
        max_retries=0,
    )

    assert summary["status"] == "failed"
    assert summary["attempt_count"] == 1
    assert summary["attempts"][0]["failure_kind"] == "parse"
    assert "promoted_rel_lib" not in summary["files"]


def test_promote_rel_lib_if_accepted_copies_only_v_and_recompiles(monkeypatch, tmp_path):
    """Promotion must copy only ``.v`` (the attempt's ``.vo`` was compiled
    outside the lib dir's ``-R`` prefix, so its embedded library name is
    wrong) and then recompile in the lib dir so the project's
    ``_CoqProject`` ``-R`` mapping applies."""
    assembled = tmp_path / "attempt-0" / "demo_rel_lib.v"
    assembled.parent.mkdir(parents=True)
    assembled.write_text("Definition x := 0.\n", encoding="utf-8")
    # Stale sidecars in the attempt dir — must NOT be propagated.
    for ext in [".vo", ".vok", ".vos", ".glob"]:
        assembled.with_suffix(ext).write_text(ext, encoding="utf-8")
    # Stale sidecars in the target dir from a previous run — must be cleared.
    target_dir = tmp_path / "libs"
    target_dir.mkdir()
    for ext in [".vo", ".vok", ".vos", ".glob"]:
        (target_dir / f"demo_rel_lib{ext}").write_text("stale", encoding="utf-8")
    monkeypatch.setenv("COQ_LIB_DIR", str(target_dir))

    recompile_calls = []
    import GenMonads.absprog.synthesize as synth_mod
    monkeypatch.setattr(
        synth_mod,
        "check_rocq_file",
        lambda path: (recompile_calls.append(path), {"status": "passed"})[1],
    )

    promoted = _promote_rel_lib_if_accepted(str(assembled), "demo", "passed")

    assert promoted == str(target_dir / "demo_rel_lib.v")
    assert (target_dir / "demo_rel_lib.v").exists()
    # The attempt's .vo/.vok/.vos/.glob must NOT be copied; stale ones removed.
    for ext in [".vo", ".vok", ".vos", ".glob"]:
        assert not (target_dir / f"demo_rel_lib{ext}").exists(), \
            f"stale {ext} should have been removed"
    # And the recompile must have been triggered at the target path.
    assert recompile_calls == [str(target_dir / "demo_rel_lib.v")]


def test_validate_opaque_callee_usage_rejects_discarded_result():
    context = {
        "generation_policy": {"opaque_external_programs": ["list_tail_M"]},
    }
    response = (
        "Definition list_append_raw_M_normal : MretTy -> MONAD (list Z) :=\n"
        "  fun s => let '(l1, l2) := s in _ <- list_tail_M(l1);; return (l1 ++ l2).\n"
    )
    try:
        _validate_opaque_callee_usage(context, response)
    except ValueError as exc:
        assert "must be bound to a named variable" in str(exc)
        assert "list_tail_M" in str(exc)
    else:
        raise AssertionError("expected ValueError for discarded opaque callee result")


def test_validate_opaque_callee_usage_accepts_named_binding():
    context = {
        "generation_policy": {"opaque_external_programs": ["list_tail_M"]},
    }
    response = (
        "Definition list_append_raw_M_normal : MretTy -> MONAD (list Z) :=\n"
        "  fun s => let '(l1, l2) := s in r <- list_tail_M(l1);; return r.\n"
    )
    # Should not raise.
    _validate_opaque_callee_usage(context, response)


_SLL_LEN_CALLER_SRC = (
    '#include "verification_list.h"\n'
    '#include "sll_shape_def.h"\n'
    '\n'
    'int sll_len(struct list * x)\n'
    '/*@ Require listrep(x)\n'
    '    Ensure  listrep(x)\n'
    ' */\n'
    '{\n'
    '    int n = 0;\n'
    '    struct list * p = x;\n'
    '    /*@ Inv listrep(p) */\n'
    '    while (p) {\n'
    '        n = n + 1;\n'
    '        p = p->next;\n'
    '    }\n'
    '    return n;\n'
    '}\n'
    '\n'
    'int sll_len_caller(struct list * x)\n'
    '/*@ Require listrep(x)\n'
    '    Ensure  listrep(x)\n'
    ' */\n'
    '{\n'
    '    int r = sll_len(x);\n'
    '    return r;\n'
    '}\n'
)


def test_render_prompt_includes_callee_c_body_when_available(tmp_path):
    c_file = tmp_path / "sll_len_caller.c"
    c_file.write_text(_SLL_LEN_CALLER_SRC, encoding="utf-8")
    context = collect_synthesis_context(str(c_file), func_name="sll_len_caller")

    callees = context.get("available_callees", [])
    assert any(c.get("func_name") == "sll_len" and c.get("c_source") for c in callees), \
        "expected sll_len callee with c_source populated"

    prompt = render_prompt(context)

    assert "C body:" in prompt
    assert "```c" in prompt
    assert "int sll_len(struct list * x)" in prompt


# ---------------------------------------------------------------------------
# --coq-lib-dir threading (CLI override flows into the synthesis pipeline) +
# PrerequisiteError aborts retries on permanent failures.


from GenMonads.absprog.synthesize import PrerequisiteError


def _make_runnable_context(tmp_path, *, with_callee=False):
    """Build a minimal context dict the workdir backend can consume.

    When *with_callee* is True the C file's translated form includes a
    sibling callee whose ``_rel_lib.v`` must exist in the user-supplied
    COQ_LIB_DIR.  Used to exercise the prereq check's directory selection.
    """
    c_path = tmp_path / "demo.c"
    c_path.write_text(
        "struct list { int data; struct list *next; };\n"
        "\n"
        "long demo(struct list *x)\n"
        "/*@ Require listrep(x)\n"
        "    Ensure  listrep(x@pre)\n"
        " */\n"
        "{\n"
        "    /*@ Inv listrep(x) */\n"
        "    while (x) { x = x->next; }\n"
        "    return 0;\n"
        "}\n"
    )
    (tmp_path / "_CoqProject").write_text("-Q . X\n", encoding="utf-8")
    return c_path


def test_coq_lib_dir_override_flows_into_prerequisite_check(monkeypatch, tmp_path):
    """Bug fix: ``--coq-lib-dir`` from the CLI must reach the workdir
    pre-spawn check, not get silently dropped in favour of the
    CONFIGURE/env value."""
    from GenMonads.absprog import workdir as workdir_mod
    from GenMonads.absprog.synthesize import _run_command_backend

    c_path = _make_runnable_context(tmp_path)
    # The skeleton (generated inside _run_command_backend) will include the
    # mandatory imports but no project-internal callees — so the check
    # should pass when our explicit coq_lib_dir resolves.  Instrument it
    # to capture the directory the check actually saw.
    seen: Dict = {}
    real_check = workdir_mod.check_prerequisites

    def fake_check(skeleton_text, coq_lib_dir):
        seen["coq_lib_dir"] = coq_lib_dir
        return real_check(skeleton_text, coq_lib_dir)

    monkeypatch.setattr(
        "GenMonads.absprog.workdir.check_prerequisites", fake_check,
    )
    # Don't actually invoke codex — short-circuit by raising after the
    # check, so we only exercise the pre-spawn path.
    monkeypatch.setattr(
        "GenMonads.absprog.synthesize.shutil.which",
        lambda name: "/usr/local/bin/codex" if name == "codex" else None,
    )
    monkeypatch.setattr(
        "GenMonads.absprog.workdir.locate_coq_project",
        lambda start_dir: str(tmp_path / "_CoqProject"),
    )
    # Short-circuit codex with a recognisable error so the test exits the
    # backend cleanly after the prereq check has captured its directory.
    def _stop(*a, **kw):
        raise RuntimeError("test sentinel: stop after prereq check")
    monkeypatch.setattr("GenMonads.absprog.synthesize.subprocess.run", _stop)

    context = {
        "id": "demo",
        "source": {"c_file": str(c_path), "file_id": "demo"},
        "summary": {"func_name": "demo"},
        "generation_policy": {"must_define": ["MretTy"]},
    }
    user_lib_dir = str(tmp_path / "user_libs")
    os.makedirs(user_lib_dir, exist_ok=True)

    with pytest.raises(RuntimeError, match="test sentinel"):
        _run_command_backend(
            prompt_text="x",
            context=context,
            output_dir=str(tmp_path / "synth"),
            coq_lib_dir=user_lib_dir,
        )
    assert seen["coq_lib_dir"] == user_lib_dir


def test_coq_lib_dir_unspecified_falls_back_to_configure(monkeypatch, tmp_path):
    """Without the explicit kwarg, the backend still pulls COQ_LIB_DIR from
    CONFIGURE/env — the historical behaviour stays intact."""
    from GenMonads.absprog import workdir as workdir_mod
    from GenMonads.absprog.synthesize import _run_command_backend

    c_path = _make_runnable_context(tmp_path)
    seen: Dict = {}
    real_check = workdir_mod.check_prerequisites

    def fake_check(skeleton_text, coq_lib_dir):
        seen["coq_lib_dir"] = coq_lib_dir
        return real_check(skeleton_text, coq_lib_dir)

    monkeypatch.setattr(
        "GenMonads.absprog.workdir.check_prerequisites", fake_check,
    )
    monkeypatch.setattr(
        "GenMonads.absprog.synthesize.shutil.which",
        lambda name: "/usr/local/bin/codex" if name == "codex" else None,
    )
    monkeypatch.setattr(
        "GenMonads.absprog.workdir.locate_coq_project",
        lambda start_dir: str(tmp_path / "_CoqProject"),
    )
    def _stop(*a, **kw):
        raise RuntimeError("test sentinel: stop after prereq check")
    monkeypatch.setattr("GenMonads.absprog.synthesize.subprocess.run", _stop)
    fallback = str(tmp_path / "fallback")
    monkeypatch.setattr(
        "GenMonads.absprog.synthesize.read_configure_value",
        lambda key: fallback if key == "COQ_LIB_DIR" else None,
    )

    context = {
        "id": "demo",
        "source": {"c_file": str(c_path), "file_id": "demo"},
        "summary": {"func_name": "demo"},
        "generation_policy": {"must_define": ["MretTy"]},
    }
    with pytest.raises(RuntimeError, match="test sentinel"):
        _run_command_backend(
            prompt_text="x",
            context=context,
            output_dir=str(tmp_path / "synth"),
            coq_lib_dir=None,
        )
    assert seen["coq_lib_dir"] == fallback


def test_missing_callee_lib_raises_prerequisite_error(monkeypatch, tmp_path):
    """When a cross-file callee lib isn't on disk the backend surfaces a
    distinct ``PrerequisiteError`` so the pipeline can break out of the
    retry loop instead of burning every attempt on the same env failure."""
    from GenMonads.absprog.synthesize import _run_command_backend

    c_path = _make_runnable_context(tmp_path)
    # Simulate a skeleton with a missing callee.
    monkeypatch.setattr(
        "GenMonads.absprog.assemble.generate_rel_lib_skeleton_for_file",
        lambda c_file, **kw: "Require Import missing_callee_rel_lib.\n",
    )
    monkeypatch.setattr(
        "GenMonads.absprog.synthesize.shutil.which",
        lambda name: "/usr/local/bin/codex" if name == "codex" else None,
    )
    monkeypatch.setattr(
        "GenMonads.absprog.workdir.locate_coq_project",
        lambda start_dir: str(tmp_path / "_CoqProject"),
    )
    user_lib_dir = str(tmp_path / "user_libs")
    os.makedirs(user_lib_dir, exist_ok=True)

    context = {
        "id": "demo",
        "source": {"c_file": str(c_path), "file_id": "demo"},
        "summary": {"func_name": "demo"},
        "generation_policy": {"must_define": []},
    }
    with pytest.raises(PrerequisiteError, match="missing_callee_rel_lib"):
        _run_command_backend(
            prompt_text="x",
            context=context,
            output_dir=str(tmp_path / "synth"),
            coq_lib_dir=user_lib_dir,
        )


def test_missing_codex_raises_prerequisite_error(monkeypatch, tmp_path):
    from GenMonads.absprog.synthesize import _run_command_backend

    c_path = _make_runnable_context(tmp_path)
    monkeypatch.setattr(
        "GenMonads.absprog.synthesize.shutil.which",
        lambda name: None,
    )
    context = {
        "id": "demo",
        "source": {"c_file": str(c_path), "file_id": "demo"},
        "summary": {"func_name": "demo"},
        "generation_policy": {"must_define": []},
    }
    with pytest.raises(PrerequisiteError, match="codex executable not found"):
        _run_command_backend(
            prompt_text="x",
            context=context,
            output_dir=str(tmp_path / "synth"),
        )


def test_missing_coq_project_raises_prerequisite_error(monkeypatch, tmp_path):
    from GenMonads.absprog.synthesize import _run_command_backend

    c_path = _make_runnable_context(tmp_path)
    (tmp_path / "_CoqProject").unlink()
    monkeypatch.setattr(
        "GenMonads.absprog.synthesize.shutil.which",
        lambda name: "/usr/local/bin/codex" if name == "codex" else None,
    )
    monkeypatch.setattr(
        "GenMonads.absprog.workdir.locate_coq_project",
        lambda start_dir: None,
    )
    monkeypatch.setattr(
        "GenMonads.absprog.assemble.generate_rel_lib_skeleton_for_file",
        lambda c_file, **kw: "(* skeleton *)\n",
    )
    context = {
        "id": "demo",
        "source": {"c_file": str(c_path), "file_id": "demo"},
        "summary": {"func_name": "demo"},
        "generation_policy": {"must_define": []},
    }
    with pytest.raises(PrerequisiteError, match="_CoqProject not found"):
        _run_command_backend(
            prompt_text="x",
            context=context,
            output_dir=str(tmp_path / "synth"),
        )


def test_run_synthesis_pipeline_aborts_on_prerequisite_error(monkeypatch, tmp_path):
    """End-to-end: a PrerequisiteError must abort the per-function retry
    loop after one attempt, recording failure_kind=prerequisite, instead
    of burning every ``--max-retries`` slot."""
    from GenMonads.absprog import synthesize

    def always_raise_prereq(*args, **kwargs):
        raise PrerequisiteError("missing list_tail_rel_lib.v")

    monkeypatch.setattr(
        synthesize, "generate_candidate_response", always_raise_prereq,
    )
    example_path = _write_example_with_gold(tmp_path)
    summary = synthesize.run_synthesis_pipeline(
        input_path=example_path,
        output_dir=str(tmp_path / "synth"),
        backend="command",
        max_retries=2,            # would normally produce 3 attempts
        run_check=False,
    )
    # Exactly one attempt was recorded, not 3.
    assert summary["attempt_count"] == 1
    failure = summary["attempts"][0]
    assert failure["failure_kind"] == "prerequisite"
    assert "list_tail_rel_lib" in failure["failure_message"]
    assert summary["status"] == "failed"


def test_run_synthesis_pipeline_still_retries_on_ordinary_errors(monkeypatch, tmp_path):
    """Regression: an ordinary backend ValueError (not PrerequisiteError)
    must still walk the full retry loop so the repair-prompt flow keeps
    working."""
    from GenMonads.absprog import synthesize

    call_count = {"n": 0}

    def always_value_error(*args, **kwargs):
        call_count["n"] += 1
        raise ValueError("LLM produced garbage")

    monkeypatch.setattr(
        synthesize, "generate_candidate_response", always_value_error,
    )
    example_path = _write_example_with_gold(tmp_path)
    summary = synthesize.run_synthesis_pipeline(
        input_path=example_path,
        output_dir=str(tmp_path / "synth"),
        backend="command",
        max_retries=2,
        run_check=False,
    )
    # Three attempts as configured by --max-retries=2.
    assert call_count["n"] == 3
    assert summary["attempt_count"] == 3
    for attempt in summary["attempts"]:
        assert attempt["failure_kind"] == "backend"


# ---------------------------------------------------------------------------
# Bug 1 + Bug 2 — promote / merge honor --coq-lib-dir.


def test_promote_rel_lib_writes_to_explicit_coq_lib_dir(monkeypatch, tmp_path):
    """Regression for Bug 1: when an explicit ``coq_lib_dir`` is passed,
    the promoted lib lands there — not in ``_default_coq_lib_dir()``."""
    assembled = tmp_path / "attempt-0" / "demo_rel_lib.v"
    assembled.parent.mkdir(parents=True)
    assembled.write_text("Definition demo_M := tt.\n")

    user_dir = tmp_path / "user_libs"
    default_dir = tmp_path / "wrong_default"
    # If the fix isn't in place we'd see the file land in default_dir.
    monkeypatch.setattr(
        "GenMonads.absprog.synthesize._default_coq_lib_dir",
        lambda: str(default_dir),
    )
    # Skip the recompile — that's exercised separately.
    monkeypatch.setattr(
        "GenMonads.absprog.synthesize.check_rocq_file",
        lambda path: {"status": "skipped", "passed": False, "reason": "check disabled", "stdout": "", "stderr": ""},
    )

    promoted = _promote_rel_lib_if_accepted(
        str(assembled), "demo", "passed",
        coq_lib_dir=str(user_dir),
    )

    assert promoted == str(user_dir / "demo_rel_lib.v")
    assert (user_dir / "demo_rel_lib.v").exists()
    assert not (default_dir / "demo_rel_lib.v").exists(), \
        "promotion fell back to the CONFIGURE default despite --coq-lib-dir"


def test_promote_rel_lib_falls_back_to_default_when_unset(monkeypatch, tmp_path):
    """When the caller doesn't pass ``coq_lib_dir``, the historical
    CONFIGURE/env default is still used.  No regression for callers that
    weren't updated."""
    assembled = tmp_path / "attempt-0" / "demo_rel_lib.v"
    assembled.parent.mkdir(parents=True)
    assembled.write_text("Definition demo_M := tt.\n")

    fallback_dir = tmp_path / "fallback"
    monkeypatch.setattr(
        "GenMonads.absprog.synthesize._default_coq_lib_dir",
        lambda: str(fallback_dir),
    )
    monkeypatch.setattr(
        "GenMonads.absprog.synthesize.check_rocq_file",
        lambda path: {"status": "skipped", "passed": False, "reason": "check disabled", "stdout": "", "stderr": ""},
    )

    promoted = _promote_rel_lib_if_accepted(
        str(assembled), "demo", "passed",  # coq_lib_dir omitted
    )

    assert promoted == str(fallback_dir / "demo_rel_lib.v")
    assert (fallback_dir / "demo_rel_lib.v").exists()


def test_run_synthesis_pipeline_threads_coq_lib_dir_into_promotion(monkeypatch, tmp_path):
    """End-to-end: ``--coq-lib-dir`` flows from run_synthesis_pipeline into
    the promotion call.  Pin this so a future refactor can't accidentally
    drop the kwarg again."""
    import GenMonads.absprog.synthesize as synth

    promote_calls = []

    def fake_promote(assembled_file, context_id, status, coq_lib_dir=None):
        promote_calls.append({
            "assembled_file": assembled_file,
            "context_id": context_id,
            "status": status,
            "coq_lib_dir": coq_lib_dir,
        })
        return ""

    monkeypatch.setattr(synth, "_promote_rel_lib_if_accepted", fake_promote)
    # Skip the rest of the pipeline by making the backend return a fixed
    # response that the assembler accepts.
    gold = _GOLD_DATA
    response_text = "\n".join([
        "```coq",
        f"Definition MretTy : Type := {gold['MretTy']}.",
        gold["components"]["M_loop_before"],
        gold["components"]["M_1"],
        gold["components"]["M_2"],
        gold["components"]["M_loop_end"],
        "```",
        "",
    ])
    monkeypatch.setattr(
        synth, "generate_candidate_response",
        lambda *a, **kw: response_text,
    )

    example_path = _write_example_with_gold(tmp_path)
    user_dir = str(tmp_path / "my_libs")
    synth.run_synthesis_pipeline(
        input_path=example_path,
        output_dir=str(tmp_path / "synth"),
        backend="command",
        run_check=False,
        coq_lib_dir=user_dir,
    )

    assert promote_calls, "promote was never called"
    assert promote_calls[-1]["coq_lib_dir"] == user_dir


def test_synth_cli_multi_function_merge_uses_explicit_coq_lib_dir(monkeypatch, tmp_path):
    """Regression for Bug 2: ``synth_cli``'s multi-function merge path
    writes the merged lib to ``args.coq_lib_dir`` when set, not the
    CONFIGURE default."""
    # synth_cli.py:323-334 reads args.coq_lib_dir and falls back to
    # _default_coq_lib_dir() — we verify the line by inspecting it.
    src = open("GenMonads/absprog/synth_cli.py").read()
    assert "libs_dir = args.coq_lib_dir or _default_coq_lib_dir()" in src, (
        "synth_cli multi-function merge no longer honors --coq-lib-dir; "
        "Bug 2 has regressed."
    )
