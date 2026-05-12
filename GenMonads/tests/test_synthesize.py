import json
import os
import subprocess

from GenMonads.absprog.assemble import assemble_rel_lib_from_blocks
from GenMonads.absprog.context import collect_synthesis_context
from GenMonads.absprog.parse_coq import parse_synthesized_components
from GenMonads.absprog.synthesize import (
    _append_missing_residual_decls_to_rel_c,
    _eliminate_mretty_in_rel_c,
    _extract_mretty_type,
    _promote_rel_lib_if_accepted,
    _sync_residual_artifacts,
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
    c_file = _write_sll_multi_merge_c(tmp_path)
    context = collect_synthesis_context(c_file, func_name="sll_multi_merge")

    prompt = render_prompt(context)

    assert "## Available Callees" in prompt
    assert "`sll_merge_M` (same-file): list Z -> list Z -> MONAD (list Z)" in prompt
    assert "Use opaque callee placeholders when modeling same-file calls: sll_merge_M" in prompt
    assert "## Selected Scaffold" in prompt
    assert "Template case: both" in prompt
    assert "early_result" in prompt
    assert "sll_multi_merge_M_after_loop" in prompt
    assert "The following definitions are already generated by the scaffold. Do not redefine them: sll_multi_merge_M_after_loop" in prompt
    assert "Use the Selected Scaffold above as the authoritative composition rule for this target." in prompt
    assert "## Opaque Call Obligations" in prompt
    assert "Do not replace helper-call results with `any`." in prompt
    assert "`t = sll_merge(y, z);` must use `sll_merge_M`" in prompt
    assert "M_loop_M1: (list Z * list Z * list Z * list Z * Z) -> MONAD MretTy" in prompt
    assert "M_loop_M2: (list Z * list Z * list Z * list Z * Z) -> MONAD (early_result (list Z * list Z * list Z * list Z * Z) (list Z))" in prompt
    assert "break (Continue r)" in prompt
    assert "| Continue a'' => continue a''" in prompt
    assert "| ReturnNow r' => break (ReturnNow r')" in prompt
    assert "The full program composes:" not in prompt
    assert "f_M(l1, ..., lm) :=" not in prompt


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


def test_generate_candidate_response_command_backend_uses_stdin_and_placeholders(monkeypatch, tmp_path):
    example = _load_example(tmp_path)
    prompt_file = tmp_path / "prompt.txt"
    context_file = tmp_path / "context.json"
    prompt_text = "PROMPT CONTENT"

    seen = {}

    def fake_run(cmd, shell, text, input, capture_output):
        seen["cmd"] = cmd
        seen["shell"] = shell
        seen["text"] = text
        seen["input"] = input
        seen["capture_output"] = capture_output
        return subprocess.CompletedProcess(
            args=cmd,
            returncode=0,
            stdout="```coq\nDefinition MretTy : Type := list Z.\n```",
            stderr="",
        )

    monkeypatch.setattr("GenMonads.absprog.synthesize.subprocess.run", fake_run)

    response = generate_candidate_response(
        example,
        backend="command",
        prompt_text=prompt_text,
        prompt_file=str(prompt_file),
        context_file=str(context_file),
        output_dir=str(tmp_path),
        backend_response_file=str(tmp_path / "backend.txt"),
        command="echo using {prompt_file} for {func_name}",
    )

    assert "Definition MretTy" in response
    assert seen["input"] == prompt_text
    assert seen["shell"] is True
    assert str(prompt_file) in seen["cmd"]
    assert "sll_reverse" in seen["cmd"]


def test_run_synthesis_pipeline_command_backend_writes_artifacts(monkeypatch, tmp_path):
    gold = _GOLD_DATA
    output_dir = tmp_path / "synth"
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

    def fake_run(cmd, shell, text, input, capture_output):
        return subprocess.CompletedProcess(
            args=cmd,
            returncode=0,
            stdout=response_text,
            stderr="",
        )

    monkeypatch.setattr("GenMonads.absprog.synthesize.subprocess.run", fake_run)

    example_path = _write_example_with_gold(tmp_path)
    summary = run_synthesis_pipeline(
        input_path=example_path,
        output_dir=str(output_dir),
        backend="command",
        command="codex exec",
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
    checks = iter(
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

    monkeypatch.setattr(
        "GenMonads.absprog.synthesize.generate_candidate_response",
        lambda *_args, **_kwargs: response_text,
    )
    monkeypatch.setattr(
        "GenMonads.absprog.synthesize.check_rocq_file",
        lambda _path: next(checks),
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


def test_promote_rel_lib_if_accepted_copies_compiled_sidecars(monkeypatch, tmp_path):
    assembled = tmp_path / "attempt-0" / "demo_rel_lib.v"
    assembled.parent.mkdir(parents=True)
    assembled.write_text("Definition x := 0.\n", encoding="utf-8")
    for ext in [".vo", ".vok", ".vos", ".glob"]:
        assembled.with_suffix(ext).write_text(ext, encoding="utf-8")

    target_dir = tmp_path / "libs"
    monkeypatch.setenv("COQ_LIB_DIR", str(target_dir))

    promoted = _promote_rel_lib_if_accepted(str(assembled), "demo", "passed")

    assert promoted == str(target_dir / "demo_rel_lib.v")
    assert (target_dir / "demo_rel_lib.v").exists()
    assert (target_dir / "demo_rel_lib.vo").read_text(encoding="utf-8") == ".vo"
    assert (target_dir / "demo_rel_lib.vok").read_text(encoding="utf-8") == ".vok"
    assert (target_dir / "demo_rel_lib.vos").read_text(encoding="utf-8") == ".vos"
    assert (target_dir / "demo_rel_lib.glob").read_text(encoding="utf-8") == ".glob"
