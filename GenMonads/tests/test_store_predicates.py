"""Regression tests for the typed ``store(...)`` pipeline: extraction,
desugaring of ``EXPR -> FIELD == VAR``, and data-witness carrier selection.
"""

import textwrap

from GenMonads.transshape.c_types import (
    build_type_env,
    collect_struct_decls,
    coq_type_of,
    is_pointer_type,
    is_scalar_type,
    parse_struct_decls,
    resolve_field_type,
)
from GenMonads.transshape.translator import (
    ShapeTranslator,
    _desugar_field_equalities,
    _extract_memory_state_predicates,
    parse_store_predicates,
)
from GenMonads.transshape.data_witness import (
    extract_data_witnesses,
    extract_data_witnesses_typed,
    extract_pre_existing_vars,
)


def _write(tmp_path, name, content):
    path = tmp_path / name
    path.write_text(textwrap.dedent(content), encoding="utf-8")
    return str(path)


# ---------------------------------------------------------------------------
# c_types.py


def test_parse_struct_decls_extracts_field_types():
    decls = parse_struct_decls(
        "struct list { int data; struct list *next; };\n"
        "struct counter { unsigned long count; };"
    )
    assert decls["list"]["data"] == "int"
    assert decls["list"]["next"] == "struct list *"
    assert decls["counter"]["count"] == "unsigned long"


def test_type_classifier_recognises_pointers_and_scalars():
    assert is_pointer_type("struct list *")
    assert not is_pointer_type("int")
    assert is_scalar_type("int")
    assert is_scalar_type("unsigned long")
    assert not is_scalar_type("struct list *")
    assert coq_type_of("int") == "Z"
    assert coq_type_of("unsigned long") == "Z"
    assert coq_type_of("_Bool") == "bool"
    assert coq_type_of("struct list *") is None


def test_build_type_env_skips_forward_declarations(tmp_path):
    src = (
        'struct list { int data; struct list *next; };\n'
        'struct list * sll_merge(struct list *x, struct list *y);\n'
        'struct list * sll_multi_merge(struct list *x, struct list *y, struct list *z)\n'
        '{\n'
        '    struct list *t, *u;\n'
        '    return x;\n'
        '}\n'
    )
    # Forward decl shouldn't leak its params into the definition's env.
    assert build_type_env(src, "sll_merge") == {}
    env = build_type_env(src, "sll_multi_merge")
    assert env["__return"] == "struct list *"
    assert env["x"] == "struct list *"
    assert env["t"] == "struct list *"
    assert env["u"] == "struct list *"


def test_resolve_field_type_uses_struct_decls():
    decls = parse_struct_decls(
        "struct list { int data; struct list *next; };"
    )
    env = {"__return": "struct list *", "t": "struct list *"}
    assert resolve_field_type("__return", "data", env, decls) == "int"
    assert resolve_field_type("t", "next", env, decls) == "struct list *"
    # Unknown struct -> None.
    assert resolve_field_type("z", "data", env, decls) is None


# ---------------------------------------------------------------------------
# translator.py: extraction + desugaring


def test_extract_memory_state_handles_nested_parens_in_store_args():
    text = (
        "exists v, store(&(t->data), int, v) && "
        "store(&(t->next), struct list *, u) && t != 0 * sll(y, l1)"
    )
    cleaned, kept = _extract_memory_state_predicates(text)
    assert "store(&(t->data), int, v)" in kept
    assert "store(&(t->next), struct list *, u)" in kept
    assert "store(" not in cleaned


def test_desugar_field_equality_emits_typed_store_for_scalar_field():
    decls = parse_struct_decls(
        "struct list { int data; struct list *next; };"
    )
    env = {"__return": "struct list *"}
    out = _desugar_field_equalities(
        "exists v, __return -> data == v && lseg(x, __return)",
        env, decls,
    )
    assert "store(&(__return->data), int, v)" in out
    assert "__return -> data == v" not in out


def test_desugar_handles_reverse_field_equality():
    decls = parse_struct_decls(
        "struct list { int data; struct list *next; };"
    )
    env = {"t": "struct list *"}
    out = _desugar_field_equalities(
        "exists v, v == t -> data && u == t -> next && sll(y, l)",
        env, decls,
    )
    assert "store(&(t->data), int, v)" in out
    assert "store(&(t->next), struct list *, u)" in out


def test_desugar_skips_when_struct_unknown():
    out = _desugar_field_equalities(
        "exists v, __return -> data == v",
        type_env={"__return": "struct list *"},
        struct_decls={},  # struct unknown
    )
    assert out == "exists v, __return -> data == v"


def test_desugar_does_not_double_splice_explicit_store():
    decls = parse_struct_decls(
        "struct list { int data; struct list *next; };"
    )
    env = {"__return": "struct list *"}
    out = _desugar_field_equalities(
        "exists v, store(&(__return->data), int, v) && __return -> data == v",
        env, decls,
    )
    # The explicit ``store`` survives unchanged; the redundant ``== v``
    # equality is left alone (not transformed into a second ``store``).
    assert out.count("store(&(__return->data)") == 1


def test_parse_store_predicates_returns_triples():
    triples = parse_store_predicates(
        "store(&(t->data), int, v) * store(&(t->next), struct list *, u)"
    )
    assert triples == [
        ("&(t->data)", "int", "v"),
        ("&(t->next)", "struct list *", "u"),
    ]


# ---------------------------------------------------------------------------
# data_witness.py


def test_extract_data_witness_keeps_scalar_store_var():
    inv = (
        "exists v, store(&(t->data), int, v) * sll(t, l1)"
    )
    assert extract_data_witnesses(inv, ["v"]) == ["v"]
    assert extract_data_witnesses_typed(inv, ["v"]) == [("v", "Z")]


def test_extract_data_witness_skips_pointer_store_var():
    inv = (
        "exists st, store(&stop, struct list *, st) * sll(y, l1)"
    )
    assert extract_data_witnesses(inv, ["st"]) == []
    assert extract_data_witnesses_typed(inv, ["st"]) == []


def test_extract_data_witness_with_long_typed_store():
    inv = "exists s, store(&sum, long, s)"
    assert extract_data_witnesses_typed(inv, ["s"]) == [("s", "Z")]


def test_extract_pre_existing_vars_parses_exists_header():
    assert extract_pre_existing_vars(
        "exists v w, v == t -> data && ..."
    ) == ["v", "w"]


# ---------------------------------------------------------------------------
# End-to-end: ShapeTranslator drives desugaring + splicing


def test_shape_translator_desugars_ensure_field_equality():
    src = (
        'struct list { int data; struct list *next; };\n'
        'struct list *list_tail(struct list *x) { return x; }\n'
    )
    decls = parse_struct_decls(src)
    env = build_type_env(src, "list_tail")
    assertion = (
        "exists v, __return != 0 && __return -> next == 0 && "
        "__return -> data == v && lseg(x, __return)"
    )
    translator = ShapeTranslator()
    translated, _ = translator.translate_assertion(
        assertion, type_env=env, struct_decls=decls,
    )
    # The pointer-field equality survives as a ``store`` (pointer type, not
    # carried), the data-field equality becomes a scalar ``store`` (carried),
    # and ``lseg`` becomes ``sllseg`` with a fresh existential.
    assert "store(&(__return->data), int, v)" in translated
    assert "store(&(__return->next), struct list *, 0)" in translated
    assert "sllseg(x, __return," in translated


def test_shape_translator_preserves_undef_data_at_and_store():
    src = (
        'struct counter { long sum; };\n'
        'long compute(long n) { long sum = 0; return sum; }\n'
    )
    decls = parse_struct_decls(src)
    env = build_type_env(src, "compute")
    assertion = (
        "exists s, p != 0 && store(&sum, long, s) * "
        "undef_data_at(&tmp, long) * listrep(p)"
    )
    translator = ShapeTranslator()
    translated, _ = translator.translate_assertion(
        assertion, type_env=env, struct_decls=decls,
    )
    assert "store(&sum, long, s)" in translated
    assert "undef_data_at(&tmp, long)" in translated
