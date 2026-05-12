# guardgen/predicates/sll.py
from ..registry import PredicateSpec, register_predicate

def _parse(args: list[str]) -> dict:
    if len(args) != 2:
        raise ValueError(f"sll(...) expects 2 args, got {args}")
    return {"ptr": args[0], "abs": args[1]}

def _root_null(payload: dict, is_eq: bool) -> str:
    l = payload["abs"]
    return f"{l} = []" if is_eq else f"{l} <> []"

def _field_deref_null(payload: dict, field: str, is_eq: bool) -> str:
    """Translate ``<root>-><field> {==,!=} null`` for sll.

    The predicate ``sll(p, l)`` decomposes (when ``p != null``) into
    ``p -> next == nxt && sll(nxt, l')`` where ``l = head :: l'``.  So
    ``p->next == null`` ⇔ the tail of ``l`` is empty (the list has exactly
    one element); ``p->next != null`` ⇔ the tail of ``l`` is non-empty
    (the list has at least two elements).
    """
    if field != "next":
        raise ValueError(
            f"sll: field deref '->{field}' is not supported "
            f"(only 'next' is recognized)"
        )
    l = payload["abs"]
    return f"tl {l} = []" if is_eq else f"tl {l} <> []"

def _abs(payload: dict) -> list[str]:
    return [payload["abs"]]

register_predicate(PredicateSpec(
    name="sll",
    kind="root",
    arity=2,
    parse_args=_parse,
    to_coq_root_null=_root_null,
    to_coq_field_deref_null=_field_deref_null,
    abs_names=_abs,
))


def _parse(args: list[str]) -> dict:
    if len(args) != 3:
        raise ValueError(f"sllseg(...) expects 3 args, got {args}")
    return {"start": args[0], "end": args[1], "seg_abs": args[2]}

def _eq(payload: dict, is_eq: bool, reversed_match: bool) -> str:
    l = payload["seg_abs"]
    return f"{l} = []" if is_eq else f"{l} <> []"

def _abs(payload: dict) -> list[str]:
    return [payload["seg_abs"]]

register_predicate(PredicateSpec(
    name="sllseg",
    kind="segment",
    arity=3,
    parse_args=_parse,
    to_coq_segment_eq=_eq,
    abs_names=_abs,
))
