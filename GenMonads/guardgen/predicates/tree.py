# guardgen/predicates/tree.py
from ..registry import PredicateSpec, register_predicate

def _parse(args: list[str]) -> dict:
    if len(args) != 2:
        raise ValueError(f"store_tree(...) expects 2 args, got {args}")
    return {"ptr": args[0], "abs": args[1]}

def _root_null(payload: dict, is_eq: bool) -> str:
    t = payload["abs"]
    return f"{t} = empty" if is_eq else f"{t} <> empty"

def _abs(payload: dict) -> list[str]:
    return [payload["abs"]]

register_predicate(PredicateSpec(
    name="store_tree",
    kind="root",
    arity=2,
    parse_args=_parse,
    to_coq_root_null=_root_null,
    abs_names=_abs,
))
