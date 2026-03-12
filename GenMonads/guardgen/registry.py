# guardgen/registry.py
from dataclasses import dataclass
from typing import Callable, Literal, Optional

PredKind = Literal["root", "segment"]

@dataclass
class PredicateSpec:
    name: str
    kind: PredKind            # "root" | "segment"
    arity: int
    parse_args: Callable[[list[str]], dict]
    to_coq_root_null: Optional[Callable[[dict, bool], str]] = None
    to_coq_segment_eq: Optional[Callable[[dict, bool, bool], str]] = None
    abs_names: Callable[[dict], list[str]] = lambda payload: []

PREDICATES: dict[str, PredicateSpec] = {}

def register_predicate(spec: PredicateSpec) -> None:
    if spec.name in PREDICATES:
        raise ValueError(f"Predicate {spec.name} already registered")
    PREDICATES[spec.name] = spec
