# guardgen/registry.py
from dataclasses import dataclass
import json
import os
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


_DATA_DIR = os.path.normpath(os.path.join(os.path.dirname(__file__), "..", "data"))
_GUARD_PREDICATE_FILE = os.path.join(_DATA_DIR, "guard_predicates.json")


def _make_parse_args(payload_map: dict[str, int], arity: int) -> Callable[[list[str]], dict]:
    def _parse(args: list[str]) -> dict:
        if len(args) != arity:
            raise ValueError(f"Expected {arity} args, got {args}")
        payload = {}
        for key, index in payload_map.items():
            payload[key] = args[index]
        return payload
    return _parse


def _make_root_null_handler(eq_template: str, ne_template: str) -> Callable[[dict, bool], str]:
    def _handler(payload: dict, is_eq: bool) -> str:
        template = eq_template if is_eq else ne_template
        return template.format(**payload)
    return _handler


def _make_segment_eq_handler(eq_template: str, ne_template: str) -> Callable[[dict, bool, bool], str]:
    def _handler(payload: dict, is_eq: bool, reversed_match: bool) -> str:
        template = eq_template if is_eq else ne_template
        return template.format(**payload)
    return _handler


def _make_abs_names(abs_fields: list[str]) -> Callable[[dict], list[str]]:
    def _abs(payload: dict) -> list[str]:
        return [payload[field] for field in abs_fields]
    return _abs


def load_predicates_from_json(config_path: str = _GUARD_PREDICATE_FILE) -> None:
    with open(config_path, "r", encoding="utf-8") as f:
        data = json.load(f)

    for name, raw_spec in data.items():
        kind = raw_spec["kind"]
        arity = raw_spec["arity"]
        payload_map = {k: int(v) for k, v in raw_spec["payload"].items()}
        abs_fields = list(raw_spec.get("abs_names", []))

        root_null = raw_spec.get("root_null")
        segment_eq = raw_spec.get("segment_eq")

        register_predicate(PredicateSpec(
            name=name,
            kind=kind,
            arity=arity,
            parse_args=_make_parse_args(payload_map, arity),
            to_coq_root_null=(
                _make_root_null_handler(root_null["eq"], root_null["ne"])
                if root_null else None
            ),
            to_coq_segment_eq=(
                _make_segment_eq_handler(segment_eq["eq"], segment_eq["ne"])
                if segment_eq else None
            ),
            abs_names=_make_abs_names(abs_fields),
        ))
