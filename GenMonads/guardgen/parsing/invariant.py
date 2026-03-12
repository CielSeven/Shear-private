# guardgen/parsing/invariant.py
import re
from dataclasses import dataclass
from ..registry import PredicateSpec, PREDICATES

@dataclass
class ShAtom:
    spec: PredicateSpec
    payload: dict

def normalize_inv(inv: str) -> str:
    s = re.sub(r"\s+", " ", inv).strip()
    s = re.sub(r"\(\s*", "(", s)
    s = re.sub(r"\s*\)", ")", s)
    s = re.sub(r"\s*,\s*", ",", s)
    return s

_PRED_CALL_RE = re.compile(r'^([A-Za-z_][A-Za-z0-9_]*)\((.*)\)$')

def _split_args(argstr: str) -> list[str]:
    if argstr.strip() == "":
        return []
    return [a.strip() for a in argstr.split(",")]

def parse_invariant(inv: str) -> list[ShAtom]:
    chunks = re.split(r'\s*(?:&&|\*)\s*', inv)
    atoms: list[ShAtom] = []
    for chunk in chunks:
        s = chunk.strip()
        if not s:
            continue
        m = _PRED_CALL_RE.match(s)
        if not m:
            # pure part like "x=3" — ignore
            continue
        name, inner = m.group(1), m.group(2)
        spec = PREDICATES.get(name)
        if spec is None:
            raise ValueError(f"Unknown predicate '{name}' (not registered)")
        args = _split_args(inner)
        if len(args) != spec.arity:
            raise ValueError(f"{name}(...) expects {spec.arity} args, got {args}")
        payload = spec.parse_args(args)
        atoms.append(ShAtom(spec=spec, payload=payload))
    return atoms
