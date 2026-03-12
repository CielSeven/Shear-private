# guardgen/cond/ast.py
from dataclasses import dataclass
from enum import Enum
from typing import Optional

class AtomKind(Enum):
    PTR_EQ_NULL = 1
    PTR_NE_NULL = 2
    PTR_EQ_PTR  = 3
    PTR_NE_PTR  = 4

@dataclass
class AtomCond:
    kind: AtomKind
    ptr1: str
    ptr2: Optional[str] = None

@dataclass
class BoolNode:
    kind: str
    atom: Optional[AtomCond] = None
    child: "Optional[BoolNode]" = None
    left: "Optional[BoolNode]" = None
    right: "Optional[BoolNode]" = None
