# guardgen/cond/ast.py
from dataclasses import dataclass
from enum import Enum
from typing import Optional

class AtomKind(Enum):
    PTR_EQ_NULL = 1
    PTR_NE_NULL = 2
    PTR_EQ_PTR  = 3
    PTR_NE_PTR  = 4
    # Scalar (integer) comparison between two operands.  Each operand is a C
    # lvalue (resolved to an abstract scalar via store bindings) or a numeric
    # literal.  ``op`` is one of: '<', '<=', '>', '>=', '==', '!='.
    SCALAR_CMP  = 5

@dataclass
class AtomCond:
    kind: AtomKind
    ptr1: str
    ptr2: Optional[str] = None
    op: Optional[str] = None

@dataclass
class BoolNode:
    kind: str
    atom: Optional[AtomCond] = None
    child: "Optional[BoolNode]" = None
    left: "Optional[BoolNode]" = None
    right: "Optional[BoolNode]" = None
