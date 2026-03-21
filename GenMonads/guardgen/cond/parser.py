# guardgen/cond/parser.py
from .lexer import lex_cond
from .ast import AtomKind, AtomCond, BoolNode

class Parser:
    def __init__(self, toks):
        self.toks = toks
        self.pos = 0

    def peek(self):
        return self.toks[self.pos] if self.pos < len(self.toks) else None

    def eat(self, kind: str):
        tok = self.peek()
        if not tok or tok.kind != kind:
            raise ValueError(f"Expected {kind}, got {tok}")
        self.pos += 1
        return tok

    def parse_expr(self) -> BoolNode:
        return self.parse_or()

    def parse_or(self) -> BoolNode:
        node = self.parse_and()
        while self.peek() and self.peek().kind == "OR":
            self.eat("OR")
            rhs = self.parse_and()
            node = BoolNode("or", left=node, right=rhs)
        return node

    def parse_and(self) -> BoolNode:
        node = self.parse_not()
        while self.peek() and self.peek().kind == "AND":
            self.eat("AND")
            rhs = self.parse_not()
            node = BoolNode("and", left=node, right=rhs)
        return node

    def parse_not(self) -> BoolNode:
        # Keep NOT at this level so "! p" becomes BoolNode("not", child=atom(p))
        if self.peek() and self.peek().kind == "NOT":
            self.eat("NOT")
            child = self.parse_not()
            return BoolNode("not", child=child)
        return self.parse_atom_expr()

    def parse_atom_expr(self) -> BoolNode:
        tok = self.peek()
        if not tok:
            raise ValueError("Unexpected end")
        if tok.kind == "LPAREN":
            self.eat("LPAREN")
            node = self.parse_expr()
            self.eat("RPAREN")
            return node
        # Atom (supports "p", "p == null", "p != 0", "x == y", etc.)
        atom = self.parse_atomic_cond()
        return BoolNode("atom", atom=atom)

    def parse_atomic_cond(self) -> AtomCond:
        """
        Accept a bare identifier "p" as sugar for "p != null".
        Also accept "p->field" as a compound pointer name (sugar for "p->field != null").
        The translation layer will validate that the pointer is a spatial root pointer.
        """
        left_tok = self.eat("ID")
        left = left_tok.text

        # Handle field dereference: p->next becomes compound name "p->next"
        if self.peek() and self.peek().kind == "ARROW":
            self.eat("ARROW")
            field_tok = self.eat("ID")
            left = f"{left}->{field_tok.text}"

        op = self.peek()
        # If no operator (or boundary), treat "p" as "p != null"
        if (op is None) or (op.kind in ("RPAREN", "AND", "OR")):
            return AtomCond(AtomKind.PTR_NE_NULL, ptr1=left)

        if op.kind == "EQ":
            self.eat("EQ")
            rhs = self.peek()
            if not rhs:
                raise ValueError("Missing RHS")
            if rhs.kind == "ID":
                idtxt = rhs.text.lower()
                if idtxt in ("null", "nullptr"):
                    self.eat("ID")
                    return AtomCond(AtomKind.PTR_EQ_NULL, ptr1=left)
                else:
                    self.eat("ID")
                    return AtomCond(AtomKind.PTR_EQ_PTR, ptr1=left, ptr2=rhs.text)
            elif rhs.kind == "NUM":  # 0
                self.eat("NUM")
                return AtomCond(AtomKind.PTR_EQ_NULL, ptr1=left)
            else:
                raise ValueError("RHS must be null/0 or pointer")

        elif op.kind in ("NE1", "NE2"):
            self.eat(op.kind)
            rhs = self.peek()
            if not rhs:
                raise ValueError("Missing RHS")
            if rhs.kind == "ID":
                idtxt = rhs.text.lower()
                if idtxt in ("null", "nullptr"):
                    self.eat("ID")
                    return AtomCond(AtomKind.PTR_NE_NULL, ptr1=left)
                else:
                    self.eat("ID")
                    return AtomCond(AtomKind.PTR_NE_PTR, ptr1=left, ptr2=rhs.text)
            elif rhs.kind == "NUM":
                self.eat("NUM")
                return AtomCond(AtomKind.PTR_NE_NULL, ptr1=left)
            else:
                raise ValueError("RHS must be null/0 or pointer")

        else:
            raise ValueError(f"Unsupported operator {op.text}")


def parse_cond_full(cond: str) -> BoolNode:
    toks = lex_cond(cond)
    p = Parser(toks)
    node = p.parse_expr()
    if p.peek():
        raise ValueError("Extra tokens after cond")
    return node
