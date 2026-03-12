"""
Parser for shape assertion formulas.

This module provides a parser to convert assertion strings into AST representations
and a recovery function to convert AST back to assertion strings.
"""

from dataclasses import dataclass
from typing import List, Optional, Union
import re


# AST Node Classes
@dataclass
class Var:
    """Variable or identifier."""
    name: str

    def __repr__(self):
        return f"Var({self.name})"


@dataclass
class BinOp:
    """Binary operation (==, !=, etc.)."""
    op: str
    left: 'Expr'
    right: 'Expr'

    def __repr__(self):
        return f"BinOp({self.op}, {self.left}, {self.right})"


@dataclass
class FieldAccess:
    """Field access (e.g., t->next, t->data)."""
    obj: 'Expr'
    field: str

    def __repr__(self):
        return f"FieldAccess({self.obj}, {self.field})"


@dataclass
class Predicate:
    """Shape predicate (e.g., listrep(x), lseg(x,y))."""
    name: str
    args: List['Expr']

    def __repr__(self):
        return f"Predicate({self.name}, {self.args})"


@dataclass
class SepConj:
    """Separating conjunction (*)."""
    formulas: List['Formula']

    def __repr__(self):
        return f"SepConj({self.formulas})"


@dataclass
class AndConj:
    """Logical conjunction (&&)."""
    formulas: List['Formula']

    def __repr__(self):
        return f"AndConj({self.formulas})"


@dataclass
class Exists:
    """Existential quantifier."""
    vars: List[str]
    body: 'Formula'

    def __repr__(self):
        return f"Exists({self.vars}, {self.body})"


# Type aliases for clarity
Expr = Union[Var, BinOp, FieldAccess, int]
Formula = Union[BinOp, Predicate, SepConj, AndConj, Exists]


class AssertionParser:
    """Parser for shape assertion formulas."""

    def __init__(self, text: str):
        self.text = text.strip()
        self.pos = 0

    def current_char(self) -> Optional[str]:
        """Get current character."""
        if self.pos < len(self.text):
            return self.text[self.pos]
        return None

    def peek_char(self, offset: int = 1) -> Optional[str]:
        """Peek ahead at character."""
        pos = self.pos + offset
        if pos < len(self.text):
            return self.text[pos]
        return None

    def skip_whitespace(self):
        """Skip whitespace characters."""
        while self.pos < len(self.text) and self.text[self.pos].isspace():
            self.pos += 1

    def consume(self, expected: str) -> bool:
        """Try to consume expected string."""
        self.skip_whitespace()
        if self.text[self.pos:].startswith(expected):
            self.pos += len(expected)
            return True
        return False

    def parse_identifier(self) -> Optional[str]:
        """Parse an identifier."""
        self.skip_whitespace()
        match = re.match(r'[a-zA-Z_][a-zA-Z0-9_]*', self.text[self.pos:])
        if match:
            ident = match.group(0)
            self.pos += len(ident)
            return ident
        return None

    def parse_number(self) -> Optional[int]:
        """Parse a number."""
        self.skip_whitespace()
        match = re.match(r'\d+', self.text[self.pos:])
        if match:
            num = int(match.group(0))
            self.pos += len(match.group(0))
            return num
        return None

    def parse_expr(self) -> Expr:
        """Parse an expression (variable, number, or field access)."""
        self.skip_whitespace()

        # Try to parse number
        num = self.parse_number()
        if num is not None:
            return num

        # Parse identifier
        ident = self.parse_identifier()
        if ident is None:
            raise ValueError(f"Expected identifier at position {self.pos}")

        # Check for @pre suffix
        if self.consume('@pre'):
            ident = f"{ident}@pre"

        expr = Var(ident)

        # Check for field access chain (->)
        while self.consume('->'):
            field = self.parse_identifier()
            if field is None:
                raise ValueError(f"Expected field name after -> at position {self.pos}")
            expr = FieldAccess(expr, field)

        return expr

    def parse_comparison(self) -> BinOp:
        """Parse a comparison (e.g., t != 0, t->next == 0)."""
        left = self.parse_expr()

        self.skip_whitespace()
        # Parse operator
        if self.consume('=='):
            op = '=='
        elif self.consume('!='):
            op = '!='
        else:
            raise ValueError(f"Expected comparison operator at position {self.pos}")

        right = self.parse_expr()

        return BinOp(op, left, right)

    def parse_predicate(self) -> Predicate:
        """Parse a shape predicate (e.g., listrep(x), lseg(x,y))."""
        name = self.parse_identifier()
        if name is None:
            raise ValueError(f"Expected predicate name at position {self.pos}")

        if not self.consume('('):
            raise ValueError(f"Expected '(' after predicate name at position {self.pos}")

        args = []
        while True:
            self.skip_whitespace()
            if self.consume(')'):
                break

            args.append(self.parse_expr())

            self.skip_whitespace()
            if not self.consume(','):
                if not self.consume(')'):
                    raise ValueError(f"Expected ',' or ')' at position {self.pos}")
                break

        return Predicate(name, args)

    def parse_atomic(self) -> Formula:
        """Parse an atomic formula (comparison or predicate)."""
        self.skip_whitespace()

        # Check for 'emp' (empty heap predicate)
        if self.text[self.pos:].startswith('emp') and \
           (self.pos + 3 >= len(self.text) or not self.text[self.pos + 3].isalnum()):
            self.pos += 3
            return Predicate('emp', [])

        # Save position for backtracking
        saved_pos = self.pos

        # Look ahead to determine if this is a predicate or comparison
        # A predicate has the form: identifier(...)
        # A comparison has the form: expr op expr

        # Peek ahead to find '(' without consuming
        temp_pos = self.pos
        try:
            # Skip whitespace and find identifier
            while temp_pos < len(self.text) and self.text[temp_pos].isspace():
                temp_pos += 1

            # Read identifier
            match = re.match(r'[a-zA-Z_][a-zA-Z0-9_]*', self.text[temp_pos:])
            if match:
                temp_pos += len(match.group(0))
                # Skip whitespace after identifier
                while temp_pos < len(self.text) and self.text[temp_pos].isspace():
                    temp_pos += 1

                # Check if next char is '('
                if temp_pos < len(self.text) and self.text[temp_pos] == '(':
                    # It's a predicate
                    return self.parse_predicate()
        except:
            pass

        # Otherwise parse as comparison
        return self.parse_comparison()

    def parse_and_formulas(self) -> Formula:
        """Parse formulas connected by &&."""
        formulas = [self.parse_atomic()]

        while True:
            self.skip_whitespace()
            saved_pos = self.pos
            if self.consume('&&'):
                formulas.append(self.parse_atomic())
            else:
                self.pos = saved_pos
                break

        if len(formulas) == 1:
            return formulas[0]
        return AndConj(formulas)

    def parse_sep_formulas(self) -> Formula:
        """Parse formulas connected by * (separating conjunction)."""
        formulas = [self.parse_and_formulas()]

        while True:
            self.skip_whitespace()
            saved_pos = self.pos
            if self.consume('*'):
                # Make sure it's not part of a comment or other operator
                formulas.append(self.parse_and_formulas())
            else:
                self.pos = saved_pos
                break

        if len(formulas) == 1:
            return formulas[0]
        return SepConj(formulas)

    def parse_exists(self) -> Formula:
        """Parse existential quantifier."""
        if not self.consume('exists'):
            return self.parse_sep_formulas()

        # Parse variable list
        # Syntax: exists x, y, z, <body>
        # We need to distinguish variables from the body
        vars = []
        while True:
            self.skip_whitespace()
            saved_pos = self.pos

            var = self.parse_identifier()
            if var is None:
                raise ValueError(f"Expected variable after 'exists' at position {self.pos}")

            self.skip_whitespace()

            # Look ahead to see if this is part of the variable list or the start of the body
            # If we see a comma followed by another variable (no operator), it's a variable
            # If we see a comparison operator or end of variables, this is the start of body
            if self.consume(','):
                # We consumed a comma. Now peek ahead to see what follows
                peek_pos = self.pos
                self.skip_whitespace()

                # Try to see if next token is an identifier followed by operator or '('
                next_ident = self.parse_identifier()
                if next_ident is not None:
                    self.skip_whitespace()
                    next_char = self.current_char()
                    next_char2 = self.peek_char() if next_char else None

                    # Check if this looks like start of a formula
                    is_comparison = (next_char == '=' or next_char == '!' or
                                   next_char == '-')  # for ->
                    is_predicate = (next_char == '(')

                    if is_comparison or is_predicate:
                        # The identifier after comma is part of the body, not a variable
                        # So the current var is the last variable
                        # Reset to after the comma
                        vars.append(var)
                        self.pos = peek_pos
                        break
                    else:
                        # It's another variable in the list
                        # Reset and let the loop parse it properly
                        vars.append(var)
                        self.pos = peek_pos
                        continue
                else:
                    # No identifier after comma - this is odd, but treat current var as last
                    vars.append(var)
                    self.pos = peek_pos
                    break
            else:
                # No comma after this identifier - shouldn't happen in well-formed exists
                # But we'll be lenient and assume this is the last variable
                vars.append(var)
                break

        # Parse body
        body = self.parse_sep_formulas()

        return Exists(vars, body)

    def parse(self) -> Formula:
        """Parse the entire assertion."""
        self.skip_whitespace()
        formula = self.parse_exists()
        self.skip_whitespace()
        return formula


def parse_assertion(text: str) -> Formula:
    """Parse an assertion string into an AST.

    Args:
        text: The assertion string to parse

    Returns:
        The AST representation of the assertion

    Example:
        >>> ast = parse_assertion("t != 0 && lseg(x, y)")
        >>> print(ast)
    """
    parser = AssertionParser(text)
    return parser.parse()


def recover_expr(expr: Expr) -> str:
    """Recover an expression from AST to string.

    Args:
        expr: The expression AST node

    Returns:
        String representation of the expression
    """
    if isinstance(expr, int):
        return str(expr)
    elif isinstance(expr, Var):
        return expr.name
    elif isinstance(expr, FieldAccess):
        obj_str = recover_expr(expr.obj)
        return f"{obj_str} -> {expr.field}"
    elif isinstance(expr, BinOp):
        left_str = recover_expr(expr.left)
        right_str = recover_expr(expr.right)
        return f"{left_str} {expr.op} {right_str}"
    else:
        raise ValueError(f"Unknown expression type: {type(expr)}")


def recover_formula(formula: Formula, indent: int = 0) -> str:
    """Recover a formula from AST to string.

    Args:
        formula: The formula AST node
        indent: Indentation level for pretty printing

    Returns:
        String representation of the formula
    """
    if isinstance(formula, BinOp):
        return recover_expr(formula)
    elif isinstance(formula, Predicate):
        if formula.name == 'emp' and len(formula.args) == 0:
            return 'emp'
        args_str = ", ".join(recover_expr(arg) for arg in formula.args)
        return f"{formula.name}({args_str})"
    elif isinstance(formula, AndConj):
        parts = [recover_formula(f, indent) for f in formula.formulas]
        return " && ".join(parts)
    elif isinstance(formula, SepConj):
        parts = [recover_formula(f, indent) for f in formula.formulas]
        return " * ".join(parts)
    elif isinstance(formula, Exists):
        vars_str = " ".join(formula.vars)  # Use space instead of comma
        body_str = recover_formula(formula.body, indent)
        return f"exists {vars_str},\n{' ' * (indent + 12)}{body_str}"
    else:
        raise ValueError(f"Unknown formula type: {type(formula)}")


def recover_assertion(ast: Formula) -> str:
    """Recover an assertion string from AST.

    Args:
        ast: The AST representation of the assertion

    Returns:
        The assertion string

    Example:
        >>> text = "t != 0 && lseg(x, y)"
        >>> ast = parse_assertion(text)
        >>> recovered = recover_assertion(ast)
        >>> print(recovered)
    """
    return recover_formula(ast)
