# guardgen/cond/lexer.py
import re
from dataclasses import dataclass

_TOKEN_REGEX = re.compile(
    r"""(?P<WS>\s+)|
        (?P<AND>&&)|
        (?P<OR>\|\|)|
        (?P<NE1>!=)|
        (?P<NE2><>)|
        (?P<NOT>!)|
        (?P<LPAREN>\()|
        (?P<RPAREN>\))|
        (?P<EQ>==)|
        (?P<ARROW>->)|
        (?P<ID>[A-Za-z_][A-Za-z0-9_]*)|
        (?P<NUM>0)
    """, re.VERBOSE
)

@dataclass
class Tok:
    kind: str
    text: str

def lex_cond(s: str) -> list[Tok]:
    toks = []
    pos = 0
    while pos < len(s):
        m = _TOKEN_REGEX.match(s, pos)
        if not m:
            raise ValueError(f"Unexpected char at {pos}: {s[pos:]}")
        if m.lastgroup != "WS":
            toks.append(Tok(m.lastgroup, m.group(0)))
        pos = m.end()
    return toks
