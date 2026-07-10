"""Extract data witness variables from a translated annotation.

The translator desugars ``EXPR -> FIELD == VAR`` clauses into
``store(&(EXPR->FIELD), <c-type>, VAR)`` (or leaves them alone when the type
cannot be resolved); any explicit ``store(...)`` calls written by the user
flow through verbatim.  This module walks the translated text, parses each
``store(addr, T, var)`` triple, and decides whether ``var`` contributes to
the abstract-program carrier:

  * scalar / boolean ``T`` → carrier element with Coq type ``Z`` (or
    ``bool``).
  * pointer ``T`` → not carried (the address is preserved by the verbatim
    splice but no carrier variable is introduced).
"""

import re
from typing import List, Optional, Tuple

from .c_types import coq_type_of
from .translator import parse_store_predicates


def extract_data_witnesses(
    translated_inv: str,
    pre_existing_vars: List[str],
) -> List[str]:
    """Return pre-existing existential vars that become abstract-state carriers.

    A var is a carrier when it appears as the third argument of a
    ``store(addr, T, var)`` predicate in *translated_inv* and ``T`` is a
    scalar / boolean C type.  Pointer-typed stores are skipped.

    Args:
        translated_inv: The translated annotation text.
        pre_existing_vars: Existential variable names from the original
            annotation (before predicate translation).  Only these are
            eligible.

    Returns:
        Matched variable names in **existential-binder order** (the order they
        appear in ``pre_existing_vars``), no duplicates.  This must match the
        order the generated lib's carrier uses for its scalar witnesses
        (``segcodegen.witness.refine`` reads the same ``exists`` binder), so that
        the ``M_loop(...)`` call emitted into the annotation binds each carrier
        slot to the program variable the lib body expects.  Ordering by
        store-appearance instead silently swaps two scalar witnesses (e.g. a
        loop carrying both a running sum ``s`` and a per-node value ``v``) when
        they occur in opposite relative order in the SEP vs. the ``exists`` list.
    """
    if not pre_existing_vars:
        return []

    scalar = {var for _addr, c_type, var in parse_store_predicates(translated_inv)
              if coq_type_of(c_type)}
    seen = set()
    result: List[str] = []
    for var in pre_existing_vars:
        if var in scalar and var not in seen:
            seen.add(var)
            result.append(var)
    return result


def extract_data_witnesses_typed(
    translated_inv: str,
    pre_existing_vars: List[str],
) -> List[Tuple[str, str]]:
    """Same as :func:`extract_data_witnesses` but also returns the Coq type
    associated with each carrier (``Z`` for integral, ``bool`` for ``_Bool``).
    Witnesses are returned in **existential-binder order** (see
    :func:`extract_data_witnesses`).
    """
    if not pre_existing_vars:
        return []

    coq_of: dict = {}
    for _addr, c_type, var in parse_store_predicates(translated_inv):
        if var in coq_of:
            continue
        coq_t = coq_type_of(c_type)
        if coq_t:
            coq_of[var] = coq_t
    seen = set()
    result: List[Tuple[str, str]] = []
    for var in pre_existing_vars:
        if var in coq_of and var not in seen:
            seen.add(var)
            result.append((var, coq_of[var]))
    return result


def extract_pre_existing_vars(original_content: str) -> List[str]:
    """Extract existential variable names from the original annotation text.

    Parses the leading ``exists v1 v2 ...,`` clause (if any) and returns the
    variable names.  These are the vars the user wrote, before predicate
    translation added generated ones.
    """
    m = re.match(r'^\s*exists\s+(.*?),', original_content, re.DOTALL)
    if not m:
        return []
    return m.group(1).split()
