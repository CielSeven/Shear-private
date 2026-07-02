"""
Add safeExec abstract predicate to translated assertions.

This module provides functions to:
1. Add parameters to function specifications (With clause)
2. Add safeExec predicate to Require assertions
3. Add safeExec predicate to Ensure assertions
4. Add safeExec predicate to loop invariants (Inv)
"""

import re
from typing import List, Optional, Tuple

try:
    from GenMonads.transshape.c_types import coq_type_of
except Exception:  # pragma: no cover - allow package fallback for tooling
    from ..transshape.c_types import coq_type_of  # type: ignore


_RETURN_EQ_RE = re.compile(r'__return\s*==\s*([A-Za-z_][A-Za-z0-9_]*)')


def extract_return_value_witnesses(
    funcspec: dict, return_type: str
) -> List[Tuple[str, str]]:
    """Vars bound by the source Ensure's leading ``exists`` that the spec
    equates with ``__return``.  When the C function returns a non-pointer
    scalar, these get lifted into the abstract program's return tuple
    (e.g. ``Ensure exists v, __return == v && ...`` → ``v : Z``).

    Returns an ordered list of ``(var, coq_type)``.  Pointer / void
    returns yield ``[]`` — pointer payloads aren't carried through the
    abstract program today.
    """
    if not funcspec or not funcspec.get('ensure'):
        return []
    coq_t = coq_type_of(return_type or '')
    if not coq_t:
        return []
    ensure = funcspec['ensure']
    original = ensure.get('original') or ''
    translated = ensure.get('translated') or ''
    if not original or not translated:
        return []
    m = re.match(r'^\s*exists\s+(.*?),', original, re.DOTALL)
    if not m:
        return []
    bound = m.group(1).split()
    if not bound:
        return []
    matches = set(_RETURN_EQ_RE.findall(translated))
    seen = set()
    result: List[Tuple[str, str]] = []
    for v in bound:
        if v in matches and v not in seen:
            seen.add(v)
            result.append((v, coq_t))
    return result


def add_safeexec_predicate(
    translated_inv: str,
    generated_vars: List[str],
    program_loop: str,
    program_loop_end: str,
    precondition: str = "ATrue",
    postcondition: str = "X",
    extra_exists_vars: Optional[List[str]] = None,
) -> str:
    """
    Add safeExec predicate to a translated loop invariant.

    Args:
        translated_inv: Translated loop invariant, e.g.,
            "exists l1 l2 l3, t != 0 && sllseg(x@pre,p, l1) * sll(p, l2) * sllseg(y, t, l3)"
        generated_vars: List of generated variables, e.g., ['l1', 'l2', 'l3']
        program_loop: Abstract program name for the loop, e.g., "sll_copy_M_loop"
        program_loop_end: Abstract program name for loop end, e.g., "sll_copy_M_loop_end"
        precondition: Precondition for safeExec (default: "ATrue")
        postcondition: Postcondition for safeExec (default: "X")

    Returns:
        Full assertion with safeExec predicate added, e.g.,
        "exists l1 l2 l3, safeExec(ATrue, bind(sll_copy_M_loop(l1,l2,l3), sll_copy_M_loop_end), X) &&
         t != 0 && sllseg(x@pre,p, l1) * sll(p, l2) * sllseg(y, t, l3)"
    """
    # Parse the translated invariant to extract exists clause and body
    exists_match = re.match(r'^exists\s+(.*?),\s*(.+)$', translated_inv.strip(), re.DOTALL)

    if exists_match:
        # Has exists clause
        exists_vars = exists_match.group(1).strip()
        inv_body = exists_match.group(2).strip()
    else:
        # No exists clause
        exists_vars = None
        inv_body = translated_inv.strip()

    # Build the safeExec predicate
    if generated_vars:
        # Format variables as arguments: l1, l2, l3 -> l1,l2,l3
        # Remove '?' prefix if present in variables
        clean_vars = [v.lstrip('?') for v in generated_vars]
        var_args = ','.join(clean_vars)
        program_call = f"{program_loop}({var_args})"
    else:
        # No variables - no parentheses
        program_call = program_loop

    # Build the bind expression
    bind_expr = f"bind({program_call}, {program_loop_end})"

    # Build the safeExec predicate
    safeexec_pred = f"safeExec({precondition}, {bind_expr}, {postcondition})"

    # Combine safeExec with the invariant body using &&
    combined_body = f"{safeexec_pred} && {inv_body}"

    # Reconstruct the full assertion.  Any caller-supplied
    # ``extra_exists_vars`` (e.g. ``outer_state`` for a nested-loop Inv
    # that binds its continuation with ``fun r => M_loop_k_tail r
    # outer_state``) are prepended to the existential list so the
    # variable is in scope where the bind expression references it.
    extras = list(extra_exists_vars or [])
    if exists_vars:
        merged = " ".join(extras + [exists_vars]) if extras else exists_vars
        result = f"exists {merged}, {combined_body}"
    elif extras:
        result = f"exists {' '.join(extras)}, {combined_body}"
    else:
        result = combined_body

    return result


def add_safeexec_to_assertion(
    assertion_dict: dict,
    program_loop: str,
    program_loop_end: str,
    precondition: str = "ATrue",
    postcondition: str = "X"
) -> dict:
    """
    Add safeExec predicate to an assertion dictionary (from transshape pipeline).

    Args:
        assertion_dict: Dictionary with 'translated' and 'variables' keys
        program_loop: Abstract program name for the loop
        program_loop_end: Abstract program name for loop end
        precondition: Precondition for safeExec (default: "ATrue")
        postcondition: Postcondition for safeExec (default: "X")

    Returns:
        Updated dictionary with 'with_safeexec' field added
    """
    result = assertion_dict.copy()

    if 'translated' in assertion_dict and 'variables' in assertion_dict:
        translated_inv = assertion_dict['translated']
        generated_vars = assertion_dict['variables']

        with_safeexec = add_safeexec_predicate(
            translated_inv,
            generated_vars,
            program_loop,
            program_loop_end,
            precondition,
            postcondition
        )

        result['with_safeexec'] = with_safeexec

    return result


# ============================================================================
# Function Specification Processing
# ============================================================================


def extract_variables_from_assertion(assertion: str) -> List[str]:
    """
    Extract ?l1, ?l2, etc. variables from a translated assertion.

    Args:
        assertion: Translated assertion string, e.g., "sll(x, ?l1) * sll(y, ?l2)"

    Returns:
        List of variable names found, e.g., ['?l1', '?l2']
    """
    # Find all ?l followed by digits
    pattern = r'\?l\d+'
    matches = re.findall(pattern, assertion)
    # Remove duplicates while preserving order
    seen = set()
    result = []
    for m in matches:
        if m not in seen:
            seen.add(m)
            result.append(m)
    return result


def canonical_funcspec(funcspec: dict, return_type: str = '') -> dict:
    """One-stop shape→data decomposition shared by ``--data-only`` and rel.c
    paths.  Computes everything both layers need without doing any safeExec
    work — that's strictly a post-processing concern on top of this canonical
    view.

    Returns a dict with:
    - ``source_with``: the source ``With`` clause (may be empty)
    - ``require_promoted_vars``: generated vars in Require (clean, no ``?``)
        — promoted into the With clause in both data and rel forms
    - ``require_body``: Require body with ``?`` stripped
    - ``ensure_clean_vars``: all generated vars in Ensure (clean)
    - ``ensure_only_vars``: Ensure-generated vars not also in Require —
        bound by the outer ``exists`` in the data form, and by the safeExec
        wrapper's ``exists`` in the rel form.
    - ``ensure_body``: Ensure body with ``?`` stripped *and* with any
        leading source ``exists`` peeled off — callers re-wrap with their
        own merged outer ``exists`` so we never emit nested ``exists``.
    - ``ensure_leftover_source_vars``: source-``exists``-bound vars that
        aren't lifted as data or return witnesses.  Callers fold these into
        the outer ``exists`` alongside generated/lifted vars.
    - ``ensure_data_witnesses``: pre-existing existentials bound by source
        ``exists`` that name data-field witnesses (e.g. ``d`` in
        ``exists d, __return -> data == d``).  Carried through so the rel
        layer can lift them into the abstract return value.
    - ``ensure_return_witnesses``: pre-existing existentials equated with
        ``__return`` (e.g. ``v`` in ``exists v, __return == v && ...``)
        when the C return type is a non-pointer scalar.  Lifted into the
        abstract return tuple as Z-typed payload.
    """
    source_with = ""
    with_clause = funcspec.get('with')
    if with_clause:
        if isinstance(with_clause, dict):
            source_with = (with_clause.get('original') or '').strip()
        else:
            source_with = str(with_clause).strip()

    require_promoted_vars: List[str] = []
    require_body = ""
    if funcspec.get('require') and funcspec['require'].get('translated'):
        translated = funcspec['require']['translated']
        require_vars = extract_variables_from_assertion(translated)
        require_promoted_vars = [v.lstrip('?') for v in require_vars]
        body = translated
        for v in require_vars:
            if v.startswith('?'):
                body = body.replace(v, v[1:])
        require_body = body

    ensure_clean_vars: List[str] = []
    ensure_only_vars: List[str] = []
    ensure_body = ""
    ensure_data_witnesses: List[str] = []
    ensure_return_witnesses: List[str] = []
    ensure_leftover_source_vars: List[str] = []
    if funcspec.get('ensure') and funcspec['ensure'].get('translated'):
        translated = funcspec['ensure']['translated']
        ensure_vars = extract_variables_from_assertion(translated)
        ensure_clean_vars = [v.lstrip('?') for v in ensure_vars]
        ensure_only_vars = [
            v for v in ensure_clean_vars if v not in require_promoted_vars
        ]
        body = translated
        for v in ensure_vars:
            if v.startswith('?'):
                body = body.replace(v, v[1:])
        ensure_data_witnesses = list(
            funcspec['ensure'].get('data_witnesses', []) or []
        )
        ensure_return_witnesses = [
            v for v, _t in extract_return_value_witnesses(funcspec, return_type)
        ]

        # Peel off the leading source ``exists`` and split its binders into
        # lifted (data/return witnesses) vs. leftover.  ``ensure_body`` is
        # always returned stripped so callers don't have to redo this dance
        # and accidentally emit nested ``exists`` clauses.
        leading = re.match(r'^\s*exists\s+(.+?),\s*(.+)$', body, re.DOTALL)
        if leading:
            inner_vars = leading.group(1).split()
            inner_body = leading.group(2)
            lifted = set(ensure_data_witnesses) | set(ensure_return_witnesses)
            ensure_leftover_source_vars = [v for v in inner_vars if v not in lifted]
            ensure_body = inner_body
        else:
            ensure_body = body

    return {
        'source_with': source_with,
        'require_promoted_vars': require_promoted_vars,
        'require_body': require_body,
        'ensure_clean_vars': ensure_clean_vars,
        'ensure_only_vars': ensure_only_vars,
        'ensure_body': ensure_body,
        'ensure_data_witnesses': ensure_data_witnesses,
        'ensure_return_witnesses': ensure_return_witnesses,
        'ensure_leftover_source_vars': ensure_leftover_source_vars,
    }


def _is_void_return_type(return_type: str) -> bool:
    """Heuristic: treat empty / 'void' (possibly with pointer stars) as void.

    A pointer-to-void (``void *``) is *not* a void return type — the function
    still produces a value the abstract program must witness.
    """
    rt = (return_type or "").strip()
    if not rt:
        return True
    if "*" in rt:
        return False
    return rt == "void"


def process_funcspec_with_safeexec(
    funcspec: dict,
    program: str,
    parameter: str = "X",
    precondition: str = "ATrue",
    return_type: str = "",
) -> dict:
    """
    Process a complete function specification: add With parameter and safeExec to Require/Ensure.

    Args:
        funcspec: Translated function specification dictionary
        program: Abstract program name for the function, e.g., "sll_copy_M"
        parameter: Parameter to add to With clause (default: "X")
        precondition: Precondition for safeExec (default: "ATrue")

    Returns:
        Updated function specification with:
        - With clause including the parameter
        - Require with safeExec(ATrue, program(?l1, ...), X)
        - Ensure with safeExec(ATrue, return(?l2, ...), X)

    Example:
        Input funcspec:
            {'require': {'translated': 'sll(x, ?l1)'},
             'ensure': {'translated': 'sll(__return, ?l2) * sll(x, ?l3)'}}

        Output:
            {'with': {'original': None, 'translated': 'X l1'},
             'require': {'with_safeexec': 'safeExec(ATrue, sll_copy_M(l1), X) && sll(x, l1)', ...},
             'ensure': {'with_safeexec': 'exists l2 l3, safeExec(ATrue, return(l2, l3), X) && ...', ...}}
    """
    canon = canonical_funcspec(funcspec, return_type=return_type)

    with_parts: List[str] = []
    if canon['source_with']:
        with_parts.append(canon['source_with'])
    with_parts.append(parameter)
    if canon['require_promoted_vars']:
        with_parts.append(' '.join(canon['require_promoted_vars']))

    source_with_raw = funcspec.get('with')
    if isinstance(source_with_raw, dict):
        original_with = source_with_raw.get('original') if source_with_raw.get('original') is not None else None
    else:
        original_with = source_with_raw

    result: dict = {
        'with': {
            'original': original_with,
            'translated': ' '.join(with_parts),
        },
    }

    if canon['require_body']:
        if canon['require_promoted_vars']:
            program_call = f"{program}({', '.join(canon['require_promoted_vars'])})"
        else:
            program_call = program
        safeexec = f"safeExec({precondition}, {program_call}, {parameter})"
        rel_require_body = f"{safeexec} && {canon['require_body']}"
        require = (funcspec.get('require') or {}).copy()
        require['with_safeexec'] = rel_require_body
        result['require'] = require
    elif funcspec.get('require'):
        # Caller handed us an already-processed Require (no ``translated``,
        # only ``with_safeexec``).  Pass it through unchanged so downstream
        # rendering can still pick up the pre-baked safeExec form.
        result['require'] = (funcspec['require'] or {}).copy()

    if canon['ensure_body']:
        body = canon['ensure_body']
        data_witnesses = canon['ensure_data_witnesses']
        return_witnesses = canon['ensure_return_witnesses']
        leftover_source_vars = canon['ensure_leftover_source_vars']

        ensure_translated_raw = (funcspec.get('ensure') or {}).get('translated', '') or ''
        # Only synthesize an ``r`` witness when the C function returns a
        # value that the source spec didn't already bind via
        # ``__return == <var>`` — those explicit binders flow through
        # ``return_witnesses`` already.
        need_witness = (
            not _is_void_return_type(return_type)
            and "__return" not in ensure_translated_raw
            and not return_witnesses
        )
        witness = "r" if need_witness else None
        return_vars = (
            list(canon['ensure_only_vars'])
            + list(data_witnesses)
            + list(return_witnesses)
            + ([witness] if witness else [])
        )

        if len(return_vars) > 1:
            return_call = f"return(maketuple({', '.join(return_vars)}))"
        elif len(return_vars) == 1:
            return_call = f"return({return_vars[0]})"
        else:
            return_call = "return(tt)"

        safeexec = f"safeExec({precondition}, {return_call}, {parameter})"

        if witness:
            body = f"__return == {witness} && {body}"

        rel_ensure_body = f"{safeexec} && {body}"
        # Outer ``exists`` merges leftover source binders, lifted witnesses
        # and generated list vars into a single clause — never nested.
        # Source binders come first to match the order users wrote them in.
        outer_exists = (
            list(leftover_source_vars)
            + list(data_witnesses)
            + list(return_witnesses)
            + list(canon['ensure_only_vars'])
            + ([witness] if witness else [])
        )
        if outer_exists:
            rel_ensure_body = f"exists {' '.join(outer_exists)}, {rel_ensure_body}"

        ensure = (funcspec.get('ensure') or {}).copy()
        ensure['with_safeexec'] = rel_ensure_body
        result['ensure'] = ensure
    elif funcspec.get('ensure'):
        # As for Require above — preserve a caller-provided pre-baked Ensure.
        result['ensure'] = (funcspec['ensure'] or {}).copy()

    return result
