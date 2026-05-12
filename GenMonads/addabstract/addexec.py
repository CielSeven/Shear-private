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


def add_safeexec_predicate(
    translated_inv: str,
    generated_vars: List[str],
    program_loop: str,
    program_loop_end: str,
    precondition: str = "ATrue",
    postcondition: str = "X"
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

    # Reconstruct the full assertion
    if exists_vars:
        result = f"exists {exists_vars}, {combined_body}"
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

def add_with_parameter(
    funcspec: dict,
    parameter: str = "X"
) -> dict:
    """
    Add a parameter to the With clause of a function specification.

    Args:
        funcspec: Translated function specification dictionary with 'with', 'require', 'ensure' keys
        parameter: Parameter to add (default: "X")

    Returns:
        Updated function specification dictionary

    Example:
        Input:  {'with': None, 'require': {'translated': 'sll(x, ?l1)'}, ...}
        Output: {'with': {'original': None, 'translated': 'X'}, ...}

        Input:  {'with': {'original': 'l'}, 'require': {...}, ...}
        Output: {'with': {'original': 'l', 'translated': 'l X'}, ...}
    """
    result = {}

    # Handle With clause
    if funcspec.get('with') is None:
        # No With clause - create one with just the parameter
        # original stays None since there was no original With clause
        result['with'] = {'original': None, 'translated': parameter}
    else:
        # Has With clause - append parameter
        with_clause = funcspec['with']
        if isinstance(with_clause, dict):
            original = with_clause.get('original', '')
            result['with'] = {
                'original': original,
                'translated': f"{original} {parameter}".strip() if original else parameter
            }
        else:
            # String format
            result['with'] = {
                'original': with_clause,
                'translated': f"{with_clause} {parameter}".strip()
            }

    # Copy require and ensure
    result['require'] = funcspec.get('require')
    result['ensure'] = funcspec.get('ensure')

    # Copy variables if present at top level
    if 'variables' in funcspec:
        result['variables'] = funcspec['variables']

    return result


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


def add_safeexec_to_require(
    translated_require: str,
    generated_vars: List[str],
    program: str,
    precondition: str = "ATrue",
    postcondition: str = "X"
) -> str:
    """
    Add safeExec predicate to a translated Require assertion.

    Strips ? prefix from variables, wraps with exists quantifier.

    Args:
        translated_require: Translated require assertion, e.g., "sll(x, ?l1)"
        generated_vars: List of generated variables, e.g., ['?l1']
        program: Abstract program name for the function, e.g., "sll_copy_M"
        precondition: Precondition for safeExec (default: "ATrue")
        postcondition: Postcondition for safeExec (default: "X")

    Returns:
        Require assertion with exists and safeExec added, e.g.,
        "exists l1, safeExec(ATrue, sll_copy_M(l1), X) && sll(x, l1)"

    Example:
        Input:  "sll(x, ?l1)", ['?l1'], "sll_copy_M"
        Output: "exists l1, safeExec(ATrue, sll_copy_M(l1), X) && sll(x, l1)"
    """
    # Strip ? prefix from variables
    clean_vars = [v.lstrip('?') for v in generated_vars]

    # Build the program call with clean variables
    if clean_vars:
        var_args = ', '.join(clean_vars)
        program_call = f"{program}({var_args})"
    else:
        program_call = program

    # Build the safeExec predicate
    safeexec_pred = f"safeExec({precondition}, {program_call}, {postcondition})"

    # Replace ?-prefixed vars in the assertion body
    body = translated_require
    for var in generated_vars:
        if var.startswith('?'):
            body = body.replace(var, var[1:])

    # Combine with the original assertion
    combined = f"{safeexec_pred} && {body}"

    # Wrap with exists if there are variables
    if clean_vars:
        exists_vars = ' '.join(clean_vars)
        result = f"exists {exists_vars}, {combined}"
    else:
        result = combined

    return result


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


def add_safeexec_to_ensure(
    translated_ensure: str,
    generated_vars: List[str],
    precondition: str = "ATrue",
    postcondition: str = "X",
    return_type: str = "",
    data_witnesses: Optional[List[str]] = None,
) -> str:
    """
    Add safeExec predicate to a translated Ensure assertion.

    Strips ? prefix from variables, wraps with exists quantifier.  If the
    function has a non-void *return_type* and the Ensure body does not
    mention ``__return``, a fresh witness variable ``r`` is synthesized so the
    abstract program return value is observable: it is appended to the
    existentials, threaded into the ``return(...)`` call, and bound by
    ``__return == r`` in the body.

    Pre-existing existentials that name data-field witnesses (e.g.
    ``exists d, __return -> data == d``) are *lifted out* of the body into
    the outer ``exists`` list and threaded into ``return(maketuple(…))``;
    the now-redundant inner ``exists`` clause is stripped from the body.

    Args:
        translated_ensure: Translated ensure assertion, e.g., "sll(__return, ?l2) * sll(x, ?l3)"
        generated_vars: List of generated variables, e.g., ['?l2', '?l3']
        precondition: Precondition for safeExec (default: "ATrue")
        postcondition: Postcondition for safeExec (default: "X")
        return_type: C function return type (e.g. ``"long"``, ``"void"``,
            ``"struct list *"``).  Empty string or ``"void"`` is treated as
            void.
        data_witnesses: Names of pre-existing existentials that bind data-field
            witnesses (e.g. ``['d']`` for ``exists d, ... __return -> data == d``).
            These get lifted into the outer ``exists`` and the abstract return.

    Returns:
        Ensure assertion with exists and safeExec added, e.g.,
        "exists l2 l3, safeExec(ATrue, return(maketuple(l2, l3)), X) && sll(__return, l2) * sll(x, l3)"

    Example (no __return predicate, non-void return type):
        Input:  "sll(x@pre, ?l2)", ['?l2'], return_type="long"
        Output: "exists l2 r, safeExec(ATrue, return(maketuple(l2, r)), X) && __return == r && sll(x@pre, l2)"
    """
    data_witnesses = list(data_witnesses or [])

    # Strip ? prefix from variables.
    clean_vars = [v.lstrip('?') for v in generated_vars]

    # Replace ?-prefixed vars in the assertion body first so we can scan it
    # for the presence of __return cleanly.
    body = translated_ensure
    for var in generated_vars:
        if var.startswith('?'):
            body = body.replace(var, var[1:])

    # Strip any leading ``exists <vars>,`` clause from the body so the data
    # witnesses can be re-bound by the outer wrapper.  Names not promoted to
    # the outer exists (e.g. pointer existentials we don't track) are
    # preserved in a residual ``exists`` clause kept inside the body.
    body, leftover_exists = _strip_leading_exists(body, data_witnesses)
    if leftover_exists:
        body = f"exists {' '.join(leftover_exists)}, {body}"

    # Decide whether we need a synthetic return witness for __return.
    need_witness = (
        not _is_void_return_type(return_type)
        and "__return" not in body
    )
    witness = "r" if need_witness else None
    return_vars = clean_vars + data_witnesses + ([witness] if witness else [])

    # Build the return call.
    if len(return_vars) > 1:
        var_args = ', '.join(return_vars)
        return_call = f"return(maketuple({var_args}))"
    elif len(return_vars) == 1:
        return_call = f"return({return_vars[0]})"
    else:
        # No Ensure-only variables AND no return witness ⇒ unit return type.
        return_call = "return(tt)"

    safeexec_pred = f"safeExec({precondition}, {return_call}, {postcondition})"

    if witness:
        body = f"__return == {witness} && {body}"

    combined = f"{safeexec_pred} && {body}"

    if return_vars:
        exists_vars = ' '.join(return_vars)
        return f"exists {exists_vars}, {combined}"
    return combined


def _strip_leading_exists(body: str, promote_vars: List[str]) -> tuple:
    """Strip a leading ``exists v1 v2 ..., `` clause from *body*.

    The variables in *promote_vars* are removed from the binder list (they
    are being lifted to an outer scope).  Any remaining binders are returned
    in *leftover_exists* so the caller can re-wrap them around the body.
    """
    m = re.match(r"\s*exists\s+([^,]+?)\s*,\s*", body, re.DOTALL)
    if not m:
        return body, []
    binders = m.group(1).split()
    leftover = [b for b in binders if b not in promote_vars]
    rest = body[m.end():]
    return rest, leftover


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
    # First add the With parameter
    result = add_with_parameter(funcspec, parameter)

    # Process Require — produces exists-wrapped result, then lift exists into With
    require_clean_vars = []
    if result.get('require') and result['require'].get('translated'):
        require = result['require'].copy()
        translated = require['translated']

        # Extract variables from the translated assertion
        require_vars = extract_variables_from_assertion(translated)
        require_clean_vars = [v.lstrip('?') for v in require_vars]

        require['with_safeexec'] = add_safeexec_to_require(
            translated,
            require_vars,
            program,
            precondition,
            parameter  # postcondition is the parameter (X)
        )

        # Strip the exists wrapper — those vars go into With instead
        if require_clean_vars:
            exists_prefix = f"exists {' '.join(require_clean_vars)}, "
            if require['with_safeexec'].startswith(exists_prefix):
                require['with_safeexec'] = require['with_safeexec'][len(exists_prefix):]

        result['require'] = require

    # Lift Require's existential vars into the With clause
    if require_clean_vars and result.get('with'):
        current_with = result['with']['translated']
        result['with']['translated'] = f"{current_with} {' '.join(require_clean_vars)}"

    # Process Ensure — keeps exists wrapper
    if result.get('ensure') and result['ensure'].get('translated'):
        ensure = result['ensure'].copy()
        translated = ensure['translated']

        # Extract variables from the translated assertion
        ensure_vars = extract_variables_from_assertion(translated)
        ensure_data_witnesses = ensure.get('data_witnesses', [])

        ensure['with_safeexec'] = add_safeexec_to_ensure(
            translated,
            ensure_vars,
            precondition,
            parameter,  # postcondition is the parameter (X)
            return_type=return_type,
            data_witnesses=ensure_data_witnesses,
        )
        result['ensure'] = ensure

    return result
