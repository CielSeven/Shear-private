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

    Args:
        translated_require: Translated require assertion, e.g., "sll(x, ?l1)"
        generated_vars: List of generated variables, e.g., ['?l1']
        program: Abstract program name for the function, e.g., "sll_copy_M"
        precondition: Precondition for safeExec (default: "ATrue")
        postcondition: Postcondition for safeExec (default: "X")

    Returns:
        Require assertion with safeExec added, e.g.,
        "safeExec(ATrue, sll_copy_M(?l1), X) && sll(x, ?l1)"

    Example:
        Input:  "sll(x, ?l1)", ['?l1'], "sll_copy_M"
        Output: "safeExec(ATrue, sll_copy_M(?l1), X) && sll(x, ?l1)"
    """
    # Build the program call with variables
    if generated_vars:
        # Keep the ? prefix for require variables
        var_args = ', '.join(generated_vars)
        program_call = f"{program}({var_args})"
    else:
        # No variables - no parentheses
        program_call = program

    # Build the safeExec predicate
    safeexec_pred = f"safeExec({precondition}, {program_call}, {postcondition})"

    # Combine with the original assertion
    result = f"{safeexec_pred} && {translated_require}"

    return result


def add_safeexec_to_ensure(
    translated_ensure: str,
    generated_vars: List[str],
    precondition: str = "ATrue",
    postcondition: str = "X"
) -> str:
    """
    Add safeExec predicate to a translated Ensure assertion.

    Args:
        translated_ensure: Translated ensure assertion, e.g., "sll(__return, ?l2) * sll(x, ?l3)"
        generated_vars: List of generated variables, e.g., ['?l2', '?l3']
        precondition: Precondition for safeExec (default: "ATrue")
        postcondition: Postcondition for safeExec (default: "X")

    Returns:
        Ensure assertion with safeExec added, e.g.,
        "safeExec(ATrue, return(?l2, ?l3), X) && sll(__return, ?l2) * sll(x, ?l3)"

    Example:
        Input:  "sll(__return, ?l2) * sll(x, ?l3)", ['?l2', '?l3']
        Output: "safeExec(ATrue, return(?l2, ?l3), X) && sll(__return, ?l2) * sll(x, ?l3)"
    """
    # Build the return call with variables
    if generated_vars:
        # Keep the ? prefix for ensure variables
        var_args = ', '.join(generated_vars)
        return_call = f"return({var_args})"
    else:
        # No variables - no parentheses
        return_call = "return"

    # Build the safeExec predicate
    safeexec_pred = f"safeExec({precondition}, {return_call}, {postcondition})"

    # Combine with the original assertion
    result = f"{safeexec_pred} && {translated_ensure}"

    return result


def process_funcspec_with_safeexec(
    funcspec: dict,
    program: str,
    parameter: str = "X",
    precondition: str = "ATrue"
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
            {'with': {'original': None, 'translated': 'X'},
             'require': {'with_safeexec': 'safeExec(ATrue, sll_copy_M(?l1), X) && sll(x, ?l1)', ...},
             'ensure': {'with_safeexec': 'safeExec(ATrue, return(?l2, ?l3), X) && sll(__return, ?l2) * sll(x, ?l3)', ...}}
    """
    # First add the With parameter
    result = add_with_parameter(funcspec, parameter)

    # Process Require
    if result.get('require') and result['require'].get('translated'):
        require = result['require'].copy()
        translated = require['translated']

        # Extract variables from the translated assertion
        require_vars = extract_variables_from_assertion(translated)

        require['with_safeexec'] = add_safeexec_to_require(
            translated,
            require_vars,
            program,
            precondition,
            parameter  # postcondition is the parameter (X)
        )
        result['require'] = require

    # Process Ensure
    if result.get('ensure') and result['ensure'].get('translated'):
        ensure = result['ensure'].copy()
        translated = ensure['translated']

        # Extract variables from the translated assertion
        ensure_vars = extract_variables_from_assertion(translated)

        ensure['with_safeexec'] = add_safeexec_to_ensure(
            translated,
            ensure_vars,
            precondition,
            parameter  # postcondition is the parameter (X)
        )
        result['ensure'] = ensure

    return result
