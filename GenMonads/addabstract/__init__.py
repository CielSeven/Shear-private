# addabstract module
# Add safeExec abstract predicate to translated assertions
from .addexec import (
    # Loop invariant processing
    add_safeexec_predicate,
    add_safeexec_to_assertion,
    # Function specification processing
    add_with_parameter,
    add_safeexec_to_require,
    add_safeexec_to_ensure,
    process_funcspec_with_safeexec,
    extract_variables_from_assertion,
)

__all__ = [
    'add_safeexec_predicate',
    'add_safeexec_to_assertion',
    'add_with_parameter',
    'add_safeexec_to_require',
    'add_safeexec_to_ensure',
    'process_funcspec_with_safeexec',
    'extract_variables_from_assertion',
]
