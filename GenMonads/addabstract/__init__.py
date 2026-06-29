# addabstract module
# Add safeExec abstract predicate to translated assertions
from .addexec import (
    # Loop invariant processing
    add_safeexec_predicate,
    add_safeexec_to_assertion,
    # Function specification processing
    process_funcspec_with_safeexec,
    extract_variables_from_assertion,
)

__all__ = [
    'add_safeexec_predicate',
    'add_safeexec_to_assertion',
    'process_funcspec_with_safeexec',
    'extract_variables_from_assertion',
]
