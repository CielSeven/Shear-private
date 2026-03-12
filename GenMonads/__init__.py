"""
GenMonads: Translate C programs with shape assertions to data predicates.

Usage as a library:

    from GenMonads import translate_c_file, translate_directory

    # Single file
    translate_c_file("input.c", "output_rel.c")

    # Directory
    results = translate_directory("input_dir/", "output_dir/")
"""

from GenMonads.translate_c_file import translate_c_file, translate_directory
from GenMonads.guardgen import gen_coq_guard

__all__ = ["translate_c_file", "translate_directory", "gen_coq_guard"]
