"""
Test header mapping functionality.
"""

from GenMonads.header_mapping import (
    get_header_mappings,
    add_header_mapping,
    remove_header_mapping,
    clear_header_mappings,
    reset_header_mappings,
    translate_headers,
)


def setup_function():
    """Reset mappings before each test."""
    reset_header_mappings()


def test_default_mappings():
    mappings = get_header_mappings()
    assert 'sll_shape_def.h' in mappings
    assert mappings['sll_shape_def.h'] == 'sll_def.h'
    assert 'dll_shape_def.h' in mappings
    assert mappings['dll_shape_def.h'] == 'dll_def.h'


def test_add_mapping():
    add_header_mapping('tree_shape_def.h', 'tree_def.h')
    mappings = get_header_mappings()
    assert 'tree_shape_def.h' in mappings
    assert mappings['tree_shape_def.h'] == 'tree_def.h'


def test_remove_mapping():
    assert remove_header_mapping('sll_shape_def.h') == True
    mappings = get_header_mappings()
    assert 'sll_shape_def.h' not in mappings
    assert remove_header_mapping('nonexistent.h') == False


def test_clear_mappings():
    clear_header_mappings()
    assert len(get_header_mappings()) == 0


def test_reset_mappings():
    clear_header_mappings()
    add_header_mapping('custom.h', 'custom_new.h')
    reset_header_mappings()
    mappings = get_header_mappings()
    assert 'custom.h' not in mappings
    assert 'sll_shape_def.h' in mappings
    assert 'dll_shape_def.h' in mappings


def test_translate_headers_quoted():
    content = '''#include "sll_shape_def.h"
#include "dll_shape_def.h"
#include "other_header.h"

int main() {
    return 0;
}
'''
    translated = translate_headers(content)
    assert '#include "sll_def.h"' in translated
    assert '#include "dll_def.h"' in translated
    assert '#include "other_header.h"' in translated
    assert '#include "sll_shape_def.h"' not in translated
    assert '#include "dll_shape_def.h"' not in translated


def test_translate_headers_angle():
    content = '''#include <sll_shape_def.h>
#include <stdio.h>

int main() {
    return 0;
}
'''
    translated = translate_headers(content)
    assert '#include <sll_def.h>' in translated
    assert '#include <stdio.h>' in translated
    assert '#include <sll_shape_def.h>' not in translated


def test_translate_headers_mixed():
    content = '''#include <stdio.h>
#include "sll_shape_def.h"
#include <stdlib.h>
#include "dll_shape_def.h"
#include "myheader.h"

struct Node* sll_copy(struct Node* x) {
    return x;
}
'''
    translated = translate_headers(content)
    assert '#include "sll_def.h"' in translated
    assert '#include "dll_def.h"' in translated
    assert '#include <stdio.h>' in translated
    assert '#include <stdlib.h>' in translated
    assert '#include "myheader.h"' in translated


def test_translate_with_custom_mapping():
    content = '''#include "custom_shape.h"
#include "sll_shape_def.h"

int main() {
    return 0;
}
'''
    custom_mappings = {'custom_shape.h': 'custom_def.h'}
    translated = translate_headers(content, mappings=custom_mappings)
    assert '#include "custom_def.h"' in translated
    assert '#include "sll_shape_def.h"' in translated  # unchanged (not in custom)
