"""
Header file mapping module for C file translation.

This module provides functionality to map header file includes from one name to another
during the C file translation process.

Mappings are persisted to a JSON configuration file.
"""

import json
import os
import re
from typing import Dict, Optional


# Configuration file path
_CONFIG_DIR = os.path.join(os.path.dirname(__file__), 'data')
_CONFIG_FILE = os.path.join(_CONFIG_DIR, 'header_mappings.json')

# Default header mappings
_DEFAULT_MAPPINGS: Dict[str, str] = {
    'dll_shape_def.h': 'dll_def.h',
    'sll_shape_def.h': 'sll_def.h',
}


def _load_mappings() -> Dict[str, str]:
    """Load mappings from config file, or return defaults if not exists."""
    if os.path.exists(_CONFIG_FILE):
        try:
            with open(_CONFIG_FILE, 'r', encoding='utf-8') as f:
                return json.load(f)
        except (json.JSONDecodeError, IOError):
            return _DEFAULT_MAPPINGS.copy()
    return _DEFAULT_MAPPINGS.copy()


def _save_mappings(mappings: Dict[str, str]) -> None:
    """Save mappings to config file."""
    os.makedirs(_CONFIG_DIR, exist_ok=True)
    with open(_CONFIG_FILE, 'w', encoding='utf-8') as f:
        json.dump(mappings, f, indent=2)


def get_header_mappings() -> Dict[str, str]:
    """
    Get a copy of the current header mappings.

    Returns:
        Dictionary mapping original header names to translated names
    """
    return _load_mappings()


def add_header_mapping(original: str, translated: str) -> None:
    """
    Add a header file mapping (persisted to config file).

    Args:
        original: Original header file name (e.g., 'sll_shape_def.h')
        translated: Translated header file name (e.g., 'sll_def.h')
    """
    mappings = _load_mappings()
    mappings[original] = translated
    _save_mappings(mappings)


def remove_header_mapping(original: str) -> bool:
    """
    Remove a header file mapping (persisted to config file).

    Args:
        original: Original header file name to remove

    Returns:
        True if mapping was removed, False if it didn't exist
    """
    mappings = _load_mappings()
    if original in mappings:
        del mappings[original]
        _save_mappings(mappings)
        return True
    return False


def clear_header_mappings() -> None:
    """Clear all header mappings (persisted to config file)."""
    _save_mappings({})


def reset_header_mappings() -> None:
    """Reset header mappings to default values (persisted to config file)."""
    _save_mappings(_DEFAULT_MAPPINGS.copy())


def translate_headers(content: str, mappings: Optional[Dict[str, str]] = None) -> str:
    """
    Translate header file includes in C file content.

    Args:
        content: C file content
        mappings: Optional custom mappings (uses persisted mappings if None)

    Returns:
        Content with translated header includes
    """
    if mappings is None:
        mappings = _load_mappings()

    for original, translated in mappings.items():
        # Match #include "header.h" or #include <header.h>
        # Pattern handles both quoted and angle bracket includes
        pattern_quoted = rf'#include\s*"{re.escape(original)}"'
        pattern_angle = rf'#include\s*<{re.escape(original)}>'

        content = re.sub(pattern_quoted, f'#include "{translated}"', content)
        content = re.sub(pattern_angle, f'#include <{translated}>', content)

    return content
