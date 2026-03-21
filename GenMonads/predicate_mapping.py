"""
Predicate name mapping module for shape assertion translation.

This module provides functionality to map shape predicate names to data predicate names
during the translation process.

Mappings are persisted to a JSON configuration file.

Format: { "shape_predicate": ["data_predicate", num_list_args] }
Example: { "listrep": ["sll", 1] } means listrep(x) -> sll(x, ?l)
"""

import json
import os
from typing import Dict, Tuple, Optional, List


# Configuration file path
_CONFIG_DIR = os.path.join(os.path.dirname(__file__), 'data')
_CONFIG_FILE = os.path.join(_CONFIG_DIR, 'predicate_mappings.json')

# Default predicate mappings
# Format: shape_name -> (data_name, num_list_args)
_DEFAULT_MAPPINGS: Dict[str, Tuple[str, int]] = {
    # SLL (Singly-Linked List) predicates
    'listrep': ('sll', 1),           # listrep(x) -> sll(x, ?l)
    'lseg': ('sllseg', 1),           # lseg(x, y) -> sllseg(x, y, ?l)

    # DLL (Doubly-Linked List) predicates
    'dlistrep_shape': ('dlistrep', 1),  # dlistrep_shape(x, y) -> dlistrep(x, y, ?l)
    'dllseg_shape': ('dllseg', 1),      # dllseg_shape(x, y, z, w) -> dllseg(x, y, z, w, ?l)
    'dllsegR_shape': ('dllsegR', 1),    # dllsegR_shape(x, y, z, w) -> dllsegR(x, y, z, w, ?l)

    # Already data predicates (name stays the same)
    'sll': ('sll', 1),               # sll(x) -> sll(x, ?l)
    'sllseg': ('sllseg', 1),         # sllseg(x, y) -> sllseg(x, y, ?l)
    'dlistrep': ('dlistrep', 1),     # dlistrep(x, y) -> dlistrep(x, y, ?l)
    'dllseg': ('dllseg', 1),         # dllseg(x, y, z, w) -> dllseg(x, y, z, w, ?l)
    'dllsegR': ('dllsegR', 1),       # dllsegR(x, y, z, w) -> dllsegR(x, y, z, w, ?l)
}


def _convert_to_json_format(mappings: Dict[str, Tuple[str, int]]) -> Dict[str, List]:
    """Convert internal tuple format to JSON-compatible list format."""
    return {k: [v[0], v[1]] for k, v in mappings.items()}


def _convert_from_json_format(data: Dict[str, List]) -> Dict[str, Tuple[str, int]]:
    """Convert JSON list format to internal tuple format."""
    return {k: (v[0], v[1]) for k, v in data.items()}


def _load_mappings() -> Dict[str, Tuple[str, int]]:
    """Load mappings from config file, or return defaults if not exists."""
    if os.path.exists(_CONFIG_FILE):
        try:
            with open(_CONFIG_FILE, 'r', encoding='utf-8') as f:
                data = json.load(f)
                return _convert_from_json_format(data)
        except (json.JSONDecodeError, IOError):
            return _DEFAULT_MAPPINGS.copy()
    return _DEFAULT_MAPPINGS.copy()


def _save_mappings(mappings: Dict[str, Tuple[str, int]]) -> None:
    """Save mappings to config file."""
    os.makedirs(_CONFIG_DIR, exist_ok=True)
    with open(_CONFIG_FILE, 'w', encoding='utf-8') as f:
        json.dump(_convert_to_json_format(mappings), f, indent=2)


def get_predicate_mappings() -> Dict[str, Tuple[str, int]]:
    """
    Get a copy of the current predicate mappings.

    Returns:
        Dictionary mapping shape predicate names to (data_name, num_list_args) tuples
    """
    return _load_mappings()


def add_predicate_mapping(shape_name: str, data_name: str, num_list_args: int = 1) -> None:
    """
    Add a predicate mapping (persisted to config file).

    Args:
        shape_name: Shape predicate name (e.g., 'listrep')
        data_name: Data predicate name (e.g., 'sll')
        num_list_args: Number of list arguments to add (default: 1)
    """
    mappings = _load_mappings()
    mappings[shape_name] = (data_name, num_list_args)
    _save_mappings(mappings)


def remove_predicate_mapping(shape_name: str) -> bool:
    """
    Remove a predicate mapping (persisted to config file).

    Args:
        shape_name: Shape predicate name to remove

    Returns:
        True if mapping was removed, False if it didn't exist
    """
    mappings = _load_mappings()
    if shape_name in mappings:
        del mappings[shape_name]
        _save_mappings(mappings)
        return True
    return False


def clear_predicate_mappings() -> None:
    """Clear all predicate mappings (persisted to config file)."""
    _save_mappings({})


def reset_predicate_mappings() -> None:
    """Reset predicate mappings to default values (persisted to config file)."""
    _save_mappings(_DEFAULT_MAPPINGS.copy())


def get_predicate_mapping(shape_name: str) -> Optional[Tuple[str, int]]:
    """
    Get a single predicate mapping.

    Args:
        shape_name: Shape predicate name to look up

    Returns:
        Tuple of (data_name, num_list_args) or None if not found
    """
    mappings = _load_mappings()
    return mappings.get(shape_name)
