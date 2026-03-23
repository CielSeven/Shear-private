"""
Predicate mapping module for shape assertion translation.

Mappings are persisted to a JSON configuration file.

Required JSON schema:
{
  "shape_predicate": {
    "data_name": "data_predicate",
    "shape_arity": 1,
    "data_arity": 1,
    "data_var_types": ["list Z"]
  }
}
"""

from dataclasses import dataclass
import json
import os
from typing import Any, Dict, List, Optional


# Configuration file path
_CONFIG_DIR = os.path.join(os.path.dirname(__file__), 'data')
_CONFIG_FILE = os.path.join(_CONFIG_DIR, 'predicate_mappings.json')

@dataclass(frozen=True)
class PredicateMapping:
    """Mapping metadata for one predicate family."""

    data_name: str
    shape_arity: int
    data_arity: int
    data_var_types: List[str]


def _make_mapping(data_name: str, shape_arity: int, data_var_types: List[str]) -> PredicateMapping:
    return PredicateMapping(
        data_name=data_name,
        shape_arity=shape_arity,
        data_arity=len(data_var_types),
        data_var_types=data_var_types[:],
    )


# Default predicate mappings using the new schema
_DEFAULT_MAPPINGS: Dict[str, PredicateMapping] = {
    'listrep': _make_mapping('sll', 1, ['list Z']),
    'lseg': _make_mapping('sllseg', 2, ['list Z']),
    'dlistrep_shape': _make_mapping('dlistrep', 2, ['list Z']),
    'dllseg_shape': _make_mapping('dllseg', 4, ['list Z']),
    'dllsegR_shape': _make_mapping('dllsegR', 4, ['list Z']),
}


def _mapping_to_json(mapping: PredicateMapping) -> Dict[str, Any]:
    return {
        'data_name': mapping.data_name,
        'shape_arity': mapping.shape_arity,
        'data_arity': mapping.data_arity,
        'data_var_types': mapping.data_var_types[:],
    }


def _normalize_mapping(shape_name: str, raw_mapping: object) -> PredicateMapping:
    """Normalize a JSON entry into a PredicateMapping."""
    if not isinstance(raw_mapping, dict):
        raise ValueError(
            f"Invalid mapping for {shape_name!r}: expected an object with "
            "data_name, shape_arity, data_arity, and data_var_types"
        )

    data_name = raw_mapping.get('data_name')
    shape_arity = raw_mapping.get('shape_arity')
    data_arity = raw_mapping.get('data_arity')
    data_var_types = raw_mapping.get('data_var_types')

    if not isinstance(data_name, str) or not data_name:
        raise ValueError(f"Invalid data_name for {shape_name!r}")
    if not isinstance(shape_arity, int):
        raise ValueError(f"Invalid shape_arity for {shape_name!r}")
    if not isinstance(data_arity, int) or data_arity < 0:
        raise ValueError(f"Invalid data_arity for {shape_name!r}")
    if not isinstance(data_var_types, list) or any(not isinstance(t, str) or not t for t in data_var_types):
        raise ValueError(f"Invalid data_var_types for {shape_name!r}")
    if len(data_var_types) != data_arity:
        raise ValueError(
            f"data_arity/data_var_types mismatch for {shape_name!r}: "
            f"{data_arity} != {len(data_var_types)}"
        )

    return PredicateMapping(
        data_name=data_name,
        shape_arity=shape_arity,
        data_arity=data_arity,
        data_var_types=data_var_types[:],
    )


def _convert_to_json_format(mappings: Dict[str, PredicateMapping]) -> Dict[str, Dict[str, Any]]:
    """Convert internal format to JSON-compatible schema objects."""
    return {name: _mapping_to_json(mapping) for name, mapping in mappings.items()}


def _convert_from_json_format(data: Dict[str, Any]) -> Dict[str, PredicateMapping]:
    """Convert JSON data to PredicateMapping objects."""
    return {name: _normalize_mapping(name, mapping) for name, mapping in data.items()}


def _load_mappings() -> Dict[str, PredicateMapping]:
    """Load mappings from config file, or return defaults if not exists."""
    if os.path.exists(_CONFIG_FILE):
        try:
            with open(_CONFIG_FILE, 'r', encoding='utf-8') as f:
                data = json.load(f)
                return _convert_from_json_format(data)
        except (json.JSONDecodeError, IOError):
            return _DEFAULT_MAPPINGS.copy()
    return _DEFAULT_MAPPINGS.copy()


def _save_mappings(mappings: Dict[str, PredicateMapping]) -> None:
    """Save mappings to config file."""
    os.makedirs(_CONFIG_DIR, exist_ok=True)
    with open(_CONFIG_FILE, 'w', encoding='utf-8') as f:
        json.dump(_convert_to_json_format(mappings), f, indent=2)


def get_predicate_mappings() -> Dict[str, PredicateMapping]:
    """
    Get a copy of the current predicate mappings.

    Returns:
        Dictionary mapping shape predicate names to PredicateMapping objects
    """
    return _load_mappings()


def add_predicate_mapping(
    shape_name: str,
    data_name: str,
    data_arity: int = 1,
    *,
    shape_arity: Optional[int] = None,
    data_var_types: Optional[List[str]] = None,
) -> None:
    """
    Add a predicate mapping (persisted to config file).

    Args:
        shape_name: Shape predicate name (e.g., 'listrep')
        data_name: Data predicate name (e.g., 'sll')
        data_arity: Number of augmented data arguments to add
        shape_arity: Number of original shape predicate arguments
        data_var_types: Coq types for each augmented data argument
    """
    if data_var_types is None:
        raise ValueError("data_var_types is required and must match data_arity")
    if shape_arity is None:
        shape_arity = data_arity
    if len(data_var_types) != data_arity:
        raise ValueError(
            f"data_var_types length mismatch: expected {data_arity}, got {len(data_var_types)}"
        )

    mappings = _load_mappings()
    mappings[shape_name] = PredicateMapping(
        data_name=data_name,
        shape_arity=shape_arity,
        data_arity=data_arity,
        data_var_types=data_var_types[:],
    )
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


def get_predicate_mapping(shape_name: str) -> Optional[PredicateMapping]:
    """
    Get a single predicate mapping.

    Args:
        shape_name: Shape predicate name to look up

    Returns:
        PredicateMapping or None if not found
    """
    mappings = _load_mappings()
    return mappings.get(shape_name)
