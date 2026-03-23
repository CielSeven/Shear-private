import json

import pytest

import GenMonads.predicate_mapping as predicate_mapping
from GenMonads.predicate_mapping import (
    PredicateMapping,
    add_predicate_mapping,
    get_predicate_mapping,
    get_predicate_mappings,
)


def test_new_schema_loads_predicate_metadata():
    mapping = get_predicate_mapping("listrep")

    assert mapping == PredicateMapping(
        data_name="sll",
        shape_arity=1,
        data_arity=1,
        data_var_types=["list Z"],
    )


def test_legacy_list_style_mapping_is_rejected(tmp_path, monkeypatch):
    config_dir = tmp_path / "data"
    config_dir.mkdir()
    config_file = config_dir / "predicate_mappings.json"
    config_file.write_text(json.dumps({"listrep": ["sll", 1]}), encoding="utf-8")

    monkeypatch.setattr(predicate_mapping, "_CONFIG_DIR", str(config_dir))
    monkeypatch.setattr(predicate_mapping, "_CONFIG_FILE", str(config_file))

    with pytest.raises(ValueError, match="expected an object"):
        get_predicate_mappings()


def test_add_predicate_mapping_requires_data_var_types():
    with pytest.raises(ValueError, match="data_var_types is required"):
        add_predicate_mapping("foo", "bar", data_arity=1)


def test_new_schema_loads_non_list_types(tmp_path, monkeypatch):
    config_dir = tmp_path / "data"
    config_dir.mkdir()
    config_file = config_dir / "predicate_mappings.json"
    config_file.write_text(
        json.dumps(
            {
                "boxed_int_shape": {
                    "data_name": "boxed_int",
                    "shape_arity": 1,
                    "data_arity": 2,
                    "data_var_types": ["Z", "bool"],
                }
            }
        ),
        encoding="utf-8",
    )

    monkeypatch.setattr(predicate_mapping, "_CONFIG_DIR", str(config_dir))
    monkeypatch.setattr(predicate_mapping, "_CONFIG_FILE", str(config_file))

    mappings = get_predicate_mappings()

    assert mappings["boxed_int_shape"] == PredicateMapping(
        data_name="boxed_int",
        shape_arity=1,
        data_arity=2,
        data_var_types=["Z", "bool"],
    )
