import json

import GenMonads.parser_symbols as parser_symbols


def test_parser_symbols_are_loaded_once(tmp_path, monkeypatch):
    config_file = tmp_path / "parser_symbols.json"
    config_file.write_text(
        json.dumps({
            "spatial_predicates": ["emp", "custom_spatial"],
            "pure_call_exprs": ["custom_call"],
        }),
        encoding="utf-8",
    )

    exists_calls = []
    original_exists = parser_symbols.os.path.exists

    def counted_exists(path):
        exists_calls.append(path)
        return original_exists(path)

    parser_symbols.clear_parser_symbols_cache()
    monkeypatch.setattr(parser_symbols, "_CONFIG_FILE", str(config_file))
    monkeypatch.setattr(parser_symbols.os.path, "exists", counted_exists)

    try:
        assert parser_symbols.get_parser_symbols()["pure_call_exprs"] == ["custom_call"]
        assert parser_symbols.get_parser_symbols()["spatial_predicates"] == ["emp", "custom_spatial"]
        assert parser_symbols.get_parser_symbols()["pure_call_exprs"] == ["custom_call"]
        assert exists_calls == [str(config_file)]
    finally:
        parser_symbols.clear_parser_symbols_cache()
