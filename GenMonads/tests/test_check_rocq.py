"""Tests for the _CoqProject logical-path resolver added in Option C.

The resolver turns a physical .v path under a project's -Q/-R bindings
into the canonical Coq logical name used in `Require Import` statements.
"""

import os

import pytest

from GenMonads.absprog.check_rocq import (
    parse_coq_project_mappings,
    qualified_require_import_for_callee,
    resolve_lib_logical_path,
)


def _cp(tmp_path, body):
    p = tmp_path / "_CoqProject"
    p.write_text(body, encoding="utf-8")
    return str(p)


class TestParseCoqProjectMappings:
    def test_extracts_q_and_r_mappings(self, tmp_path):
        cp = _cp(
            tmp_path,
            "# comment\n"
            "-Q /foo/lib_a A\n"
            "-R /bar/lib_b B.Sub\n"
            "\n"
            '-Q /baz/lib_c ""\n',
        )
        mappings = parse_coq_project_mappings(cp)
        # Order preserved.
        assert mappings == [
            (os.path.abspath("/foo/lib_a"), "A"),
            (os.path.abspath("/bar/lib_b"), "B.Sub"),
            (os.path.abspath("/baz/lib_c"), ""),
        ]

    def test_ignores_non_q_r_lines(self, tmp_path):
        cp = _cp(
            tmp_path,
            "-arg something\n"
            "-Q /yes A\n"
            "# -Q commented-out B\n",
        )
        mappings = parse_coq_project_mappings(cp)
        assert mappings == [(os.path.abspath("/yes"), "A")]

    def test_returns_empty_when_file_missing(self, tmp_path):
        missing = str(tmp_path / "nope")
        assert parse_coq_project_mappings(missing) == []


class TestResolveLibLogicalPath:
    def test_qualified_under_r_with_subdir(self, tmp_path):
        # -R /libs PREFIX  →  /libs/sub/foo.v → PREFIX.sub.foo
        libs = tmp_path / "libs"
        libs.mkdir()
        cp = _cp(tmp_path, f"-R {libs} LLM4PV.libs\n")
        lib_file = libs / "sub" / "foo_rel_lib.v"
        lib_file.parent.mkdir()
        lib_file.write_text("(* stub *)\n")
        assert resolve_lib_logical_path(cp, str(lib_file)) == (
            "LLM4PV.libs.sub.foo_rel_lib"
        )

    def test_qualified_under_r_flat(self, tmp_path):
        libs = tmp_path / "libs"
        libs.mkdir()
        cp = _cp(tmp_path, f"-R {libs} LIB\n")
        lib_file = libs / "foo_rel_lib.v"
        lib_file.write_text("")
        assert resolve_lib_logical_path(cp, str(lib_file)) == "LIB.foo_rel_lib"

    def test_empty_prefix_q_drops_segment(self, tmp_path):
        libs = tmp_path / "libs"
        libs.mkdir()
        cp = _cp(tmp_path, f'-Q {libs} ""\n')
        flat = libs / "foo_rel_lib.v"
        nested = libs / "sub" / "bar_rel_lib.v"
        flat.write_text("")
        nested.parent.mkdir()
        nested.write_text("")
        assert resolve_lib_logical_path(cp, str(flat)) == "foo_rel_lib"
        assert resolve_lib_logical_path(cp, str(nested)) == "sub.bar_rel_lib"

    def test_longest_prefix_match_wins(self, tmp_path):
        """When both -R /libs P1 and -R /libs/sub P2 cover the file, the
        more specific binding (longer physical path) is the right one."""
        libs = tmp_path / "libs"
        sub = libs / "sub"
        sub.mkdir(parents=True)
        cp = _cp(
            tmp_path,
            f"-R {libs} Outer\n"
            f"-R {sub} Inner\n",
        )
        nested = sub / "foo_rel_lib.v"
        nested.write_text("")
        assert resolve_lib_logical_path(cp, str(nested)) == "Inner.foo_rel_lib"

    def test_no_matching_prefix_returns_none(self, tmp_path):
        libs = tmp_path / "libs"
        elsewhere = tmp_path / "elsewhere"
        libs.mkdir()
        elsewhere.mkdir()
        cp = _cp(tmp_path, f"-R {libs} LIB\n")
        outsider = elsewhere / "foo_rel_lib.v"
        outsider.write_text("")
        assert resolve_lib_logical_path(cp, str(outsider)) is None

    def test_directory_boundary_match_not_substring(self, tmp_path):
        """-R /libs LIB should NOT match a file under /libs_extra/...
        even though `startswith` would say so."""
        libs = tmp_path / "libs"
        libs_extra = tmp_path / "libs_extra"
        libs.mkdir()
        libs_extra.mkdir()
        cp = _cp(tmp_path, f"-R {libs} LIB\n")
        file_in_extra = libs_extra / "foo_rel_lib.v"
        file_in_extra.write_text("")
        assert resolve_lib_logical_path(cp, str(file_in_extra)) is None

    def test_pre_dotted_logical_prefix_kept_intact(self, tmp_path):
        """A prefix like ``A.B.C`` already has its dots; emitting it should
        not produce double dots or treat it as a single segment."""
        libs = tmp_path / "libs"
        libs.mkdir()
        cp = _cp(tmp_path, f"-R {libs} A.B.C\n")
        lib_file = libs / "foo_rel_lib.v"
        lib_file.write_text("")
        assert resolve_lib_logical_path(cp, str(lib_file)) == "A.B.C.foo_rel_lib"


class TestQualifiedRequireImportHelper:
    def test_returns_qualified_when_project_resolves(self, tmp_path):
        libs = tmp_path / "libs"
        libs.mkdir()
        cp = _cp(tmp_path, f"-R {libs} PROJ.libs\n")
        # The helper walks up from coq_lib_dir to find _CoqProject.
        # _cp put it at tmp_path/_CoqProject; libs is the child dir.
        # Create the callee file so the resolver path-exists check passes
        # in spirit (resolver itself doesn't require existence, but the
        # presence keeps the contract aligned with real-world callers).
        (libs / "foo_rel_lib.v").write_text("")
        result = qualified_require_import_for_callee("foo", str(libs))
        assert result == "PROJ.libs.foo_rel_lib"

    def test_falls_back_to_bare_when_no_coq_lib_dir(self, tmp_path):
        # Without a lib dir to anchor the lookup, the helper preserves the
        # historical bare-name behaviour.
        assert qualified_require_import_for_callee("foo", None) == "foo_rel_lib"

    def test_falls_back_to_bare_when_no_project_found(self, tmp_path):
        # coq_lib_dir given but no _CoqProject in any ancestor: emit bare.
        deep = tmp_path / "no_project_here"
        deep.mkdir()
        assert qualified_require_import_for_callee("foo", str(deep)) == "foo_rel_lib"

    def test_falls_back_to_bare_when_path_uncovered_by_project(self, tmp_path):
        """Project exists but no -Q/-R covers the lib dir → fall back so
        we don't emit something that ``coqc`` definitely can't resolve."""
        libs = tmp_path / "libs"
        libs.mkdir()
        # _CoqProject lives next to libs but binds an unrelated directory.
        _cp(tmp_path, f"-R {tmp_path / 'somewhere_else'} OTHER\n")
        assert qualified_require_import_for_callee("foo", str(libs)) == "foo_rel_lib"
