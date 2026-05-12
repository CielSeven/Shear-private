"""Generate first-stage residual definitions for callee calls in a caller program."""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Dict, List, Optional, Set, Tuple


_DEF_RE = re.compile(r"^Definition\s+([A-Za-z_][A-Za-z0-9_']*)\b", re.MULTILINE)
_IDENT_BOUNDARY = r"[A-Za-z0-9_']"
_IDENT_RE = re.compile(
    rf"(?<!{_IDENT_BOUNDARY})([A-Za-z_][A-Za-z0-9_']*)(?!{_IDENT_BOUNDARY})"
)
_PATTERN_RESERVED = {
    "Continue",
    "ReturnNow",
    "by_continue",
    "by_break",
    "nil",
    "true",
    "false",
}


@dataclass
class DefinitionBlock:
    name: str
    body: str
    start: int
    text: str
    signature: Optional[str]


@dataclass
class Continuation:
    binder: str
    body: str


@dataclass
class ResidualSegment:
    caller_component: str
    call_index: int
    binder: str
    body: str
    definition: str
    captured_identifiers: List[str]
    captured_identifier_types: Dict[str, str]
    callee_return_type: Optional[str]
    caller_return_type: Optional[str]
    origin_component: str
    origin_start: int


def _is_simple_identifier(name: str) -> bool:
    return bool(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", name))


def _binder_is_used(binder: str, body: str) -> bool:
    if binder == "_":
        return False
    return re.search(
        rf"(?<!{_IDENT_BOUNDARY}){re.escape(binder)}(?!{_IDENT_BOUNDARY})",
        body,
    ) is not None


def promote_captured_identifiers_to_arguments(
    definition: str,
    captured_identifiers: List[str],
    captured_identifier_types: Optional[Dict[str, str]] = None,
) -> str:
    """Add captured identifiers as explicit arguments in the Definition header."""

    if not captured_identifiers:
        return definition
    captured_identifier_types = captured_identifier_types or {}

    lines = definition.splitlines()
    if not lines:
        return definition

    header = lines[0]
    assign_index = header.find(":=")
    if assign_index == -1:
        return definition

    before_assign = header[:assign_index].rstrip()
    after_assign = header[assign_index:]
    match = re.fullmatch(
        r"(Definition\s+[A-Za-z_][A-Za-z0-9_']*)(\s*:\s*.+)?",
        before_assign,
    )
    if match is None:
        return definition

    header_prefix = match.group(1)
    header_type = match.group(2) or ""
    promoted_args = []
    for identifier in captured_identifiers:
        identifier_type = captured_identifier_types.get(identifier)
        if identifier_type:
            promoted_args.append(f"({identifier} : {identifier_type})")
        else:
            promoted_args.append(identifier)
    promoted_header = (
        f"{header_prefix} {' '.join(promoted_args)}{header_type} {after_assign}"
    )
    return "\n".join([promoted_header] + lines[1:])


def _parse_definition_blocks(text: str) -> Dict[str, DefinitionBlock]:
    matches = list(_DEF_RE.finditer(text))
    blocks: Dict[str, DefinitionBlock] = {}
    for index, match in enumerate(matches):
        start = match.start()
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        block_text = text[start:end].strip()
        assign_index = block_text.find(":=")
        body = block_text[assign_index + 2:].strip() if assign_index != -1 else ""
        signature = None
        if assign_index != -1:
            header = block_text[:assign_index].rstrip()
            colon_index = header.rfind(":")
            if colon_index != -1:
                signature = header[colon_index + 1:].strip()
        blocks[match.group(1)] = DefinitionBlock(
            name=match.group(1),
            body=body,
            start=start,
            text=block_text,
            signature=signature,
        )
    return blocks


def _parse_parameter_signatures(text: str) -> Dict[str, str]:
    signatures: Dict[str, str] = {}
    for match in re.finditer(
        r"^Parameter\s+([A-Za-z_][A-Za-z0-9_']*)\s*:",
        text,
        re.MULTILINE,
    ):
        name = match.group(1)
        rest = text[match.end():]
        # Find the terminating period at paren depth 0.
        depth = 0
        end = -1
        for i, ch in enumerate(rest):
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth = max(0, depth - 1)
            elif ch == "." and depth == 0:
                end = i
                break
        if end == -1:
            continue
        sig = " ".join(rest[:end].split())
        signatures[name] = sig
    return signatures


def _strip_terminal_period(text: str) -> str:
    stripped = text.strip()
    if stripped.endswith("."):
        return stripped[:-1].rstrip()
    return stripped


def _strip_leading_fun(expr: str) -> str:
    current = expr.strip()
    while current.startswith("fun "):
        depth = 0
        idx = 0
        while idx < len(current) - 1:
            ch = current[idx]
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth = max(0, depth - 1)
            elif depth == 0 and current[idx:idx + 2] == "=>":
                current = current[idx + 2:].strip()
                break
            idx += 1
        else:
            return expr.strip()
    return current


def _parse_leading_fun(expr: str) -> Optional[Tuple[str, str]]:
    current = expr.strip()
    if not current.startswith("fun "):
        return None

    depth = 0
    idx = 0
    while idx < len(current) - 1:
        ch = current[idx]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        elif depth == 0 and current[idx:idx + 2] == "=>":
            binder_part = current[len("fun "):idx].strip()
            body = current[idx + 2:].strip()
            if not binder_part:
                return None
            return binder_part, body
        idx += 1
    return None


def _strip_wrapping_parens(expr: str) -> str:
    current = expr.strip()
    while current.startswith("(") and current.endswith(")"):
        depth = 0
        balanced = True
        for idx, ch in enumerate(current):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and idx != len(current) - 1:
                    balanced = False
                    break
        if not balanced or depth != 0:
            break
        current = current[1:-1].strip()
    return current


def _split_top_level_type(expr: str, separator: str) -> List[str]:
    parts: List[str] = []
    current: List[str] = []
    depth = 0
    idx = 0
    while idx < len(expr):
        ch = expr[idx]
        if ch in "([{":
            depth += 1
            current.append(ch)
            idx += 1
            continue
        if ch in ")]}":
            depth = max(0, depth - 1)
            current.append(ch)
            idx += 1
            continue
        if depth == 0 and expr[idx:idx + len(separator)] == separator:
            parts.append("".join(current).strip())
            current = []
            idx += len(separator)
            continue
        current.append(ch)
        idx += 1
    parts.append("".join(current).strip())
    return [part for part in parts if part]


def _split_top_level_arrow_type(type_expr: str) -> List[str]:
    return _split_top_level_type(type_expr, "->")


def _split_top_level_product_type(type_expr: str) -> List[str]:
    return _split_top_level_type(_strip_wrapping_parens(type_expr), "*")


def _split_top_level_tuple_pattern(pattern: str) -> Optional[List[str]]:
    stripped = pattern.strip()
    if stripped.startswith("'"):
        stripped = stripped[1:].strip()
    stripped = _strip_wrapping_parens(stripped)
    if "," not in stripped:
        return None
    parts = _split_top_level_type(stripped, ",")
    return parts if len(parts) > 1 else None


def _substitute_identifier(expr: str, identifier: str, replacement: str) -> str:
    pattern = re.compile(
        rf"(?<!{_IDENT_BOUNDARY}){re.escape(identifier)}(?!{_IDENT_BOUNDARY})"
    )
    return pattern.sub(replacement, expr)


def _extract_identifiers(expr: str) -> List[str]:
    return [match.group(1) for match in _IDENT_RE.finditer(expr)]


def _fresh_identifier(base: str, forbidden: Set[str]) -> str:
    if base == "_":
        base = "v"
    candidate = base
    counter = 0
    while candidate in forbidden:
        counter += 1
        candidate = f"{base}{counter}"
    return candidate


def _rename_identifier(expr: str, old: str, new: str) -> str:
    if old == new:
        return expr
    return _substitute_identifier(expr, old, new)


def _collect_pattern_bound_identifiers(pattern: str) -> Set[str]:
    return {
        name
        for name in _extract_identifiers(pattern)
        if name not in _PATTERN_RESERVED
    }


def _freshen_continuation(cont: Optional[Continuation], forbidden: Set[str]) -> Optional[Continuation]:
    if cont is None or cont.binder == "_" or cont.binder not in forbidden:
        return cont
    fresh = _fresh_identifier(cont.binder, forbidden.union(set(_extract_identifiers(cont.body))))
    return Continuation(
        binder=fresh,
        body=_rename_identifier(cont.body, cont.binder, fresh),
    )


def _freshen_bound_identifiers(expr: str, forbidden: Set[str]) -> str:
    result = expr
    local_bound = sorted(_collect_locally_bound_identifiers(result))
    used = forbidden.union(set(_extract_identifiers(result)))
    for binder in local_bound:
        if binder == "_" or binder not in forbidden:
            continue
        fresh = _fresh_identifier(binder, used)
        result = _rename_identifier(result, binder, fresh)
        used.add(fresh)
    return result


def _reconstruct_match(scrutinee: str, branches: List[Tuple[str, str]]) -> str:
    lines = [f"match {scrutinee} with"]
    for pattern, body in branches:
        body_lines = body.splitlines()
        if len(body_lines) == 1:
            lines.append(f"| {pattern} => {body_lines[0]}")
        else:
            lines.append(f"| {pattern} =>")
            lines.extend(body_lines)
    lines.append("end")
    return "\n".join(lines)


def _format_application_argument(arg: str) -> str:
    stripped = arg.strip()
    if not stripped:
        return stripped
    if stripped.startswith("(") and stripped.endswith(")"):
        return stripped
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", stripped):
        return stripped
    return f"({stripped})"


def _substitute_identifier_scoped(expr: str, identifier: str, replacement: str) -> str:
    expr = _strip_terminal_period(expr)

    parsed_fun = _parse_leading_fun(expr)
    if parsed_fun is not None:
        binder_part, body = parsed_fun
        if identifier in _collect_pattern_bound_identifiers(binder_part):
            return f"fun {binder_part} => {body}"
        return f"fun {binder_part} => {_substitute_identifier_scoped(body, identifier, replacement)}"

    let_parts = _split_top_level_let(expr)
    if let_parts is not None:
        pattern, value, body = let_parts
        value_sub = _substitute_identifier_scoped(value, identifier, replacement)
        if identifier in _collect_pattern_bound_identifiers(pattern):
            body_sub = body
        else:
            body_sub = _substitute_identifier_scoped(body, identifier, replacement)
        return f"let {pattern} := {value_sub} in {body_sub}"

    bind_parts = _split_top_level_bind(expr)
    if bind_parts is not None:
        binder, left, right = bind_parts
        left_sub = _substitute_identifier_scoped(left, identifier, replacement)
        if binder == identifier:
            right_sub = right
        else:
            right_sub = _substitute_identifier_scoped(right, identifier, replacement)
        return f"{binder} <- {left_sub};;\n{right_sub}"

    match_parts = _parse_top_level_match(expr)
    if match_parts is not None:
        scrutinee, branches = match_parts
        scrutinee_sub = _substitute_identifier_scoped(scrutinee, identifier, replacement)
        branch_subs: List[Tuple[str, str]] = []
        for pattern, body in branches:
            if identifier in _collect_pattern_bound_identifiers(pattern):
                branch_subs.append((pattern, body))
            else:
                branch_subs.append(
                    (pattern, _substitute_identifier_scoped(body, identifier, replacement))
                )
        return _reconstruct_match(scrutinee_sub, branch_subs)

    seq_parts = _split_top_level_sequence(expr)
    if seq_parts is not None:
        left, right = seq_parts
        return (
            f"{_substitute_identifier_scoped(left, identifier, replacement)};;\n"
            f"{_substitute_identifier_scoped(right, identifier, replacement)}"
        )

    head, args = _parse_top_level_application(expr)
    if head and args:
        substituted_args = [
            _format_application_argument(
                _substitute_identifier_scoped(arg, identifier, replacement)
            )
            for arg in args
        ]
        return f"{head} {' '.join(substituted_args)}"

    return _substitute_identifier(expr, identifier, replacement)


def _match_keyword_at(expr: str, index: int, keyword: str) -> bool:
    end = index + len(keyword)
    if expr[index:end] != keyword:
        return False
    before_ok = index == 0 or not (expr[index - 1].isalnum() or expr[index - 1] == "_")
    after_ok = end >= len(expr) or not (expr[end].isalnum() or expr[end] == "_")
    return before_ok and after_ok


def _find_matching_end(expr: str, start_keyword: str = "match") -> Optional[int]:
    depth = 0
    idx = 0
    while idx < len(expr):
        if _match_keyword_at(expr, idx, start_keyword):
            depth += 1
            idx += len(start_keyword)
            continue
        if _match_keyword_at(expr, idx, "end"):
            depth -= 1
            idx += len("end")
            if depth == 0:
                return idx
            continue
        idx += 1
    return None


def _parse_top_level_match(expr: str) -> Optional[Tuple[str, List[Tuple[str, str]]]]:
    expr = _strip_wrapping_parens(expr)
    if not expr.startswith("match "):
        return None

    match_depth = 0
    with_index = -1
    idx = 0
    while idx < len(expr):
        if _match_keyword_at(expr, idx, "match"):
            match_depth += 1
            idx += len("match")
            continue
        if _match_keyword_at(expr, idx, "with"):
            if match_depth == 1:
                with_index = idx
                idx += len("with")
                break
            idx += len("with")
            continue
        idx += 1

    if with_index == -1:
        return None

    end_index = _find_matching_end(expr, "match")
    if end_index is None:
        return None

    scrutinee = expr[len("match"):with_index].strip()
    branches_text = expr[with_index + len("with"):end_index - len("end")].strip()
    branches: List[Tuple[str, str]] = []
    idx = 0
    branch_start = -1
    body_start = -1
    current_pattern: Optional[str] = None
    paren_depth = 0
    nested_match = 0

    while idx < len(branches_text):
        ch = branches_text[idx]
        if ch in "([{":
            paren_depth += 1
            idx += 1
            continue
        if ch in ")]}":
            paren_depth = max(0, paren_depth - 1)
            idx += 1
            continue
        if paren_depth == 0:
            if _match_keyword_at(branches_text, idx, "match"):
                nested_match += 1
                idx += len("match")
                continue
            if _match_keyword_at(branches_text, idx, "end") and nested_match > 0:
                nested_match -= 1
                idx += len("end")
                continue
            if branches_text[idx] == "|" and nested_match == 0:
                if body_start != -1:
                    if current_pattern is None:
                        raise ValueError("Malformed match: found branch body without a pattern")
                    branches.append((current_pattern, branches_text[body_start:idx].strip()))
                    body_start = -1
                    current_pattern = None
                branch_start = idx + 1
                idx += 1
                continue
            if branches_text[idx:idx + 2] == "=>" and nested_match == 0 and body_start == -1:
                current_pattern = branches_text[branch_start:idx].strip()
                body_start = idx + 2
                idx += 2
                continue
        idx += 1

    if body_start != -1:
        if current_pattern is None:
            raise ValueError("Malformed match: found branch body without a pattern")
        branches.append((current_pattern, branches_text[body_start:].strip()))

    return scrutinee, [(pattern, body) for pattern, body in branches if body]


def _parse_top_level_match_branches(expr: str) -> Optional[List[str]]:
    parsed = _parse_top_level_match(expr)
    if parsed is None:
        return None
    _, branches = parsed
    return [body for _, body in branches]


def _parse_top_level_application(expr: str) -> Tuple[str, List[str]]:
    expr = _strip_wrapping_parens(expr).strip()
    match = re.match(r"([A-Za-z_][A-Za-z0-9_']*)", expr)
    if not match:
        return "", []

    head = match.group(1)
    rest = expr[match.end():].strip()
    if not rest:
        return head, []

    args: List[str] = []
    current: List[str] = []
    paren_depth = 0
    match_depth = 0
    idx = 0
    while idx < len(rest):
        ch = rest[idx]
        if ch in "([{":
            paren_depth += 1
            current.append(ch)
            idx += 1
            continue
        if ch in ")]}":
            paren_depth = max(0, paren_depth - 1)
            current.append(ch)
            idx += 1
            continue
        if paren_depth == 0:
            if _match_keyword_at(rest, idx, "match"):
                match_depth += 1
            if _match_keyword_at(rest, idx, "end") and match_depth > 0:
                match_depth -= 1
            if ch.isspace() and match_depth == 0:
                if current:
                    args.append("".join(current).strip())
                    current = []
                idx += 1
                while idx < len(rest) and rest[idx].isspace():
                    idx += 1
                continue
        current.append(ch)
        idx += 1
    if current:
        args.append("".join(current).strip())
    return head, [arg for arg in args if arg]


def _bind_pattern_types(
    pattern: str,
    type_expr: Optional[str],
    type_env: Dict[str, str],
) -> Dict[str, str]:
    env = dict(type_env)
    if not type_expr:
        return env

    stripped = pattern.strip()
    if stripped == "_" or stripped in {"nil", "true", "false"}:
        return env

    tuple_parts = _split_top_level_tuple_pattern(stripped)
    if tuple_parts is not None:
        type_parts = _split_top_level_product_type(type_expr)
        if len(type_parts) == len(tuple_parts):
            for subpattern, subtype in zip(tuple_parts, type_parts):
                env = _bind_pattern_types(subpattern, subtype, env)
        return env

    cons_match = re.fullmatch(r"([A-Za-z_][A-Za-z0-9_']*)\s*::\s*([A-Za-z_][A-Za-z0-9_']*)", stripped)
    if cons_match is not None:
        head_name, tail_name = cons_match.groups()
        head_type = None
        list_match = re.fullmatch(r"list\s+(.+)", _strip_wrapping_parens(type_expr))
        if list_match is not None:
            head_type = list_match.group(1).strip()
        if head_type:
            env[head_name] = head_type
        env[tail_name] = _strip_wrapping_parens(type_expr)
        return env

    app_head, app_args = _parse_top_level_application(stripped)
    if app_head == "Continue" and len(app_args) == 1:
        head, targs = _parse_top_level_application(_strip_wrapping_parens(type_expr))
        if head == "early_result" and len(targs) >= 2:
            env[app_args[0]] = targs[0]
        return env
    if app_head == "ReturnNow" and len(app_args) == 1:
        head, targs = _parse_top_level_application(_strip_wrapping_parens(type_expr))
        if head == "early_result" and len(targs) >= 2:
            env[app_args[0]] = targs[1]
        return env
    if app_head == "by_continue" and len(app_args) == 1:
        head, targs = _parse_top_level_application(_strip_wrapping_parens(type_expr))
        if head == "CntOrBrk" and len(targs) >= 2:
            env[app_args[0]] = targs[0]
        return env
    if app_head == "by_break" and len(app_args) == 1:
        head, targs = _parse_top_level_application(_strip_wrapping_parens(type_expr))
        if head == "CntOrBrk" and len(targs) >= 2:
            env[app_args[0]] = targs[1]
        return env

    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", stripped):
        env[stripped] = _strip_wrapping_parens(type_expr)
    return env


def _infer_monadic_result_type(type_expr: Optional[str]) -> Optional[str]:
    if not type_expr:
        return None
    head, args = _parse_top_level_application(_strip_wrapping_parens(type_expr))
    if head == "MONAD" and args:
        return args[-1]
    if head == "program" and len(args) >= 2:
        return args[-1]
    return None


def _infer_named_return_type(signature: Optional[str]) -> Optional[str]:
    if not signature:
        return None
    parts = _split_top_level_arrow_type(signature)
    if not parts:
        return None
    return _infer_monadic_result_type(parts[-1])


def _infer_application_result_type(
    head: str,
    args: List[str],
    type_env: Dict[str, str],
    blocks: Dict[str, DefinitionBlock],
) -> Optional[str]:
    if head in type_env:
        type_expr = type_env[head]
        parts = _split_top_level_arrow_type(type_expr)
        if len(parts) > len(args):
            remainder = parts[len(args):]
            return " -> ".join(remainder)
        if len(parts) == len(args):
            return parts[-1]

    block = blocks.get(head)
    if block is not None and block.signature:
        parts = _split_top_level_arrow_type(block.signature)
        if len(parts) > len(args):
            remainder = parts[len(args):]
            return " -> ".join(remainder)
        if len(parts) == len(args) + 1:
            return parts[-1]

    if head in {"return", "ret"} and args:
        arg_type = _infer_expression_type(args[0], type_env, blocks)
        return f"MONAD {arg_type}" if arg_type else None

    if head == "repeat_break" and len(args) >= 2:
        body_result = _infer_application_result_type(args[0], [args[1]], type_env, blocks)
        monadic = _infer_monadic_result_type(body_result)
        if monadic:
            inner_head, inner_args = _parse_top_level_application(_strip_wrapping_parens(monadic))
            if inner_head == "CntOrBrk" and len(inner_args) >= 2:
                return f"MONAD {inner_args[1]}"
        return None

    return None


def _infer_expression_type(
    expr: str,
    type_env: Dict[str, str],
    blocks: Dict[str, DefinitionBlock],
) -> Optional[str]:
    expr = _strip_wrapping_parens(expr.strip())
    if expr in type_env:
        return type_env[expr]

    tuple_parts = _split_top_level_tuple_pattern(expr)
    if tuple_parts is not None:
        part_types = [
            _infer_expression_type(part, type_env, blocks)
            for part in tuple_parts
        ]
        if all(part_types):
            return "(" + " * ".join(part_types) + ")"

    head, args = _parse_top_level_application(expr)
    if head:
        return _infer_application_result_type(head, args, type_env, blocks)

    return None


def _infer_initial_type_environment(block: DefinitionBlock) -> Dict[str, str]:
    env: Dict[str, str] = {}
    parsed_fun = _parse_leading_fun(_strip_terminal_period(block.body))
    if parsed_fun is None or not block.signature:
        return env

    binder_part, _ = parsed_fun
    type_parts = _split_top_level_arrow_type(block.signature)
    if len(type_parts) < 2:
        return env

    arg_types = type_parts[:-1]
    binders = [part for part in binder_part.split() if part]
    if binders and all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", binder) for binder in binders):
        for binder, binder_type in zip(binders, arg_types):
            env[binder] = binder_type
        return env

    env = _bind_pattern_types(binder_part, arg_types[0], env)
    return env


def _propagate_argument_types_from_signature(
    block: DefinitionBlock,
    args: List[str],
    type_env: Dict[str, str],
) -> Dict[str, str]:
    if not block.signature:
        return dict(type_env)

    arg_types = _split_top_level_arrow_type(block.signature)[:-1]
    if not arg_types:
        return dict(type_env)

    updated = dict(type_env)
    for arg, arg_type in zip(args, arg_types):
        stripped = _strip_wrapping_parens(arg)
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", stripped) and stripped not in updated:
            updated[stripped] = arg_type
    return updated


def _apply_named_definition(block: DefinitionBlock, args: List[str]) -> str:
    body = _strip_terminal_period(block.body)
    parsed_fun = _parse_leading_fun(body)
    if parsed_fun is None:
        if not args:
            return body
        return f"{_strip_wrapping_parens(body)} {' '.join(args)}"

    binder_part, inner_body = parsed_fun
    simple_binders = [part for part in binder_part.split() if part]
    all_simple = bool(simple_binders) and all(
        re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", binder) for binder in simple_binders
    )

    remaining_args = list(args)
    result = inner_body
    if all_simple:
        consumed = 0
        for binder in simple_binders:
            if not remaining_args:
                break
            arg = remaining_args.pop(0)
            result = _freshen_bound_identifiers(result, set(_extract_identifiers(arg)))
            result = _substitute_identifier(result, binder, _strip_wrapping_parens(arg))
            consumed += 1

        leftover_binders = simple_binders[consumed:]
        if leftover_binders:
            result = f"fun {' '.join(leftover_binders)} => {result}"
    else:
        if remaining_args:
            arg = remaining_args.pop(0)
            result = f"let {binder_part} := {_strip_wrapping_parens(arg)} in {result}"
        else:
            result = f"fun {binder_part} => {result}"

    if remaining_args:
        result = f"{_strip_wrapping_parens(result)} {' '.join(remaining_args)}"
    return result


def _split_top_level_bind(expr: str) -> Optional[Tuple[str, str, str]]:
    expr = _strip_wrapping_parens(expr)
    depth = 0
    match_depth = 0
    let_depth = 0
    bind_index = -1
    sep_index = -1

    idx = 0
    while idx < len(expr):
        ch = expr[idx]
        if ch in "([{":
            depth += 1
            idx += 1
            continue
        if ch in ")]}":
            depth = max(0, depth - 1)
            idx += 1
            continue
        if depth == 0:
            if _match_keyword_at(expr, idx, "match"):
                match_depth += 1
                idx += len("match")
                continue
            if _match_keyword_at(expr, idx, "end") and match_depth > 0:
                match_depth -= 1
                idx += len("end")
                continue
            if _match_keyword_at(expr, idx, "let"):
                let_depth += 1
                idx += len("let")
                continue
            if _match_keyword_at(expr, idx, "in") and let_depth > 0:
                let_depth -= 1
                idx += len("in")
                continue
            if match_depth == 0 and let_depth == 0 and bind_index == -1 and expr[idx:idx + 2] == "<-":
                bind_index = idx
                idx += 2
                continue
            if match_depth == 0 and let_depth == 0 and bind_index != -1 and expr[idx:idx + 2] == ";;":
                sep_index = idx
                break
        idx += 1

    if bind_index == -1 or sep_index == -1:
        return None

    binder = expr[:bind_index].strip()
    left = expr[bind_index + 2:sep_index].strip()
    right = expr[sep_index + 2:].strip()
    if _is_simple_identifier(binder):
        return binder, left, right
    if _split_top_level_tuple_pattern(binder) is not None:
        return binder, left, right
    return None


def _split_top_level_sequence(expr: str) -> Optional[Tuple[str, str]]:
    expr = _strip_wrapping_parens(expr)
    depth = 0
    match_depth = 0
    let_depth = 0

    idx = 0
    while idx < len(expr):
        ch = expr[idx]
        if ch in "([{":
            depth += 1
            idx += 1
            continue
        if ch in ")]}":
            depth = max(0, depth - 1)
            idx += 1
            continue
        if depth == 0:
            if _match_keyword_at(expr, idx, "match"):
                match_depth += 1
                idx += len("match")
                continue
            if _match_keyword_at(expr, idx, "end") and match_depth > 0:
                match_depth -= 1
                idx += len("end")
                continue
            if _match_keyword_at(expr, idx, "let"):
                let_depth += 1
                idx += len("let")
                continue
            if _match_keyword_at(expr, idx, "in") and let_depth > 0:
                let_depth -= 1
                idx += len("in")
                continue
            if match_depth == 0 and let_depth == 0 and expr[idx:idx + 2] == ";;":
                left = expr[:idx].strip()
                right = expr[idx + 2:].strip()
                if left and right:
                    return left, right
                return None
        idx += 1
    return None


def _split_top_level_let(expr: str) -> Optional[Tuple[str, str, str]]:
    expr = _strip_wrapping_parens(expr)
    if not _match_keyword_at(expr, 0, "let"):
        return None

    depth = 0
    match_depth = 0
    let_depth = 0
    assign_index = -1
    in_index = -1

    idx = len("let")
    while idx < len(expr):
        ch = expr[idx]
        if ch in "([{":
            depth += 1
            idx += 1
            continue
        if ch in ")]}":
            depth = max(0, depth - 1)
            idx += 1
            continue
        if depth == 0:
            if _match_keyword_at(expr, idx, "match"):
                match_depth += 1
                idx += len("match")
                continue
            if _match_keyword_at(expr, idx, "end") and match_depth > 0:
                match_depth -= 1
                idx += len("end")
                continue
            if _match_keyword_at(expr, idx, "let"):
                let_depth += 1
                idx += len("let")
                continue
            if expr[idx:idx + 2] == ":=" and match_depth == 0 and let_depth == 0 and assign_index == -1:
                assign_index = idx
                idx += 2
                continue
            if _match_keyword_at(expr, idx, "in"):
                if let_depth > 0:
                    let_depth -= 1
                    idx += len("in")
                    continue
                if match_depth == 0 and assign_index != -1:
                    in_index = idx
                    break
        idx += 1

    if assign_index == -1 or in_index == -1:
        return None

    pattern = expr[len("let"):assign_index].strip()
    value = expr[assign_index + 2:in_index].strip()
    body = expr[in_index + len("in"):].strip()
    if not pattern or not value or not body:
        return None
    return pattern, value, body


def _compose_with_continuation(expr: str, cont: Optional[Continuation]) -> str:
    expr = _strip_terminal_period(expr)
    if cont is None:
        return expr
    cont = _freshen_continuation(cont, set(_extract_identifiers(expr)))
    return f"{cont.binder} <- {_strip_wrapping_parens(expr)};;\n{cont.body}"


def _prepend_sequence_to_continuation(expr: str, cont: Optional[Continuation]) -> Optional[Continuation]:
    expr = _strip_terminal_period(expr)
    if cont is None:
        return Continuation(binder="_", body=expr)
    cont = _freshen_continuation(cont, set(_extract_identifiers(expr)))
    return Continuation(
        binder=cont.binder,
        body=f"{expr};;\n{cont.body}",
    )


def _contains_callee(expr: str, callee_M: str) -> bool:
    return re.search(rf"\b{re.escape(callee_M)}\b", expr) is not None


def _collect_locally_bound_identifiers(body: str) -> Set[str]:
    bound: Set[str] = set()
    _collect_bound_recursive(body, bound)
    return bound


def _collect_bound_recursive(expr: str, bound: Set[str]) -> None:
    expr = _strip_terminal_period(_strip_wrapping_parens(expr.strip()))

    # Bind: x <- m ;; k
    bind_parts = _split_top_level_bind(expr)
    if bind_parts is not None:
        binder, left, right = bind_parts
        if _is_simple_identifier(binder):
            bound.add(binder)
        else:
            bound.update(_collect_pattern_bound_identifiers(binder))
        _collect_bound_recursive(left, bound)
        _collect_bound_recursive(right, bound)
        return

    # Let: let p := v in k
    let_parts = _split_top_level_let(expr)
    if let_parts is not None:
        pattern, value, let_body = let_parts
        bound.update(_collect_pattern_bound_identifiers(pattern))
        _collect_bound_recursive(value, bound)
        _collect_bound_recursive(let_body, bound)
        return

    # Sequence: m1 ;; m2
    seq_parts = _split_top_level_sequence(expr)
    if seq_parts is not None:
        left, right = seq_parts
        _collect_bound_recursive(left, bound)
        _collect_bound_recursive(right, bound)
        return

    # Match: match e with | p => b end
    match_parts = _parse_top_level_match(expr)
    if match_parts is not None:
        _, branches = match_parts
        for pattern, branch_body in branches:
            bound.update(_collect_pattern_bound_identifiers(pattern))
            _collect_bound_recursive(branch_body, bound)
        return

    # Fun: fun x => k
    parsed_fun = _parse_leading_fun(expr)
    if parsed_fun is not None:
        binder_part, fun_body = parsed_fun
        bound.update(_collect_pattern_bound_identifiers(binder_part))
        _collect_bound_recursive(fun_body, bound)
        return


def _extract_captured_identifiers(
    binder: str,
    body: str,
    blocks: Dict[str, DefinitionBlock],
    callee_M: str,
) -> List[str]:
    reserved = {
        binder,
        callee_M,
        "fun",
        "match",
        "with",
        "end",
        "return",
        "ret",
        "choice",
        "repeat_break",
        "continue",
        "break",
        "assume",
        "let",
        "in",
        "Continue",
        "ReturnNow",
        "by_continue",
        "by_break",
        "nil",
        "true",
        "false",
    }
    reserved.update(blocks.keys())
    reserved.update(_collect_locally_bound_identifiers(body))

    captured: List[str] = []
    for name in _extract_identifiers(body):
        if name in reserved:
            continue
        if name not in captured:
            captured.append(name)
    return captured


def _extract_captured_identifier_types(
    captured_identifiers: List[str],
    type_env: Dict[str, str],
) -> Dict[str, str]:
    return {
        name: type_env[name]
        for name in captured_identifiers
        if name in type_env
    }


def _render_residual_result_type(
    callee_return_type: Optional[str],
    caller_return_type: Optional[str],
) -> str:
    if not callee_return_type or not caller_return_type:
        return ""
    rendered_callee = _strip_wrapping_parens(callee_return_type)
    rendered_caller = _strip_wrapping_parens(caller_return_type)
    return f" : {rendered_callee} -> MONAD ({rendered_caller})"


def _render_residual_definition(
    caller_component: str,
    call_index: int,
    binder: str,
    body: str,
    callee_return_type: Optional[str] = None,
    caller_return_type: Optional[str] = None,
) -> str:
    return "\n".join(
        [
            (
                f"Definition residual_prog_in_{caller_component}_call_{call_index}"
                f"{_render_residual_result_type(callee_return_type, caller_return_type)} :="
            ),
            f"  fun {binder} =>",
            f"    {body}.",
        ]
    )


def _build_residual_segment(
    caller_component: str,
    call_index: int,
    cont: Optional[Continuation],
    callee_return_type: Optional[str],
    caller_return_type: Optional[str],
    origin_component: str,
    origin_start: int,
) -> ResidualSegment:
    if cont is None:
        body = "return r"
        binder = "r"
    else:
        body = _strip_terminal_period(cont.body)
        binder = cont.binder
    definition = _render_residual_definition(
        caller_component,
        call_index,
        binder,
        body,
        callee_return_type,
        caller_return_type,
    )
    return ResidualSegment(
        caller_component=caller_component,
        call_index=call_index,
        binder=binder,
        body=body,
        definition=definition,
        captured_identifiers=[],
        captured_identifier_types={},
        callee_return_type=callee_return_type,
        caller_return_type=caller_return_type,
        origin_component=origin_component,
        origin_start=origin_start,
    )


def _render_polished_residual_definition(
    caller_component: str,
    call_index: int,
    binder: str,
    body: str,
    callee_return_type: Optional[str],
    caller_return_type: Optional[str],
) -> str:
    return _render_residual_definition(
        caller_component,
        call_index,
        binder,
        body,
        callee_return_type,
        caller_return_type,
    )


def _simplify_residual_body(expr: str) -> str:
    expr = _strip_terminal_period(expr)
    bind_parts = _split_top_level_bind(expr)
    if bind_parts is not None:
        binder, left, right = bind_parts
        simplified_left = _simplify_residual_body(left)
        simplified_right = _simplify_residual_body(right)
        head, args = _parse_top_level_application(simplified_left)
        if head == "return" and args:
            replacement = " ".join(args)
            simplified_right = _freshen_bound_identifiers(
                simplified_right,
                set(_extract_identifiers(replacement)),
            )
            substituted = _substitute_identifier_scoped(
                simplified_right,
                binder,
                replacement,
            )
            return _simplify_residual_body(substituted)
        return f"{binder} <- {simplified_left};;\n{simplified_right}"

    seq_parts = _split_top_level_sequence(expr)
    if seq_parts is not None:
        left, right = seq_parts
        return f"{_simplify_residual_body(left)};;\n{_simplify_residual_body(right)}"

    return expr


def polish_residual_segment(entry: ResidualSegment) -> ResidualSegment:
    """Apply first-stage simplifications to a residual segment."""

    polished_body = _simplify_residual_body(entry.body)
    polished_definition = _render_polished_residual_definition(
        entry.caller_component,
        entry.call_index,
        entry.binder,
        polished_body,
        entry.callee_return_type,
        entry.caller_return_type,
    )
    return ResidualSegment(
        caller_component=entry.caller_component,
        call_index=entry.call_index,
        binder=entry.binder,
        body=polished_body,
        definition=polished_definition,
        captured_identifiers=list(entry.captured_identifiers),
        captured_identifier_types=dict(entry.captured_identifier_types),
        callee_return_type=entry.callee_return_type,
        caller_return_type=entry.caller_return_type,
        origin_component=entry.origin_component,
        origin_start=entry.origin_start,
    )


def _collect_residuals(
    expr: str,
    callee_M: str,
    caller_component: str,
    blocks: Dict[str, DefinitionBlock],
    named_signatures: Dict[str, str],
    type_env: Dict[str, str],
    cont: Optional[Continuation],
    out: List[ResidualSegment],
    position_ref: List[int],
    origin_component: str,
    origin_start: int,
    seen_defs: Optional[Set[str]] = None,
) -> None:
    if seen_defs is None:
        seen_defs = set()
    expr = _strip_terminal_period(_strip_wrapping_parens(expr))

    # Peel leading fun layers, recording binder types into type_env.
    # Determine available arg types from the origin component signature.
    sig = named_signatures.get(origin_component)
    sig_arg_types = _split_top_level_arrow_type(sig)[:-1] if sig else []
    consumed_args = 0
    while True:
        parsed = _parse_leading_fun(expr)
        if parsed is None:
            break
        binder_part, inner = parsed
        if consumed_args < len(sig_arg_types):
            # Simple curried binders: fun a b => ...
            simple_binders = [p for p in binder_part.split() if p]
            if simple_binders and all(
                re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", b) for b in simple_binders
            ):
                for b in simple_binders:
                    if consumed_args < len(sig_arg_types):
                        type_env = dict(type_env)
                        type_env[b] = sig_arg_types[consumed_args]
                        consumed_args += 1
            else:
                # Tuple/pattern binder
                if consumed_args < len(sig_arg_types):
                    type_env = _bind_pattern_types(
                        binder_part, sig_arg_types[consumed_args], dict(type_env),
                    )
                    consumed_args += 1
        expr = inner
    bind_parts = _split_top_level_bind(expr)

    if bind_parts is not None:
        binder, left, right = bind_parts
        if not _is_simple_identifier(binder):
            # Tuple-destructuring bind: desugar '(x,y) <- m ;; k
            # into: v <- m ;; let '(x,y) := v in k
            all_idents = set(_extract_identifiers(right))
            if cont is not None:
                all_idents.update(_extract_identifiers(cont.body))
            fresh = _fresh_identifier("v", all_idents)
            desugared = f"{fresh} <- {left};;\nlet {binder} := {fresh} in {right}"
            _collect_residuals(
                desugared,
                callee_M,
                caller_component,
                blocks,
                named_signatures,
                type_env,
                cont,
                out,
                position_ref,
                origin_component,
                origin_start,
                seen_defs.copy(),
            )
            return
        left_cont = Continuation(
            binder=binder,
            body=_compose_with_continuation(right, cont),
        )
        _collect_residuals(
            left,
            callee_M,
            caller_component,
            blocks,
            named_signatures,
            type_env,
            left_cont,
            out,
            position_ref,
            origin_component,
            origin_start,
            seen_defs.copy(),
        )
        binder_type = _infer_monadic_result_type(
            _infer_expression_type(left, type_env, blocks)
        )
        right_env = dict(type_env)
        if binder_type:
            right_env[binder] = binder_type
        _collect_residuals(
            right,
            callee_M,
            caller_component,
            blocks,
            named_signatures,
            right_env,
            cont,
            out,
            position_ref,
            origin_component,
            origin_start,
            seen_defs.copy(),
        )
        return

    let_parts = _split_top_level_let(expr)
    if let_parts is not None:
        pattern, value, body = let_parts
        value_binder = _fresh_identifier(
            "v",
            set(_extract_identifiers(body)).union(
                set() if cont is None else set(_extract_identifiers(cont.body))
            ),
        )
        value_cont = Continuation(
            binder=value_binder,
            body=f"let {pattern} := {value_binder} in {_compose_with_continuation(body, cont)}",
        )
        _collect_residuals(
            value,
            callee_M,
            caller_component,
            blocks,
            named_signatures,
            type_env,
            value_cont,
            out,
            position_ref,
            origin_component,
            origin_start,
            seen_defs.copy(),
        )
        body_env = _bind_pattern_types(
            pattern,
            _infer_expression_type(value, type_env, blocks),
            type_env,
        )
        _collect_residuals(
            body,
            callee_M,
            caller_component,
            blocks,
            named_signatures,
            body_env,
            cont,
            out,
            position_ref,
            origin_component,
            origin_start,
            seen_defs.copy(),
        )
        return

    seq_parts = _split_top_level_sequence(expr)
    if seq_parts is not None:
        left, right = seq_parts
        right_cont = _prepend_sequence_to_continuation(right, cont)
        _collect_residuals(
            left,
            callee_M,
            caller_component,
            blocks,
            named_signatures,
            type_env,
            right_cont,
            out,
            position_ref,
            origin_component,
            origin_start,
            seen_defs.copy(),
        )
        _collect_residuals(
            right,
            callee_M,
            caller_component,
            blocks,
            named_signatures,
            type_env,
            cont,
            out,
            position_ref,
            origin_component,
            origin_start,
            seen_defs.copy(),
        )
        return

    match_parts = _parse_top_level_match(expr)
    if match_parts is not None:
        scrutinee, branches = match_parts
        scrutinee_type = _infer_expression_type(scrutinee, type_env, blocks)
        for pattern, branch in branches:
            branch_env = _bind_pattern_types(pattern, scrutinee_type, type_env)
            _collect_residuals(
                branch,
                callee_M,
                caller_component,
                blocks,
                named_signatures,
                branch_env,
                cont,
                out,
                position_ref,
                origin_component,
                origin_start,
                seen_defs.copy(),
            )
        return

    head, args = _parse_top_level_application(expr)
    if head == "choice" and len(args) >= 2:
        _collect_residuals(
            args[0],
            callee_M,
            caller_component,
            blocks,
            named_signatures,
            type_env,
            cont,
            out,
            position_ref,
            origin_component,
            origin_start,
            seen_defs.copy(),
        )
        _collect_residuals(
            args[1],
            callee_M,
            caller_component,
            blocks,
            named_signatures,
            type_env,
            cont,
            out,
            position_ref,
            origin_component,
            origin_start,
            seen_defs.copy(),
        )
        return

    if head == "repeat_break" and len(args) >= 2:
        body_name = args[0]
        init_arg = args[1]
        step_binder = "step"
        loop_expr = (
            f"match {step_binder} with\n"
            f"        | by_continue a' => repeat_break {body_name} a'\n"
            f"        | by_break b => ret b\n"
            f"        end"
        )
        if cont is None:
            repeat_cont = Continuation(binder=step_binder, body=loop_expr)
        else:
            repeat_cont = Continuation(
                binder=step_binder,
                body=f"{cont.binder} <- {loop_expr};;\n{cont.body}",
            )
        unfolded = f"{body_name} {init_arg}"
        _collect_residuals(
            unfolded,
            callee_M,
            caller_component,
            blocks,
            named_signatures,
            type_env,
            repeat_cont,
            out,
            position_ref,
            origin_component,
            origin_start,
            seen_defs.copy(),
        )
        return

    if head and head in blocks and head not in seen_defs:
        next_seen = seen_defs.copy()
        next_seen.add(head)
        unfolded = _apply_named_definition(blocks[head], args)
        unfolded_env = _propagate_argument_types_from_signature(
            blocks[head],
            args,
            type_env,
        )
        _collect_residuals(
            unfolded,
            callee_M,
            caller_component,
            blocks,
            named_signatures,
            unfolded_env,
            cont,
            out,
            position_ref,
            head,
            blocks[head].start,
            next_seen,
        )
        return

    if _contains_callee(expr, callee_M):
        segment = _build_residual_segment(
            caller_component,
            position_ref[0],
            cont,
            _infer_named_return_type(named_signatures.get(callee_M)),
            _infer_named_return_type(named_signatures.get(caller_component)),
            origin_component,
            origin_start,
        )
        segment.captured_identifiers = _extract_captured_identifiers(
            segment.binder,
            segment.body,
            blocks,
            callee_M,
        )
        segment.captured_identifier_types = _extract_captured_identifier_types(
            segment.captured_identifiers,
            type_env,
        )
        out.append(segment)
        position_ref[0] += 1


def generate_func_residual_entries(
    coqfilepath: str,
    callee_M: str,
    caller_component: str,
    extra_signatures: Optional[Dict[str, str]] = None,
) -> List[ResidualSegment]:
    """Generate first-stage residual entries for each call to ``callee_M`` in ``caller_component``.

    This stage only follows bind structure:
    - start from ``Definition caller_component := ...``
    - for ``x <- m1 ;; m2``, recurse into ``m1`` with residual ``fun x => m2``
      composed with the outer continuation
    - recurse into ``m2`` with the outer continuation unchanged
    - if a leaf expression contains ``callee_M``, emit the copied residual and
      record which identifiers are captured from the surrounding context

    *extra_signatures* lets callers supply signatures for names that are only
    visible via ``Require Import``, not declared in the assembled file
    (e.g. cross-file callees).  Local Definitions/Parameters override.
    """

    with open(coqfilepath, "r", encoding="utf-8") as handle:
        text = handle.read()

    blocks = _parse_definition_blocks(text)
    named_signatures: Dict[str, str] = dict(extra_signatures or {})
    named_signatures.update({
        name: block.signature
        for name, block in blocks.items()
        if block.signature
    })
    named_signatures.update(_parse_parameter_signatures(text))
    caller_block = blocks.get(caller_component)
    if caller_block is None:
        raise ValueError(f"Could not find Definition {caller_component} in {coqfilepath}")

    residuals: List[ResidualSegment] = []
    position_ref = [1]
    initial_type_env = _infer_initial_type_environment(caller_block)
    _collect_residuals(
        caller_block.body,
        callee_M,
        caller_component,
        blocks,
        named_signatures,
        initial_type_env,
        None,
        residuals,
        position_ref,
        caller_component,
        caller_block.start,
    )
    return residuals


def generate_func_residual_segments(
    coqfilepath: str,
    callee_M: str,
    caller_component: str,
) -> List[str]:
    """Backward-compatible string-only wrapper around residual entry generation."""

    return [
        entry.definition
        for entry in generate_func_residual_entries(coqfilepath, callee_M, caller_component)
    ]


def append_func_residual_definitions(
    coqfilepath: str,
    callee_M: str,
    caller_component: str,
    polish: bool = True,
) -> List[str]:
    """Append promoted residual definitions for ``callee_M`` in ``caller_component`` to a Coq file."""

    entries = generate_func_residual_entries(coqfilepath, callee_M, caller_component)
    if polish:
        entries = [polish_residual_segment(entry) for entry in entries]
    definitions = [
        promote_captured_identifiers_to_arguments(
            entry.definition,
            entry.captured_identifiers,
            entry.captured_identifier_types,
        )
        for entry in entries
    ]
    if not definitions:
        return []

    with open(coqfilepath, "r", encoding="utf-8") as handle:
        original = handle.read()

    new_content = original.rstrip() + "\n\n" + "\n\n".join(definitions) + "\n"

    with open(coqfilepath, "w", encoding="utf-8") as handle:
        handle.write(new_content)

    return definitions
