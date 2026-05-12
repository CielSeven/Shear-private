"""
Preprocessor for C files with shape assertion annotations.

This module extracts function specifications and inner assertions from C files
in the shape_invdataset directory.
"""

import re
import os
from typing import Dict, List, Tuple, Optional
from pathlib import Path


class AnnotationExtractor:
    """Extracts annotations from C files."""

    def __init__(self):
        self.results = {}

    def extract_comment_block(self, text: str, start_pos: int) -> Optional[Tuple[str, int]]:
        """Extract a comment block starting with /*@ and ending with */.
        """
        comment_start = text.find('/*@', start_pos)
        if comment_start == -1:
            return None

        comment_end = text.find('*/', comment_start)
        if comment_end == -1:
            return None

        content = text[comment_start + 3:comment_end].strip()
        return content, comment_end + 2

    def process_funcspec(self, text: str, func_name: str) -> Optional[Dict[str, str]]:
        """Original extraction logic for funcspec."""
        func_pattern = rf'\b{re.escape(func_name)}\s*\([^)]*\)'
        match = re.search(func_pattern, text)
        if not match: return None
        func_end = match.end()
        result = self.extract_comment_block(text, func_end)
        if not result: return None
        comment_content, _ = result
        return self.parse_spec_content(comment_content)

    def parse_spec_content(self, comment_content: str) -> Dict[str, str]:
        """Parse the comment content for With, Require, Ensure.
        """
        spec = {
            'with': None,
            'require': None,
            'ensure': None
        }

        with_match = re.search(r'With\s+(.*?)(?=Require|Ensure|$)', comment_content, re.DOTALL | re.IGNORECASE)
        if with_match:
            spec['with'] = with_match.group(1).strip()

        require_match = re.search(r'Require\s+(.*?)(?=Ensure|$)', comment_content, re.DOTALL | re.IGNORECASE)
        if require_match:
            spec['require'] = require_match.group(1).strip()

        ensure_match = re.search(r'Ensure\s+(.*?)$', comment_content, re.DOTALL | re.IGNORECASE)
        if ensure_match:
            spec['ensure'] = ensure_match.group(1).strip()

        return spec

    def extract_while_condition(self, text: str, start_pos: int) -> Optional[str]:
        """Extract the while loop condition that follows an INV assertion.
        """
        remaining = text[start_pos:]
        while_match = re.search(r'\s*\bwhile\b\s*\(', remaining)

        if not while_match:
            return None

        open_paren_pos = while_match.end() - 1
        paren_count = 1
        i = open_paren_pos + 1

        while i < len(remaining) and paren_count > 0:
            if remaining[i] == '(':
                paren_count += 1
            elif remaining[i] == ')':
                paren_count -= 1
            i += 1

        if paren_count == 0:
            condition = remaining[open_paren_pos + 1:i - 1].strip()
            return condition

        return None

    def process_innerassertion(self, text: str, func_name: str) -> List[Dict[str, str]]:
        """Original logic for inner assertions."""
        func_pattern = rf'\b{re.escape(func_name)}\s*\([^)]*\)[^{{]*\{{(.*?)\n\}}'
        match = re.search(func_pattern, text, re.DOTALL)
        if not match: return []
        func_body = match.group(1)
        func_body_start = match.start(1)
        return self.process_func_body(func_body, func_body_start)

    def process_func_body(self, func_body: str, body_start_pos: int) -> List[Dict[str, str]]:
        """Extract inner assertions from a function body.
        """
        assertions = []
        pos = 0

        while True:
            result = self.extract_comment_block(func_body, pos)
            if not result:
                break

            content, end_pos = result
            assertion_type = 'unknown'
            assertion_content = content
            command_guard = None

            inv_match = re.match(r'Inv\s+(.*)', content, re.DOTALL | re.IGNORECASE)
            if inv_match:
                assertion_type = 'Inv'
                assertion_content = inv_match.group(1).strip()
                command_guard = self.extract_while_condition(func_body, end_pos)

            assertion_dict = {
                'type': assertion_type,
                'content': assertion_content,
                'position': body_start_pos + pos
            }

            if assertion_type == 'Inv' and command_guard:
                assertion_dict['command_guard'] = command_guard

            assertions.append(assertion_dict)
            pos = end_pos

        return assertions

    def process_file(self, file_path: str) -> Dict:
        """Original process_file entry point with Multi-function support added."""
        file_name = os.path.basename(file_path)
        func_name = os.path.splitext(file_name)[0]

        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            return {'file': file_path, 'function': func_name, 'error': str(e)}

        # Original behavior for existing tests
        func_spec = self.process_funcspec(content, func_name)
        inner_assertions = self.process_innerassertion(content, func_name)

        # Multi-function support (New Logic)
        functions = []
        # Pattern: func_name(...) optionally followed by an annotation block, then { or ;
        pattern = (
            r'((?:\bstruct\s+)?\b[a-zA-Z_][a-zA-Z0-9_]*\s*[\s\*]*?)'
            r'\b([a-zA-Z_][a-zA-Z0-9_]*)\s*\(([^)]*)\)\s*'
            r'(/\*@.*?\*/\s*)?([;\{])'
        )

        for header_match in re.finditer(pattern, content, re.DOTALL):
            f_name = header_match.group(2)
            if f_name in ['while', 'if', 'for', 'switch', 'return']: continue

            return_type = (header_match.group(1) or "").strip()
            inline_spec = header_match.group(4)
            terminator = header_match.group(5)
            header_start, header_end = header_match.start(), header_match.end()
            
            f_spec = None
            if inline_spec:
                inline_match = re.match(r'/\*@\s*(.*?)\*/\s*$', inline_spec, re.DOTALL)
                if inline_match:
                    f_spec = self.parse_spec_content(inline_match.group(1).strip())
            else:
                # Find last annotation before this header
                prefix = content[:header_start]
                spec_matches = list(re.finditer(r'/\*@\s*(.*?)\*/', prefix, re.DOTALL))
                if spec_matches:
                    # Basic check: is there another function between this spec and its header?
                    last_spec = spec_matches[-1]
                    if not re.search(pattern, prefix[last_spec.end():], re.DOTALL):
                        f_spec = self.parse_spec_content(last_spec.group(1))
            
            f_inner = []
            if terminator == '{':
                brace_count, pos = 1, header_end
                while pos < len(content) and brace_count > 0:
                    if content[pos] == '{': brace_count += 1
                    elif content[pos] == '}': brace_count -= 1
                    pos += 1
                if brace_count == 0:
                    f_inner = self.process_func_body(content[header_end:pos-1], header_end)
            
            functions.append({
                'function': f_name,
                'return_type': return_type,
                'funcspec': f_spec,
                'inner_assertions': f_inner,
            })

        return {
            'file': file_path,
            'function': func_name,
            'funcspec': func_spec,
            'inner_assertions': inner_assertions,
            'functions': functions
        }

    def process_directory(self, directory: str) -> Dict[str, Dict]:
        results = {}
        for root, dirs, files in os.walk(directory):
            for file in files:
                if file.endswith('.c'):
                    file_path = os.path.join(root, file)
                    result = self.process_file(file_path)
                    results[file] = result
        return results

def format_result(result: Dict) -> str:
    lines = []
    lines.append("=" * 80)
    lines.append(f"File: {result['file']}")
    if 'error' in result:
        lines.append(f"ERROR: {result['error']}")
        return '\n'.join(lines)
    for func in result.get('functions', []):
        lines.append(f"\nFunction: {func['function']}")
        lines.append("-" * 40)
        spec = func['funcspec']
        if spec:
            if spec['with']: lines.append(f"With: {spec['with']}")
            if spec['require']: lines.append(f"Require: {spec['require']}")
            if spec['ensure']: lines.append(f"Ensure: {spec['ensure']}")
        if func['inner_assertions']:
            lines.append("\nInner Assertions:")
            for i, assertion in enumerate(func['inner_assertions'], 1):
                lines.append(f"  {i}. Type: {assertion['type']}")
                lines.append(f"     Content: {assertion['content']}")
    return '\n'.join(lines)
