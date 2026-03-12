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

        Args:
            text: The text to search in
            start_pos: Position to start searching from

        Returns:
            Tuple of (comment_content, end_position) or None if not found
        """
        # Find /*@
        comment_start = text.find('/*@', start_pos)
        if comment_start == -1:
            return None

        # Find matching */
        comment_end = text.find('*/', comment_start)
        if comment_end == -1:
            return None

        # Extract content between /*@ and */
        content = text[comment_start + 3:comment_end].strip()
        return content, comment_end + 2

    def process_funcspec(self, text: str, func_name: str) -> Optional[Dict[str, str]]:
        """Extract function specification annotation.

        This extracts the annotation that appears after the function declaration,
        typically containing Require, Ensure, and With clauses.

        Args:
            text: The C file content
            func_name: Name of the function to find

        Returns:
            Dictionary with 'with', 'require', 'ensure' keys, or None if not found
        """
        # Find the function declaration
        # Pattern: return_type func_name(params)
        func_pattern = rf'\b{re.escape(func_name)}\s*\([^)]*\)'
        match = re.search(func_pattern, text)

        if not match:
            return None

        # Look for /*@ comment after the function declaration
        func_end = match.end()
        result = self.extract_comment_block(text, func_end)

        if not result:
            return None

        comment_content, _ = result

        # Parse the comment content for With, Require, Ensure
        spec = {
            'with': None,
            'require': None,
            'ensure': None
        }

        # Extract With clause
        with_match = re.search(r'With\s+(.*?)(?=Require|Ensure|$)', comment_content, re.DOTALL | re.IGNORECASE)
        if with_match:
            spec['with'] = with_match.group(1).strip()

        # Extract Require clause
        require_match = re.search(r'Require\s+(.*?)(?=Ensure|$)', comment_content, re.DOTALL | re.IGNORECASE)
        if require_match:
            spec['require'] = require_match.group(1).strip()

        # Extract Ensure clause
        ensure_match = re.search(r'Ensure\s+(.*?)$', comment_content, re.DOTALL | re.IGNORECASE)
        if ensure_match:
            spec['ensure'] = ensure_match.group(1).strip()

        return spec

    def extract_while_condition(self, text: str, start_pos: int) -> Optional[str]:
        """Extract the while loop condition that follows an INV assertion.

        Args:
            text: The text to search in
            start_pos: Position to start searching from (after the comment)

        Returns:
            The while condition (expression inside the parentheses) or None
        """
        # Skip whitespace and find 'while'
        remaining = text[start_pos:]
        while_match = re.search(r'\s*while\s*\(', remaining)

        if not while_match:
            return None

        # Find the opening parenthesis position
        open_paren_pos = while_match.end() - 1

        # Extract the condition by matching parentheses
        paren_count = 1
        i = open_paren_pos + 1

        while i < len(remaining) and paren_count > 0:
            if remaining[i] == '(':
                paren_count += 1
            elif remaining[i] == ')':
                paren_count -= 1
            i += 1

        if paren_count == 0:
            # Extract the condition between the parentheses
            condition = remaining[open_paren_pos + 1:i - 1].strip()
            return condition

        return None

    def process_innerassertion(self, text: str, func_name: str) -> List[Dict[str, str]]:
        """Extract inner assertions from function body.

        This extracts annotations that appear inside the function body,
        typically loop invariants marked with /*@ Inv ... */.
        For Inv assertions, also extracts the while loop condition (command guard).

        Args:
            text: The C file content
            func_name: Name of the function

        Returns:
            List of dictionaries, each containing assertion info
        """
        # Find the function body (between { and })
        func_pattern = rf'\b{re.escape(func_name)}\s*\([^)]*\)[^{{]*\{{(.*?)\n\}}'
        match = re.search(func_pattern, text, re.DOTALL)

        if not match:
            return []

        func_body = match.group(1)
        func_body_start = match.start(1)

        # Extract all /*@ ... */ comments in the function body
        assertions = []
        pos = 0

        while True:
            result = self.extract_comment_block(func_body, pos)
            if not result:
                break

            content, end_pos = result

            # Determine the type of assertion (Inv, etc.)
            assertion_type = 'unknown'
            assertion_content = content
            command_guard = None

            # Check for Inv keyword
            inv_match = re.match(r'Inv\s+(.*)', content, re.DOTALL | re.IGNORECASE)
            if inv_match:
                assertion_type = 'Inv'
                assertion_content = inv_match.group(1).strip()

                # Extract the while condition that follows this INV
                command_guard = self.extract_while_condition(func_body, end_pos)

            assertion_dict = {
                'type': assertion_type,
                'content': assertion_content,
                'position': func_body_start + pos
            }

            # Add command_guard only for Inv assertions
            if assertion_type == 'Inv' and command_guard:
                assertion_dict['command_guard'] = command_guard

            assertions.append(assertion_dict)

            pos = end_pos

        return assertions

    def process_file(self, file_path: str) -> Dict:
        """Process a single C file.

        Args:
            file_path: Path to the C file

        Returns:
            Dictionary containing extracted annotations
        """
        # Get function name from file name (xxx.c -> xxx)
        file_name = os.path.basename(file_path)
        func_name = os.path.splitext(file_name)[0]

        # Read file content
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            return {
                'file': file_path,
                'function': func_name,
                'error': str(e)
            }

        # Extract function specification
        func_spec = self.process_funcspec(content, func_name)

        # Extract inner assertions
        inner_assertions = self.process_innerassertion(content, func_name)

        return {
            'file': file_path,
            'function': func_name,
            'funcspec': func_spec,
            'inner_assertions': inner_assertions
        }

    def process_directory(self, directory: str) -> Dict[str, Dict]:
        """Process all C files in a directory.

        Args:
            directory: Path to directory containing C files

        Returns:
            Dictionary mapping file names to their extracted annotations
        """
        results = {}

        # Find all .c files
        for root, dirs, files in os.walk(directory):
            for file in files:
                if file.endswith('.c'):
                    file_path = os.path.join(root, file)
                    result = self.process_file(file_path)
                    results[file] = result

        return results


def format_result(result: Dict) -> str:
    """Format a single result for display.

    Args:
        result: Result dictionary from process_file

    Returns:
        Formatted string
    """
    lines = []
    lines.append("=" * 80)
    lines.append(f"File: {result['file']}")
    lines.append(f"Function: {result['function']}")
    lines.append("=" * 80)

    if 'error' in result:
        lines.append(f"ERROR: {result['error']}")
        return '\n'.join(lines)

    # Function specification
    if result['funcspec']:
        lines.append("\nFunction Specification:")
        lines.append("-" * 40)

        spec = result['funcspec']
        if spec['with']:
            lines.append(f"With: {spec['with']}")
        if spec['require']:
            lines.append(f"Require: {spec['require']}")
        if spec['ensure']:
            lines.append(f"Ensure: {spec['ensure']}")
    else:
        lines.append("\nFunction Specification: Not found")

    # Inner assertions
    lines.append("\nInner Assertions:")
    lines.append("-" * 40)

    if result['inner_assertions']:
        for i, assertion in enumerate(result['inner_assertions'], 1):
            lines.append(f"\n{i}. Type: {assertion['type']}")
            lines.append(f"   Content: {assertion['content']}")
    else:
        lines.append("No inner assertions found")

    lines.append("")
    return '\n'.join(lines)


