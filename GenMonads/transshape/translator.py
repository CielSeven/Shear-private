"""
Translator for shape predicates to data predicates.

This module provides functionality to translate shape predicates by adding
existential list variables according to a predefined mapping.
"""

from typing import Dict, Tuple, List
from .parser import (
    Formula, Expr, Predicate, SepConj, AndConj, Exists, BinOp,
    Var, FieldAccess, parse_assertion, recover_assertion
)
import copy

from GenMonads.predicate_mapping import get_predicate_mappings


class ShapeTranslator:
    """Translator for shape predicates to data predicates."""

    def __init__(self):
        """Initialize the translator with predicate mappings.

        The mapping defines:
        1. How to translate shape predicate names to data predicate names
        2. How many list arguments each predicate needs

        Format: shape_predicate_name -> (data_predicate_name, num_list_args)

        Mappings are loaded from the persistent configuration file
        at GenMonads/data/predicate_mappings.json
        """
        # Load mappings from persistent config file
        self.predicate_name_mapping: Dict[str, Tuple[str, int]] = get_predicate_mappings()

        # Counter for generating unique existential variables
        self.var_counter = 0
        self.generated_vars: List[str] = []

    def reset_var_counter(self, start_from: int = 0):
        """Reset the variable counter for a new assertion.

        Args:
            start_from: Starting counter value (default: 0)
        """
        self.var_counter = start_from
        self.generated_vars = []

    def set_var_counter(self, counter: int):
        """Set the variable counter to a specific value.

        Args:
            counter: The counter value to set
        """
        self.var_counter = counter

    def get_var_counter(self) -> int:
        """Get the current variable counter value.

        Returns:
            Current counter value
        """
        return self.var_counter

    def generate_list_var(self) -> str:
        """Generate a unique existential list variable.

        Returns:
            A unique variable name like ?l1, ?l2, etc.
        """
        self.var_counter += 1
        var_name = f"?l{self.var_counter}"
        self.generated_vars.append(var_name)
        return var_name

    def translate_expr(self, expr: Expr) -> Expr:
        """Translate an expression (no changes needed).

        Args:
            expr: The expression to translate

        Returns:
            The same expression (expressions don't need translation)
        """
        return copy.deepcopy(expr)

    def translate_predicate(self, pred: Predicate) -> Predicate:
        """Translate a shape predicate to data predicate.

        This does two things:
        1. Changes the predicate name (e.g., listrep -> sll, lseg -> sllseg)
        2. Adds list arguments (e.g., ?l1, ?l2)

        Args:
            pred: The predicate to translate

        Returns:
            A new predicate with translated name and additional list arguments
        """
        # Check if this predicate needs translation
        if pred.name in self.predicate_name_mapping:
            data_name, num_lists = self.predicate_name_mapping[pred.name]

            # Copy original arguments
            new_args = [self.translate_expr(arg) for arg in pred.args]

            # Add existential list variables
            for _ in range(num_lists):
                list_var = self.generate_list_var()
                new_args.append(Var(list_var))

            # Return predicate with DATA name and extended arguments
            return Predicate(data_name, new_args)
        else:
            # Unknown predicate - return unchanged
            return Predicate(pred.name, [self.translate_expr(arg) for arg in pred.args])

    def translate_formula(self, formula: Formula) -> Formula:
        """Translate a formula recursively.

        Args:
            formula: The formula to translate

        Returns:
            The translated formula with shape predicates augmented with list arguments.
        """
        if isinstance(formula, BinOp):
            # Binary operations (comparisons) don't need translation
            return BinOp(
                formula.op,
                self.translate_expr(formula.left),
                self.translate_expr(formula.right)
            )
        elif isinstance(formula, Predicate):
            return self.translate_predicate(formula)
        elif isinstance(formula, AndConj):
            return AndConj([self.translate_formula(f) for f in formula.formulas])
        elif isinstance(formula, SepConj):
            return SepConj([self.translate_formula(f) for f in formula.formulas])
        elif isinstance(formula, Exists):
            # Translate the body first
            translated_body = self.translate_formula(formula.body)
            # Keep the original quantified variables
            return Exists(formula.vars[:], translated_body)
        else:
            raise ValueError(f"Unknown formula type: {type(formula)}")

    def translate_assertion(self, assertion: str, reset: bool = True) -> Tuple[str, List[str]]:
        """Translate an assertion string.

        Args:
            assertion: The assertion string to translate
            reset: If True, reset the variable counter before translation.
                   If False, continue from the current counter (for continuous numbering).
                   Default is True for backward compatibility.

        Returns:
            A tuple of (translated_assertion_string, list_of_generated_variables_for_this_assertion)

        Example:
            >>> translator = ShapeTranslator()
            >>> result, vars = translator.translate_assertion("listrep(x) * lseg(y, z)")
            >>> print(result)
            sll(x, ?l1) * sllseg(y, z, ?l2)
            >>> print(vars)
            ['?l1', '?l2']

            For continuous numbering across multiple assertions:
            >>> translator = ShapeTranslator()
            >>> req, req_vars = translator.translate_assertion("listrep(x)")  # Gets ?l1
            >>> ens, ens_vars = translator.translate_assertion("listrep(y)", reset=False)  # Gets ?l2
        """
        # Track variables before translation
        vars_before = len(self.generated_vars)

        # Reset variable counter if requested
        if reset:
            self.reset_var_counter()

        # Parse the assertion
        ast = parse_assertion(assertion)

        # Translate the AST
        translated_ast = self.translate_formula(ast)

        # Recover the string representation
        translated_str = recover_assertion(translated_ast)

        # Return only the NEW variables generated for THIS assertion
        new_vars = self.generated_vars[vars_before:]

        return translated_str, new_vars

    def translate_assertion_with_exists(self, assertion: str) -> Tuple[str, List[str]]:
        """Translate an assertion and wrap with existential quantifiers.

        This function is specifically for INV assertions. It:
        1. Translates the assertion (adding ?l1, ?l2, ... to predicates)
        2. Replaces ?l1, ?l2, ... with l1, l2, ...
        3. Wraps the result with 'exists l1 l2 ...' quantifier
        4. If the assertion already has 'exists', merges the variables

        Args:
            assertion: The assertion string to translate

        Returns:
            A tuple of (translated_assertion_with_exists, list_of_generated_variables)

        Example:
            >>> translator = ShapeTranslator()
            >>> result, vars = translator.translate_assertion_with_exists("t != 0 && listrep(x) * lseg(y, z)")
            >>> print(result)
            exists l1 l2,
                t != 0 && listrep(x, l1) * lseg(y, z, l2)
            >>> print(vars)
            ['l1', 'l2']
        """
        # Reset variable counter for this assertion
        self.reset_var_counter()

        # Parse the assertion
        ast = parse_assertion(assertion)

        # Translate the AST
        translated_ast = self.translate_formula(ast)

        # Get the generated variables (e.g., ['?l1', '?l2', '?l3'])
        generated_vars = self.generated_vars[:]

        # Convert ?l1, ?l2, ... to l1, l2, ...
        var_names_without_question = [v[1:] for v in generated_vars]  # Remove '?' prefix

        # Check if the translated AST already has exists quantifier
        if isinstance(translated_ast, Exists):
            # Merge the existing variables with our generated variables
            existing_vars = translated_ast.vars
            all_vars = existing_vars + var_names_without_question
            body = translated_ast.body

            # Create new Exists with merged variables
            new_ast = Exists(all_vars, body)
        else:
            # Wrap with new exists quantifier
            if var_names_without_question:
                new_ast = Exists(var_names_without_question, translated_ast)
            else:
                # No variables generated, return as is
                new_ast = translated_ast

        # Recover string and replace ?l with l
        translated_str = recover_assertion(new_ast)

        # Replace all ?l1, ?l2, ... with l1, l2, ...
        for var in generated_vars:
            var_without_question = var[1:]  # Remove '?'
            translated_str = translated_str.replace(var, var_without_question)

        return translated_str, var_names_without_question

    def add_predicate_mapping(self, shape_name: str, data_name: str, num_lists: int = 1):
        """Add or update a predicate mapping.

        Args:
            shape_name: Shape predicate name (e.g., 'listrep')
            data_name: Data predicate name (e.g., 'sll')
            num_lists: Number of list arguments to add (default: 1)

        Example:
            >>> translator.add_predicate_mapping('my_shape', 'my_data', 2)
            # Now my_shape(x) -> my_data(x, ?l1, ?l2)
        """
        self.predicate_name_mapping[shape_name] = (data_name, num_lists)

    def remove_predicate_mapping(self, shape_name: str):
        """Remove a predicate mapping.

        Args:
            shape_name: Shape predicate name to remove
        """
        if shape_name in self.predicate_name_mapping:
            del self.predicate_name_mapping[shape_name]

    def get_predicate_mapping(self) -> Dict[str, Tuple[str, int]]:
        """Get the current predicate name mapping.

        Returns:
            Dictionary mapping shape names to (data_name, num_lists) tuples

        Example:
            >>> mapping = translator.get_predicate_mapping()
            >>> print(mapping['listrep'])
            ('sll', 1)
        """
        return self.predicate_name_mapping.copy()

    def set_predicate_mapping(self, mapping: Dict[str, Tuple[str, int]]):
        """Replace the entire predicate mapping.

        Args:
            mapping: New mapping dictionary

        Example:
            >>> new_mapping = {
            ...     'listrep': ('sll', 1),
            ...     'lseg': ('sllseg', 1),
            ... }
            >>> translator.set_predicate_mapping(new_mapping)
        """
        self.predicate_name_mapping = mapping.copy()


def translate(assertion: str, translator: ShapeTranslator = None) -> Tuple[str, List[str]]:
    """Convenience function to translate an assertion.

    Args:
        assertion: The assertion string to translate
        translator: Optional translator instance (creates new one if not provided)

    Returns:
        A tuple of (translated_assertion_string, list_of_generated_variables)

    Example:
        >>> result, vars = translate("t != 0 && listrep(x) * lseg(y, z)")
        >>> print(result)
        t != 0 && listrep(x, ?l1) * lseg(y, z, ?l2)
    """
    if translator is None:
        translator = ShapeTranslator()

    return translator.translate_assertion(assertion)


def translate_file(input_file: str, output_file: str, translator: ShapeTranslator = None):
    """Translate assertions from an input file and write to output file.

    Args:
        input_file: Path to input file containing assertions (one per line)
        output_file: Path to output file
        translator: Optional translator instance
    """
    if translator is None:
        translator = ShapeTranslator()

    with open(input_file, 'r') as f:
        assertions = [line.strip() for line in f if line.strip()]

    results = []
    for assertion in assertions:
        try:
            translated, vars = translator.translate_assertion(assertion)
            results.append(f"Original: {assertion}")
            results.append(f"Translated: {translated}")
            results.append(f"Generated variables: {', '.join(vars)}")
            results.append("")
        except Exception as e:
            results.append(f"Error translating: {assertion}")
            results.append(f"Error: {str(e)}")
            results.append("")

    with open(output_file, 'w') as f:
        f.write('\n'.join(results))
