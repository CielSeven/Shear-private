"""
Translator for shape predicates to data predicates.

This module provides functionality to translate shape predicates by adding
existential list variables according to a predefined mapping.
"""

from typing import Dict, Tuple, List, Optional
from .parser import (
    Formula, Expr, Predicate, SepConj, AndConj, Exists, BinOp,
    Var, FieldAccess, parse_assertion, recover_assertion
)
import copy

from GenMonads.predicate_mapping import get_predicate_mappings


class ShapeTranslator:
    """Translator for shape predicates to data predicates."""

    def __init__(self):
        """Initialize the translator with predicate mappings."""
        self.predicate_name_mapping: Dict[str, Tuple[str, int]] = get_predicate_mappings()
        self.var_counter = 0
        self.generated_vars: List[str] = []
        self.var_prefix = ""  # For nested loops like ?l_outer1, ?l_inner1

    def reset_var_counter(self, start_from: int = 0, prefix: str = ""):
        """Reset the variable counter and set prefix."""
        self.var_counter = start_from
        self.generated_vars = []
        self.var_prefix = prefix

    def generate_list_var(self) -> str:
        """Generate a unique existential list variable."""
        self.var_counter += 1
        prefix_sep = "_" if self.var_prefix else ""
        var_name = f"?l{self.var_prefix}{prefix_sep}{self.var_counter}"
        self.generated_vars.append(var_name)
        return var_name

    def translate_expr(self, expr: Expr) -> Expr:
        return copy.deepcopy(expr)

    def translate_predicate(self, pred: Predicate) -> Predicate:
        if pred.name in self.predicate_name_mapping:
            data_name, num_lists = self.predicate_name_mapping[pred.name]
            new_args = [self.translate_expr(arg) for arg in pred.args]
            for _ in range(num_lists):
                list_var = self.generate_list_var()
                new_args.append(Var(list_var))
            return Predicate(data_name, new_args)
        else:
            return Predicate(pred.name, [self.translate_expr(arg) for arg in pred.args])

    def translate_formula(self, formula: Formula) -> Formula:
        if isinstance(formula, BinOp):
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
            translated_body = self.translate_formula(formula.body)
            return Exists(formula.vars[:], translated_body)
        else:
            raise ValueError(f"Unknown formula type: {type(formula)}")

    def translate_assertion(self, assertion: str, reset: bool = True, prefix: str = "") -> Tuple[str, List[str]]:
        """Translate an assertion string."""
        vars_before = len(self.generated_vars)
        if reset:
            self.reset_var_counter(prefix=prefix)
        
        ast = parse_assertion(assertion)
        translated_ast = self.translate_formula(ast)
        translated_str = recover_assertion(translated_ast)
        new_vars = self.generated_vars[vars_before:]
        return translated_str, new_vars

    def translate_assertion_with_exists(self, assertion: str, prefix: str = "") -> Tuple[str, List[str]]:
        """Translate and wrap with exists."""
        self.reset_var_counter(prefix=prefix)
        ast = parse_assertion(assertion)
        translated_ast = self.translate_formula(ast)
        generated_vars = self.generated_vars[:]
        var_names_without_question = [v[1:] for v in generated_vars]

        if isinstance(translated_ast, Exists):
            existing_vars = translated_ast.vars
            all_vars = existing_vars + var_names_without_question
            body = translated_ast.body
            new_ast = Exists(all_vars, body)
        else:
            if var_names_without_question:
                new_ast = Exists(var_names_without_question, translated_ast)
            else:
                new_ast = translated_ast

        translated_str = recover_assertion(new_ast)
        for var in generated_vars:
            var_without_question = var[1:]
            translated_str = translated_str.replace(var, var_without_question)

        return translated_str, var_names_without_question

def translate(assertion: str, translator: ShapeTranslator = None) -> Tuple[str, List[str]]:
    if translator is None:
        translator = ShapeTranslator()
    return translator.translate_assertion(assertion)

def translate_file(input_file: str, output_file: str, translator: ShapeTranslator = None):
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
