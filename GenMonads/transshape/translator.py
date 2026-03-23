"""
Translator for shape predicates to data predicates.

This module translates mapped shape predicates by appending augmented data
variables according to the predicate mapping schema.
"""

from typing import Dict, List, Tuple
from .parser import (
    Formula, Expr, Predicate, SepConj, AndConj, Exists, BinOp,
    Var, FieldAccess, parse_assertion, recover_assertion
)
import copy

from GenMonads.predicate_mapping import PredicateMapping, get_predicate_mappings


class ShapeTranslator:
    """Translator for shape predicates to data predicates."""

    def __init__(self):
        """Initialize the translator with predicate mappings."""
        self.predicate_mappings: Dict[str, PredicateMapping] = get_predicate_mappings()
        self.var_counter = 0
        self.generated_vars: List[str] = []
        self.generated_var_types: List[str] = []
        self.last_generated_var_types: List[str] = []
        self.var_prefix = ""  # For nested loops like ?l_outer1, ?l_inner1

    def reset_var_counter(self, start_from: int = 0, prefix: str = ""):
        """Reset the variable counter and set prefix."""
        self.var_counter = start_from
        self.generated_vars = []
        self.generated_var_types = []
        self.last_generated_var_types = []
        self.var_prefix = prefix

    def generate_list_var(self, var_type: str = "list Z") -> str:
        """Generate a unique existential variable for an augmented data argument."""
        self.var_counter += 1
        prefix_sep = "_" if self.var_prefix else ""
        var_name = f"?l{self.var_prefix}{prefix_sep}{self.var_counter}"
        self.generated_vars.append(var_name)
        self.generated_var_types.append(var_type)
        return var_name

    def translate_expr(self, expr: Expr) -> Expr:
        return copy.deepcopy(expr)

    def translate_predicate(self, pred: Predicate) -> Predicate:
        if pred.name in self.predicate_mappings:
            mapping = self.predicate_mappings[pred.name]
            if mapping.shape_arity >= 0 and len(pred.args) != mapping.shape_arity:
                raise ValueError(
                    f"Predicate {pred.name} expected {mapping.shape_arity} shape args, "
                    f"got {len(pred.args)}"
                )
            new_args = [self.translate_expr(arg) for arg in pred.args]
            for var_type in mapping.data_var_types:
                list_var = self.generate_list_var(var_type)
                new_args.append(Var(list_var))
            return Predicate(mapping.data_name, new_args)
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
        types_before = len(self.generated_var_types)
        if reset:
            self.reset_var_counter(prefix=prefix)
            vars_before = 0
            types_before = 0
        
        ast = parse_assertion(assertion)
        translated_ast = self.translate_formula(ast)
        translated_str = recover_assertion(translated_ast)
        new_vars = self.generated_vars[vars_before:]
        self.last_generated_var_types = self.generated_var_types[types_before:]
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
        self.last_generated_var_types = self.generated_var_types[:]
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
