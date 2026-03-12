# TransShape: Shape Assertion Translator

A complete pipeline for translating C shape assertions to Coq separation logic with guard generation.

## Overview

**TransShape** processes C files with shape assertion annotations and translates them to Coq-compatible separation logic predicates. It handles function specifications (Require/Ensure) and loop invariants (Inv) with optional Coq guard generation.

## Features

✅ **Shape Predicate Translation**: `listrep(x)` → `sll(x, ?l1)`
✅ **Predicate Name Mapping**: `listrep` → `sll`, `lseg` → `sllseg`
✅ **Continuous Variable Numbering**: Variables numbered continuously across Require/Ensure (?l1, ?l2, ?l3)
✅ **INV Exists Wrapping**: Loop invariants wrapped with `exists l1 l2 ...`
✅ **Command Guard Extraction**: Extracts while loop conditions with nested parentheses
✅ **Coq Guard Generation**: Generates Coq guards using guardgen module (optional)
✅ **Null Pointer Handling**: Supports `(void *)0`, `null`, `0` as null pointer
✅ **Separation of Concerns**: Translation and guard generation are separate functions

## Quick Start

### Basic Usage

```python
from process_and_translate import process_and_translate_file, format_translation_result

# Process a C file with automatic guard generation
result = process_and_translate_file('sll_copy.c')
print(format_translation_result(result))
```

### Two-Step Process (Translation + Guard Generation)

```python
from process_and_translate import AssertionProcessor, generate_coq_guards_for_assertions

processor = AssertionProcessor()

# Step 1: Extract and translate
extraction = processor.extractor.process_file('sll_copy.c')
translated = processor.translate_inner_assertions(extraction['inner_assertions'])

# Step 2: Generate Coq guards separately
with_guards = generate_coq_guards_for_assertions(translated)
```

### Disable Guard Generation

```python
# Translation only, no guard generation
result = process_and_translate_file('sll_copy.c', generate_guards=False)
```

## Input Format

### Function Specification

```c
struct list* sll_copy(struct list* x)
/*@
    Require listrep(x)
    Ensure listrep(__return) * listrep(x)
*/
```

### Loop Invariant

```c
/*@ Inv listrep(p) * listrep(y) */
while (p != null) {
    // ...
}
```

## Output Format

### Function Specification Translation

**Input:**
```
Require: listrep(x)
Ensure: listrep(__return) * listrep(x)
```

**Output:**
```
Require: sll(x, ?l1)
Ensure: sll(__return, ?l2) * sll(x, ?l3)
Generated variables: ?l1, ?l2, ?l3
```

### Loop Invariant Translation

**Original:**
```
listrep(p) * listrep(y)
```

**Translated:**
```
exists l1 l2, sll(p, l1) * sll(y, l2)
```

**CommandGuard:** `p != null`

**CoqGuard:**
```coq
fun a =>
  let '(l1, l2) := a in
  (l1 <> [])
```

## Pipeline Architecture

```
┌─────────────┐
│  C Source   │
│  (.c file)  │
└──────┬──────┘
       │
       ▼
┌─────────────────────────┐
│  1. Extract Annotations │  (preprocess.py)
│  - Function specs       │
│  - Loop invariants      │
│  - Command guards       │
└──────┬──────────────────┘
       │
       ▼
┌─────────────────────────┐
│  2. Translate Assertions│  (translator.py)
│  - Shape → Data preds   │
│  - Predicate renaming   │
│  - Variable numbering   │
│  - Exists wrapping      │
└──────┬──────────────────┘
       │
       ▼
┌─────────────────────────┐
│  3. Generate Coq Guards │  (guardgen module)
│  (optional)             │
│  - Parse invariant      │
│  - Parse condition      │
│  - Generate guard expr  │
└──────┬──────────────────┘
       │
       ▼
┌─────────────┐
│   Result    │
│   (Dict)    │
└─────────────┘
```

## Key Components

### 1. Annotation Extractor (preprocess.py)

Extracts annotations from C source files:
- Function specifications (Require/Ensure/With)
- Inner assertions (loop invariants)
- Command guards (while conditions with nested parentheses)

### 2. Shape Translator (translator.py)

Translates shape predicates to data predicates:
- Maps predicate names: `listrep` → `sll`, `lseg` → `sllseg`
- Generates list variables: `?l1`, `?l2`, `?l3`...
- Maintains continuous numbering across Require/Ensure
- Wraps INV assertions with `exists` quantifiers

### 3. Assertion Processor (process_and_translate.py)

Orchestrates the translation pipeline:
- `translate_funcspec()`: Translates function specifications
- `translate_inner_assertions()`: Translates loop invariants
- `generate_coq_guards()`: Generates Coq guards (separate function)
- `process_file()`: Complete pipeline with optional guard generation

### 4. Coq Guard Generator (../guardgen)

Generates Coq guard expressions from:
- Translated invariants (spatial predicates)
- Command guards (loop conditions)

Supports:
- Null checks: `p != null`, `p == (void *)0`
- Pointer equality: `p == q`, `x != y`
- Boolean combinations: `&&`, `||`, `!`

## Predicate Mappings

| Shape Predicate | Data Predicate | Abstract Variable |
|----------------|----------------|-------------------|
| `listrep(x)`   | `sll(x, ?l1)` | `?l1` (list)     |
| `lseg(x, y)`   | `sllseg(x, y, ?l1)` | `?l1` (list) |
| `dlistrep(x)`  | `dll(x, ?l1)` | `?l1` (list)     |
| `dlseg(x, p, n, y)` | `dllseg(x, p, n, y, ?l1)` | `?l1` (list) |
| `tree(x)`      | `store_tree(x, ?l1)` | `?l1` (tree) |

## Important Features

### Continuous Variable Numbering

Variables are numbered continuously across Require and Ensure:

```python
# Correct:
Require: sll(x, ?l1) * sll(y, ?l2)
Ensure: sll(__return, ?l3)
Generated variables: ?l1, ?l2, ?l3

# Wrong (separate numbering):
Require: sll(x, ?l1) * sll(y, ?l2)
Ensure: sll(__return, ?l1)  # Should be ?l3!
```

### INV Exists Wrapping

Loop invariants are automatically wrapped with `exists`:

```python
# Original:
listrep(p) * listrep(y)

# Translated:
exists l1 l2, sll(p, l1) * sll(y, l2)
```

If the original already has `exists`, variables are merged:

```python
# Original:
exists u, listrep(p) * listrep(y)

# Translated:
exists l1 l2 u, sll(p, l1) * sll(y, l2)
```

### Null Pointer Handling

All these forms are recognized as null:

```c
p != null          // Keyword
p != 0             // Zero
p != (void *)0     // C null literal (normalized to 0)
p != (void*)0      // No space
p != ( void * )0   // Extra spaces
```

### Nested Parentheses in Command Guards

The command guard extractor correctly handles nested parentheses:

```c
while (curr != (void *)0)  // Correctly extracts full condition
while ((x != null) && (y != null))  // Handles nested parens
```

## Testing

### Run All Tests

```bash
cd GenMonads/transshape

# Test all C files in shape_invdataset
python test_all_c_files.py

# Test Coq guard integration
python test_coq_guard_integration.py

# Test (void *)0 handling
python test_void_ptr_null.py
```

### Test Coverage

- ✅ Translation without guard generation
- ✅ Translation with automatic guard generation
- ✅ Manual two-step guard generation
- ✅ Disabled guard generation
- ✅ Continuous variable numbering
- ✅ INV exists wrapping
- ✅ Nested parentheses in command guards
- ✅ (void *)0 null pointer handling
- ✅ Error handling for all edge cases

## API Reference

### Main Functions

#### `process_and_translate_file(file_path, generate_guards=True)`

Complete pipeline: extract, translate, and optionally generate guards.

**Parameters:**
- `file_path` (str): Path to C file
- `generate_guards` (bool): Whether to generate Coq guards (default: True)

**Returns:** Dictionary with:
- `file`: File path
- `function`: Function name
- `funcspec`: Translated function specification
- `inner_assertions`: List of translated loop invariants

#### `generate_coq_guards_for_assertions(translated_assertions)`

Generate Coq guards for translated assertions.

**Parameters:**
- `translated_assertions` (List[Dict]): Translated assertions from `translate_inner_assertions()`

**Returns:** List of assertions with `coq_guard` or `coq_guard_error` fields added

#### `format_translation_result(result)`

Format result dictionary as readable text.

**Parameters:**
- `result` (Dict): Result from `process_and_translate_file()`

**Returns:** Formatted string

### Class: AssertionProcessor

#### `translate_funcspec(funcspec)`

Translate function specification (Require/Ensure/With).

#### `translate_inner_assertions(inner_assertions)`

Translate loop invariants (without guard generation).

#### `generate_coq_guards(translated_assertions)`

Generate Coq guards for translated assertions.

#### `process_file(file_path, generate_guards=True)`

Complete pipeline for a single file.

## Examples

See example files:
- `example_usage.py`: Basic usage
- `example_complete_pipeline.py`: Full pipeline
- `example_separate_guard_gen.py`: Two-step process

## Error Handling

The pipeline handles errors gracefully:

- **Translation errors**: Captured in `error` field of assertion
- **Guard generation errors**: Captured in `coq_guard_error` field
- **Missing guardgen**: System continues without guard generation
- **Unsupported predicates**: Error message in `coq_guard_error`

## Dependencies

- Python 3.9+
- `guardgen` module (optional, for Coq guard generation)
- Standard library: `re`, `os`, `pathlib`

## Project Structure

```
transshape/
├── preprocess.py              # Annotation extraction
├── parser.py                  # Shape predicate parser
├── translator.py              # Shape to data translation
├── process_and_translate.py   # Main pipeline
├── test_*.py                  # Test files
├── example_*.py               # Example usage
└── README.md                  # This file
```

## Limitations

⚠ **Predicate Support**: Only registered predicates in guardgen can generate guards
⚠ **Simple Conditions**: Complex while conditions may not be supported by guardgen
⚠ **SLL/DLL Focus**: Best support for singly/doubly-linked lists

## Summary

TransShape provides a complete, flexible pipeline for translating C shape assertions to Coq separation logic:

✅ **Complete Pipeline**: From C source to Coq guards
✅ **Modular Design**: Each component has a single responsibility
✅ **Flexible Usage**: Automatic or manual control
✅ **Robust**: Graceful error handling
✅ **Well-Tested**: Comprehensive test coverage
✅ **Production-Ready**: Used for shape_invdataset processing
