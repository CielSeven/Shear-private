# AddAbstract: Add safeExec Predicate to Loop Invariants

This module adds abstract program predicates (`safeExec`) to translated loop invariants.

## Overview

The `addabstract` module takes a translated loop invariant and wraps it with a `safeExec` predicate that references abstract programs for:
1. The loop body (`PROGRAM_LOOP`)
2. The post-loop processing (`PROGRAM_LOOP_END`)

## Usage

### Basic Example

```python
from addabstract import add_safeexec_predicate

# Input: translated invariant
translated_inv = "exists l1 l2 l3, t != 0 && sllseg(x@pre,p, l1) * sll(p, l2) * sllseg(y, t, l3)"
generated_vars = ['l1', 'l2', 'l3']

# Add safeExec predicate
result = add_safeexec_predicate(
    translated_inv,
    generated_vars,
    program_loop="sll_copy_M_loop",
    program_loop_end="sll_copy_M_loop_end"
)

# Output:
# exists l1 l2 l3, safeExec(ATrue, bind(sll_copy_M_loop(l1,l2,l3), sll_copy_M_loop_end), X) &&
#     t != 0 && sllseg(x@pre,p, l1) * sll(p, l2) * sllseg(y, t, l3)
```

### Integration with TransShape Pipeline

```python
from transshape.process_and_translate import process_and_translate_file
from addabstract import add_safeexec_to_assertion

# Process C file
result = process_and_translate_file('sll_copy.c', generate_guards=False)

# Add safeExec to each invariant
for assertion in result['inner_assertions']:
    if assertion['type'] == 'Inv':
        with_safeexec = add_safeexec_to_assertion(
            assertion,
            program_loop=f"{result['function']}_M_loop",
            program_loop_end=f"{result['function']}_M_loop_end"
        )
        print(with_safeexec['with_safeexec'])
```

## API Reference

### `add_safeexec_predicate(translated_inv, generated_vars, program_loop, program_loop_end, precondition='ATrue', postcondition='X')`

Add safeExec predicate to a translated loop invariant.

**Parameters:**
- `translated_inv` (str): Translated loop invariant
- `generated_vars` (List[str]): List of generated variables (e.g., `['l1', 'l2', 'l3']`)
- `program_loop` (str): Abstract program name for the loop (e.g., `"sll_copy_M_loop"`)
- `program_loop_end` (str): Abstract program name for loop end (e.g., `"sll_copy_M_loop_end"`)
- `precondition` (str): Precondition for safeExec (default: `"ATrue"`)
- `postcondition` (str): Postcondition for safeExec (default: `"X"`)

**Returns:** Full assertion with safeExec predicate added (str)

### `add_safeexec_to_assertion(assertion_dict, program_loop, program_loop_end, precondition='ATrue', postcondition='X')`

Add safeExec predicate to an assertion dictionary from transshape pipeline.

**Parameters:**
- `assertion_dict` (dict): Dictionary with `'translated'` and `'variables'` keys
- `program_loop` (str): Abstract program name for the loop
- `program_loop_end` (str): Abstract program name for loop end
- `precondition` (str): Precondition for safeExec (default: `"ATrue"`)
- `postcondition` (str): Postcondition for safeExec (default: `"X"`)

**Returns:** Updated dictionary with `'with_safeexec'` field added (dict)

## Examples

### Example 1: Basic Usage

**Input:**
```
Translated: exists l1 l2 l3, t != 0 && sllseg(x@pre,p, l1) * sll(p, l2) * sllseg(y, t, l3)
Variables: [l1, l2, l3]
Program: sll_copy_M_loop
Program End: sll_copy_M_loop_end
```

**Output:**
```
exists l1 l2 l3, safeExec(ATrue, bind(sll_copy_M_loop(l1,l2,l3), sll_copy_M_loop_end), X) &&
    t != 0 && sllseg(x@pre,p, l1) * sll(p, l2) * sllseg(y, t, l3)
```

### Example 2: No Exists Clause

**Input:**
```
Translated: sll(p, l1) * sll(y, l2)
Variables: [l1, l2]
```

**Output:**
```
safeExec(ATrue, bind(test_M_loop(l1,l2), test_M_loop_end), X) && sll(p, l1) * sll(y, l2)
```

### Example 3: No Variables

**Input:**
```
Translated: exists l1, x != null && y != null
Variables: []
```

**Output:**
```
exists l1, safeExec(ATrue, bind(test_M_loop, test_M_loop_end), X) && x != null && y != null
```

**Note:** When there are no generated variables, the program name has no parentheses.

### Example 4: Custom Pre/Post Conditions

**Input:**
```python
add_safeexec_predicate(
    "exists l1, sll(p, l1)",
    ['l1'],
    "test_M_loop",
    "test_M_loop_end",
    precondition="PRE",
    postcondition="POST"
)
```

**Output:**
```
exists l1, safeExec(PRE, bind(test_M_loop(l1), test_M_loop_end), POST) && sll(p, l1)
```

## Format of safeExec Predicate

The `safeExec` predicate has the following format:

```
safeExec(PRECONDITION, bind(PROGRAM_LOOP(vars), PROGRAM_LOOP_END), POSTCONDITION)
```

Where:
- `PRECONDITION`: Precondition for the safe execution (default: `ATrue`)
- `PROGRAM_LOOP(vars)`: Abstract program for the loop body with generated variables as arguments
- `PROGRAM_LOOP_END`: Abstract program for post-loop processing
- `POSTCONDITION`: Postcondition for the safe execution (default: `X`)

## Variable Handling

The module automatically:
- Strips `?` prefix from variables (e.g., `?l1` → `l1`)
- Formats variables as comma-separated list (e.g., `l1,l2,l3`)
- Handles empty variable lists (results in `PROGRAM_LOOP` without parentheses)

## Testing

Run the test suite:

```bash
cd GenMonads
python test_addabstract.py
```

The test suite includes:
- ✓ Basic safeExec addition
- ✓ Invariants with/without exists clause
- ✓ Variables with/without `?` prefix
- ✓ Custom pre/post conditions
- ✓ Integration with assertion dictionaries
- ✓ Real files from shape_invdataset

## Integration with Full Pipeline

```python
from transshape.process_and_translate import process_and_translate_file
from addabstract import add_safeexec_predicate

# Process file
result = process_and_translate_file('sll_copy.c')

# For each loop invariant
for assertion in result['inner_assertions']:
    if assertion['type'] == 'Inv':
        # Get translated invariant and variables
        translated = assertion['translated']
        variables = assertion['variables']

        # Generate program names from function name
        func_name = result['function']
        program_loop = f"{func_name}_M_loop"
        program_loop_end = f"{func_name}_M_loop_end"

        # Add safeExec
        with_safeexec = add_safeexec_predicate(
            translated,
            variables,
            program_loop,
            program_loop_end
        )

        print(with_safeexec)
```

## Summary

✅ **Simple API**: Single function call to add safeExec predicate
✅ **Flexible**: Supports custom pre/post conditions
✅ **Robust**: Handles all edge cases (no exists, no variables, etc.)
✅ **Integrated**: Works seamlessly with transshape pipeline
✅ **Well-tested**: Comprehensive test coverage
