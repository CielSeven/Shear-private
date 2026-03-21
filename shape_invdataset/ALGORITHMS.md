# Shape Invariant Dataset — Algorithm Coverage

All files use `/*@ Require ... Ensure ... */` for function specs and `/*@ Inv ... */` for loop invariants.
Predicates: `listrep`, `lseg` (SLL); `dlistrep_shape`, `dllseg_shape` (DLL).

---

## Singly-Linked List (`sll/`)

| File | Functions | Description |
|------|-----------|-------------|
| `sll_append.c` | `sll_append(x, y)` | Find tail of `x`, link `y` at end. In-place, destructive to `x`. |
| `sll_copy.c` | `sll_copy(x)` | Forward copy of `x`, allocating fresh nodes. |
| `sll_reverse.c` | `sll_reverse(x)` | Reverse `x` in-place by relinking `next` pointers. |
| `sll_append_rev.c` | `sll_append_rev(x, y)` | Reverse `x` and append `y` in a single pass. Result: `rev(x) ++ y`. |
| `sll_copy_rev.c` | `sll_copy_rev(x)` | Non-destructive reversed copy of `x`. Allocates fresh nodes, prepends each. |
| `sll_zip.c` | `sll_zip(x, y)` | In-place interleave of two lists. Result: `[x0,y0,x1,y1,...]`. |
| `sll_rotate.c` | `sll_rotate_left(x)` | Move last element to front (in-place). |
| | `sll_rotate_right(x)` | Move first element to end (in-place). |
| `sll_merge.c` | `sll_merge(x, y)` | Sorted merge of two lists using data comparison. Uses `t->next=0` pattern to keep invariant clean. |
| `sll_multi_merge.c` | `sll_merge(x, y)` | Forward-declared helper (sorted merge). |
| | `sll_multi_merge(x, y, z)` | Merge 3 sorted lists with its own interleaving loop, calling `sll_merge` for remainders. |
| `sll_copy_double.c` | `sll_copy_double(x)` | Non-destructive copy where each element is duplicated. Result: `[x0,x0,x1,x1,...]`. Allocates 2 nodes per step. |

### SLL Invariant Patterns Used
- `listrep(curr) * listrep(acc)` — two independent lists (reverse/append_rev)
- `lseg(x@pre, p) * listrep(p) * listrep(y)` — source traversal + accumulator (copy_rev, copy_double)
- `lseg(x@pre, t) * t != 0 && t -> next == u && listrep(u)` — segment + tracked tail (append, rotate)
- `t != 0 && t -> next == 0 && listrep(x) * listrep(y) * lseg(result, t)` — merge with cleared tail
- `lseg(x@pre, t) * listrep(y) * listrep(z) * listrep(u)` — 3-list interleave (multi_merge)

---

## Doubly-Linked List (`dll/`)

| File | Functions | Description |
|------|-----------|-------------|
| `dll_copy.c` | `dll_copy(x)` | Forward copy of `x`, allocating fresh nodes with correct `prev` pointers. |
| `dll_reverse.c` | `dll_reverse(x)` | Reverse `x` in-place by swapping `next`/`prev` pointers. |
| `dll_multi_merge.c` | `merge(x, y)` | Forward-declared helper (DLL merge). |
| | `dll_multi_merge(x, y, z)` | Interleave-merge 3 DLLs with own loop; calls `merge` for remainders. |
| `append.c` | `append(x, y)` | Append two DLLs (no `dll_` prefix variant). |
| `dll_auto.c` | multiple | Multi-function file covering copy, free, reverse, append, iter, iter_back, merge, multi_merge, multi_rev. |
| `dll_append.c` | `dll_append(x, y)` | Append two DLLs maintaining `prev` pointers at the junction. |
| `dll_copy_rev.c` | `dll_copy_rev(x)` | Non-destructive reversed copy of `x`. Prepends fresh nodes, updating `prev` pointers. |
| `dll_copy_rev_append.c` | `dll_copy_rev_append(x, y)` | Reversed copy of `x` with `y` appended. One pass: traverse `x` forward, prepend copies starting from `y`. Result: `rev_copy(x) ++ y`. |
| `dll_rotate_left.c` | `dll_rotate_left(x)` | Move head to tail (in-place), maintaining all `prev`/`next` pointers. |
| `dll_zip.c` | `dll_zip(x, y)` | In-place interleave of two DLLs with `prev` pointer maintenance. |

### DLL Invariant Patterns Used
- `dlistrep_shape(w, v) * dlistrep_shape(v, w)` — dual-list reverse pattern
- `dllseg_shape(x@pre, 0, p_prev, p) * dlistrep_shape(p, p_prev)` — segment + remaining (traversal)
- `dllseg_shape(x@pre, 0, t->prev, t) * dlistrep_shape(u, t) * dlistrep_shape(y, 0)` — append/rotate pattern
- `dllseg_shape(x@pre, 0, p_prev, p) * dlistrep_shape(p, p_prev) * dlistrep_shape(acc, 0)` — copy with accumulator

---

## Notes

- `dll_zip.c` uses a 2-step `dllseg` extension per iteration (inserting one node from each list); symexec verification in progress.
- Use `scripts/symexec.sh --FILE=<path>` to verify a single file.
- Use `scripts/symexec.sh --C_DIR=shape_invdataset/sll` or `--C_DIR=shape_invdataset/dll` to batch-verify a directory.
