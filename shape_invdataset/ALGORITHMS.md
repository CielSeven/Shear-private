# Shape Invariant Dataset — Algorithm Coverage

Annotated files use `/*@ Require ... Ensure ... */` for function specs and `/*@ Inv Assert ... */` for loop invariants.
Predicates: `listrep`, `lseg` (SLL); `dlistrep_shape`, `dllseg_shape` (DLL); `IntArray::*_shape` and `IntArray::undef_*` (integer arrays).

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

## Integer Array (`int_array/`)

| File | Functions | Description |
|------|-----------|-------------|
| `lc26_remove_duplicates.c` | `array_remove_duplicates(a, n)` | Compact a sorted array in-place and return the number of unique elements. |
| `lc31_next_permutation.c` | `array_next_permutation(a, n)` | Compute the next lexicographic permutation in-place. |
| `lc42_trap_rain.c` | `array_trap_rain_water(height, n)` | Two-pointer greedy trapped-rain-water accumulation. |
| `lc45_jump_min.c` | `array_jump_min_steps(a, n)` | Greedy minimum jumps using current range end and next farthest reach. |
| `lc53_max_subarray.c` | `array_max_subarray(a, n)` | Kadane-style maximum subarray sum with a running best value. |
| `lc55_can_jump.c` | `array_can_jump(a, n)` | Greedy reachability check using the farthest reachable index. |
| `lc75_dutch_flag.c` | `array_dutch_flag_sort(a, n)` | Sort an array containing `0`, `1`, and `2` with low/mid/high pointers. |
| `lc75_partition_by_pivot.c` | `array_partition_by_pivot(a, n, pivot)` | Dutch-flag-style three-way in-place partition around an arbitrary pivot. |
| `lc88_merge_sorted.c` | `array_merge_sorted(a, m, b, n)` | Merge sorted array `b` into the spare tail of sorted array `a` from right to left. |
| `lc121_best_stock.c` | `array_best_stock_profit(prices, n)` | Greedy single-pass stock profit using the minimum price seen so far. |
| `lc152_max_product_subarray.c` | `array_max_product_subarray(a, n)` | DP tracking both maximum and minimum product ending at each index. |
| `lc189_rotate.c` | `array_rotate_right(a, n, k)` | Rotate an array in-place using three range reversals. |
| `lc198_rob_linear.c` | `array_rob_linear(a, n)` | Constant-space dynamic programming for non-adjacent maximum sum. |
| `lc238_product_except_self.c` | `array_product_except_self(a, n, out)` | Fill `out` with products of all elements except the current one using prefix/suffix scans. |
| `lc376_wiggle_length.c` | `array_wiggle_max_length(a, n)` | Greedy/DP wiggle subsequence length with `up` and `down` states. |
| `lc746_min_cost_climb.c` | `array_min_cost_climb(cost, n)` | Constant-space DP over the previous two stair costs. |

### Integer Array Patterns Used
- Forward and backward scans over one or two arrays.
- Read/write compaction with separate source and destination indices.
- In-place swaps with two-pointer and three-pointer regions.
- Suffix reversal after a pivot search.
- Prefix/suffix accumulation with an output array.
- Running dynamic-programming state over a linear scan.
- Greedy frontier maintenance (`farthest`, `current_end`) for jump-style problems.
- Constant-space DP with rolling states (`skip/take`, `prev1/prev2`, `up/down`).
- Dual-state DP where negative values can swap maxima and minima.

---

## Notes

- `dll_zip.c` uses a 2-step `dllseg` extension per iteration (inserting one node from each list); symexec verification in progress.
- Use `scripts/symexec.sh --FILE=<path>` to verify a single file.
- Use `scripts/symexec.sh --C_DIR=shape_invdataset/sll`, `--C_DIR=shape_invdataset/dll`, or `--C_DIR=shape_invdataset/int_array` to batch-verify an annotated directory.
