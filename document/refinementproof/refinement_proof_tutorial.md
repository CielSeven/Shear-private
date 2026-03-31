# A tutorial for proving generated VCs with the execution predicate $\text{Exec}(\text{Pre}, c, \text{Post})$

 This is a tutorial to illustrate how to prove program refinement with the execution predicate $\text{Exec}(\text{Pre}, c, \text{Post})$

## Generated VCs are separation-logic entailments: $\forall \vec{a}.\, P(\vec{a}) \vdash Q(\vec{a})$ 

### The syntax of an assertion 

We use linear separation logic assertions with the following grammar (informally):

```
A ::= [| P |]                          (pure proposition)
    | TT                               (true)
    | emp                              (empty heap)
    | e # T |-> v                      (points-to, `T` is the type)
    | Pred e1 ... en                   (user-defined heap predicate)
    | A && A                           (logical conjunction)
    | A || A                           (logical disjunction)
    | A ** A                           (separating conjunction)
    | A -* A                           (separating implication)
    | EX x: T, A                       (existential quantification)
    | ALL x: T, A                      (universal quantification)
```

Here `P` is a pure proposition over program expressions (e.g., equalities and arithmetic),
`e`/`v` are expressions, `T` is a type (e.g., `Int`, `Ptr`), and `Pred` ranges over the
separating predicates defined below (e.g., `sll`, `sllseg`, `dlistrep`, `dllseg`).



##  Interpretation  for user-defined heap predicates

1. `sll p l`: denotes a complete singly linked list starting at address `p`, corresponding in order to all elements of the logical list `l`.
2. `sllseg p q l`: denotes a singly linked list segment from address `p` to address `q`, logically corresponding to the list `l`.
3. `sllbseg x y l`: in memory there exists a singly linked list segment bounded by two second-level pointer endpoints `x` and `y`, and this segment stores all elements of the sequence `l`.
4. `dlistrep p pre l`: denotes a complete doubly linked list starting at address `p`, with predecessor pointer `pre` for the head, and containing all elements of the logical list `l` in order.
5. `dllseg x y xpre ypre l`: denotes a doubly linked list segment from address `x` to address `y`, where the predecessor of `x` is `xpre` and the predecessor of `y` is `ypre`, and the segment logically corresponds to the list `l`.

## Tactics 

The following lists auxiliary tactics, beyond Rocq's standard library, for solving logical entailments.  

1. `pre_process_default`: unfolds the VC and normalize the assertion; typically used at the start of a VC proof.

    Example:
    ```
    1 goal
  
    ============================
    sll_strategy18
    ```
    After `pre_process_default.`:
    ```
    1 goal
    
    l1 : list Z
    p, v1, q : Z
    ============================
    sllbseg p q l1 ** q # Ptr |-> v1
    |-- q # Ptr |-> v1 ** (ALL l2 : list Z, ALL v2 : Z, TT && [|l1 = l2|] && emp ** q # Ptr |-> v2 -* TT && emp ** sllbseg p q l2 ** q # Ptr |-> v2)
    ```


2. `entailer!`: extracts and solves pure propositions on the right and cancels identical atomic predicates that appear on both sides. It does not extract or solve pure propositions that are under `EX` or `ALL`.

    After `entailer!.`:
    ```
    1 goal
    
    l1 : list Z
    p, v1, q : Z
    ============================
    sllbseg p q l1
    |-- ALL l2 : list Z, ALL v2 : Z, TT && [|l1 = l2|] && emp ** q # Ptr |-> v2 -* TT && emp ** sllbseg p q l2 ** q # Ptr |-> v2
    ```

3. `Intros_r`: introduces a universally quantified variable from the right-hand side into the context; typically used to instantiate `ALL` in the goal.


    After `Intros_r l2.`:
    ```
    1 goal
    
    l1 : list Z
    p, v1, q : Z
    l2 : list Z
    ============================
    sllbseg p q l1 |-- ALL v2 : Z, TT && [|l1 = l2|] && emp ** q # Ptr |-> v2 -* TT && emp ** sllbseg p q l2 ** q # Ptr |-> v2
    ```

4. `Intros`:

    4.1. with no arguments, it moves a pure proposition from the left-hand assertion into the context.

    4.2. with one argument (e.g., `x`), it instantiates an existential on the left-hand side and introduces the witness into the context.

    Example:
    ```
    1 goal
    
    p, x : Z
    l : list Z
    ============================
    EX x0 : addr, &( p # "list" ->ₛ "data") # Int |-> x ** &( p # "list" ->ₛ "next") # Ptr |-> x0 ** sll x0 l && [|p <> NULL|]
    |-- EX y : Z, (TT && emp ** &( p # "list" ->ₛ "data") # Int |-> x ** &( p # "list" ->ₛ "next") # Ptr |-> y ** sll y l) ** (TT && emp -* TT && emp)
    ```
    After `Intros y.`:
    ```
    1 goal
    
    p, x : Z
    l : list Z
    y : addr
    H : p <> NULL
    ============================
    &( p # "list" ->ₛ "data") # Int |-> x ** (&( p # "list" ->ₛ "next") # Ptr |-> y ** sll y l)
    |-- EX y0 : Z, (TT && emp ** &( p # "list" ->ₛ "data") # Int |-> x ** &( p # "list" ->ₛ "next") # Ptr |-> y0 ** sll y0 l) ** (TT && emp -* TT && emp)
    ```

5. `Exists`: instantiates the first existential on the right-hand side with the given witness.
    
    After `Exists y.`:
    ```
    1 goal
    
    p, x : Z
    l : list Z
    y : addr
    H : p <> NULL
    ============================
    &( p # "list" ->ₛ "data") # Int |-> x ** (&( p # "list" ->ₛ "next") # Ptr |-> y ** sll y l)
    |-- (TT && emp ** &( p # "list" ->ₛ "data") # Int |-> x ** &( p # "list" ->ₛ "next") # Ptr |-> y ** sll y l) ** (TT && emp -* TT && emp)
    ```

6. `sep_apply`: finds a matching spatial subterm `A` on the left, brings it into position, and rewrites it using a hypothesis of the form `A |-- B` to replace it with `B`.

    Example:
    ```
    1 goal
  
    y, z : addr
    a : Z
    l1, l2 : list Z
    IHl1 : forall x : addr, sllseg x y l1 ** sllseg y z l2 |-- sllseg x z (l1 ++ l2)
    x, z0 : addr
    H : x <> NULL
    ============================
    &( x # "list" ->ₛ "data") # Int |-> a ** (&( x # "list" ->ₛ "next") # Ptr |-> z0 ** (sllseg z0 y l1 ** sllseg y z l2))
    |-- &( x # "list" ->ₛ "data") # Int |-> a ** &( x # "list" ->ₛ "next") # Ptr |-> z0 ** sllseg z0 z (l1 ++ l2) && [|x <> NULL|]
    ```
    After `sep_apply IHl1.`
    ```
    1 goal
  
    y, z : addr
    a : Z
    l1, l2 : list Z
    IHl1 : forall x : addr, sllseg x y l1 ** sllseg y z l2 |-- sllseg x z (l1 ++ l2)
    x, z0 : addr
    H : x <> NULL
    ============================
    sllseg z0 z (l1 ++ l2) ** (&( x # "list" ->ₛ "data") # Int |-> a ** &( x # "list" ->ₛ "next") # Ptr |-> z0)
    |-- [|x <> NULL|] && &( x # "list" ->ₛ "data") # Int |-> a ** (&( x # "list" ->ₛ "next") # Ptr |-> z0 ** sllseg z0 z (l1 ++ l2))
    ```

#### representative lemmas for `sep_apply`

You can use Rocq's `Search` to find lemmas for user-defined predicates. Below are representative examples and how `sep_apply` uses them.

0. `store_ptr_undef_store_ptr`

```coq
Lemma store_ptr_undef_store_ptr : p # Ptr |-> v |-- p # Ptr |->_.
```
**sep_apply store_ptr_undef_store_ptr**

```proof state
================
p # Ptr |-> v ** M |-- N
```
becomes
```proof state
================
p # Ptr |-> _ ** M |-- N
```


1. `empty_sll`

```coq
Lemma empty_sll : emp |-- sll 0 nil.
```

**sep_apply empty_sll**
```proof state
================
emp ** M |-- N
```
becomes
```proof state
================
sll 0 nil ** M |-- N
```

2. `sll_not_zero`

```coq
Lemma sll_not_zero: forall x l,
  x <> NULL ->
  sll x l |--
    EX y a l0,
      [| l = a :: l0 |] &&
      &(x # "list" ->? "data") # Int |-> a **
      &(x # "list" ->? "next") # Ptr |-> y **
      sll y l0.
```

**sep_apply (sll_not_zero x l)**
```proof state
H: x <> 0
================
sll x l ** M |-- N
```
becomes
```proof state
H: x <> 0
================
(EX y a l0,
  [| l = a :: l0 |] &&
  &(x # "list" ->? "data") # Int |-> a **
  &(x # "list" ->? "next") # Ptr |-> y **
  sll y l0) ** M |-- N
```

3. `sllseg_sllseg`

```coq
Lemma sllseg_sllseg: forall x y z l1 l2,
  sllseg x y l1 ** sllseg y z l2 |--
  sllseg x z (l1 ++ l2).
```

**sep_apply (sllseg_sllseg x y z l1 l2)**
```proof state
================
(sllseg x y l1 ** sllseg y z l2) ** M |-- N
```
becomes
```proof state
================
sllseg x z (l1 ++ l2) ** M |-- N
```

4. `sllbseg_2_sllseg`

```coq
Lemma sllbseg_2_sllseg: forall x y z l,
  sllbseg x y l ** y # Ptr |-> z |--
  EX y': addr, x # Ptr |-> y' ** sllseg y' z l.
```

**sep_apply (sllbseg_2_sllseg x y z l)**
```proof state
================
(sllbseg x y l ** y # Ptr |-> z) ** M |-- N
```
becomes
```proof state
================
(EX y': addr, x # Ptr |-> y' ** sllseg y' z l) ** M |-- N
```

## Tactics for solving the execution predicate

The execution predicate is a structured pure proposition. After `entailer!`, it can be extracted from the right-hand side and appear as a standalone goal. The tactics below are typical steps for discharging such goals.

1. `unfold`: Rocq's standard tactic to expand a definition, either in the goal or selected hypotheses.

    Example:
    ```proof state
    1 goal
      
    X : list Z -> unit -> Prop
    l3_2 : list Z
    x_data : Z
    l1_new : list Z
    y_data : Z
    l2_new : list Z
    H : x_data < y_data
    H4 : safeExec ATrue (merge_from_mid_rel (x_data :: l1_new) (y_data :: l2_new) l3_2) X
    ============================
    safeExec ATrue (merge_from_mid_rel l1_new (y_data :: l2_new) (l3_2 +:: x_data)) X
    ```
    After `unfold merge_from_mid_rel in *.`:
    ```proof state
    1 goal
      
    X : list Z -> unit -> Prop
    l3_2 : list Z
    x_data : Z
    l1_new : list Z
    y_data : Z
    l2_new : list Z
    H : x_data < y_data
    H4 : safeExec ATrue (repeat_break merge_body (x_data :: l1_new, y_data :: l2_new, l3_2)) X
    ============================
    safeExec ATrue (repeat_break merge_body (l1_new, y_data :: l2_new, l3_2 +:: x_data)) X
    ```

2. `unfold_loop in`: rewrites loop constructors such as `repeat_break` using its unfolding lemma inside the specified hypothesis or goal.

    After `unfold_loop in H4.`:
    ```
    1 goal
      
    X : list Z -> unit -> Prop
    l3_2 : list Z
    x_data : Z
    l1_new : list Z
    y_data : Z
    l2_new : list Z
    H : x_data < y_data
    H4 :
    safeExec ATrue
    (x <- merge_body (x_data :: l1_new, y_data :: l2_new, l3_2) ;;
    match x with
    | by_continue a0 => repeat_break merge_body a0
    | by_break b0 => return b0
    end) X
    ============================
    safeExec ATrue (repeat_break merge_body (l1_new, y_data :: l2_new, l3_2 +:: x_data)) X
    ```

3. `prog_nf`: repeatedly reassociates binds, distributes bind over `choice`, and simplifies `ret`-binds to reach a simpler normal form.

    3.1 with no arguments, normalizes the program inside the execution predicate in the goal.

    3.2 with `in H`, normalizes the program inside the execution predicate in hypothesis `H`.


    After `unfold merge_body in H4 at 1;prog_nf in H4.`:
    ```
    1 goal
      
      X : list Z -> unit -> Prop
      l3_2 : list Z
      x_data : Z
      l1_new : list Z
      y_data : Z
      l2_new : list Z
      H : x_data < y_data
      H4 :
        safeExec ATrue
          (choice
            (assume!! (x_data <= y_data) ;; repeat_break merge_body
                                              (l1_new, y_data :: l2_new, l3_2 +:: x_data))
            (assume!! (y_data <= x_data) ;; repeat_break merge_body
                                              (x_data :: l1_new, l2_new, l3_2 +:: y_data))) X
      ============================
      safeExec ATrue
        (repeat_break merge_body (l1_new, y_data :: l2_new, l3_2 +:: x_data)) X
    ```
4. `safe_choice_l` or `safe_choice_r`: chooses the left or right branch of the program in hypothesis `H` and extracts the corresponding assumption (and try to solve it with `auto`).

    you should choose the correct branch according to the context.

    After `safe_choice_l H4.`:
    ```
    2 goals
      
      X : list Z -> unit -> Prop
      l3_2 : list Z
      x_data : Z
      l1_new : list Z
      y_data : Z
      l2_new : list Z
      H : x_data < y_data
      H4 :
        safeExec ATrue
          (repeat_break merge_body (l1_new, y_data :: l2_new, l3_2 +:: x_data)) X
      ============================
      safeExec ATrue
        (repeat_break merge_body (l1_new, y_data :: l2_new, l3_2 +:: x_data)) X

    goal 2 is:
    x_data <= y_data
    ```

    This can then be solved. However, if you choose to `safe_choice_r H4`, then the goal becomes
    ```
    2 goals
  
    X : list Z -> unit -> Prop
    l3_2 : list Z
    x_data : Z
    l1_new : list Z
    y_data : Z
    l2_new : list Z
    H : x_data < y_data
    H4 :
      safeExec ATrue
        (repeat_break merge_body (x_data :: l1_new, l2_new, l3_2 +:: y_data)) X
    ============================
    safeExec ATrue
      (repeat_break merge_body (l1_new, y_data :: l2_new, l3_2 +:: x_data)) X

    goal 2 is:
    y_data <= x_data
    ```
    which is apparently unsolvable.
