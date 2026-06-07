---
name: vc-proving
description: 使用两套 tactic 配合 Rocq MCP 完成分离逻辑验证条件（VC）的证明
---

# VC 证明 Tactics

我们提供两套 tactics 来证明 VC：

1. **whole-proof tactics**：原子化、细粒度，每个 tactic 的证明状态变化完全可预测，适合一次性生成完整的长证明。
2. **step-by-step tactics**：自动化程度更高，适合局部使用——当 whole-proof 证明中某步出错时，可切换到这套 tactics 在局部快速探索，单步调试，无需精确实例化所有参数，适合局部快速完成证明。

---

# Whole-proof Tactics

**术语说明**：
- 在证明结论 `P |-- Q` 中，P 称为**前条件**，Q 称为**后条件**
- **前提**指 Coq 中的 Hypothesis

## 1. `pre_process`

**功能**：展开定义、引入变量、提取前条件中的纯命题。

**用途**：每个证明开头必用。

**注意**：一般而言，每个证明会帮你做好 `pre_process` 这一步，你无需自己调用，只需顺着它继续推进证明。

## 2. `Intros x` / `Intros x y ...`

**功能**：引入前条件中 `EX` 修饰的变量，命名为 x。

**示例（证明状态变化）**：

使用前：
```proof state
条件...
===============================
EX n, [|n > 0|] && sll p l |-- ...
```

使用：`Intros n.`

使用后：
```proof state
条件...
n : nat
===============================
[|n > 0|] && sll p l |-- ...
```

## 3. `Intros_p H`

**功能**：引入前条件中的纯命题 `[| P |]`，命名为 `H`。

**示例（证明状态变化）**：

使用前：
```proof state
条件...
===============================
[|n > 0|] && sll p l |-- ...
```

使用：`Intros_p H.`

使用后：
```proof state
条件...
H: n > 0
===============================
sll p l |-- ...
```

## 4. `Exists x` / `Exists x y ...`

**功能**：实例化后条件中的存在量词。

**示例（证明状态变化）**：

使用前：
```proof state
条件...
l_1 : list
l_2 : list
===============================
sll p l |-- EX l1 l2, [|l = l1 ++ l2|] && ...
```

使用：`Exists l_1 l_2.`

使用后：
```proof state
条件...
l_1 : list
l_2 : list
===============================
sll p l |-- [|l = l_1 ++ l_2|] && ...
```

## 5. `cancel P`

**功能**：消去前后条件中形式相同的空间谓词 `P`；若不严格匹配则报错。

**示例（证明状态变化）**：

使用前：
```proof state
条件...
===============================
sll p l |-- sllseg p p nil ** sll p l
```

使用：`cancel (sll p l).`

使用后：
```proof state
条件...
===============================
emp |-- sllseg p p nil
```

**注意**：
1. 前后条件的空间谓词 `P` 需严格（形式上）相同，仅语义相同不能通过；`cancel` 不做任何化简。
2. 当前后条件只剩一个相同谓词如 `P |-- P` 时，`cancel P` 直接完成目标，不会再产生 `emp |-- emp`，因此无需再使用 `cancel emp`。

## 6. `sep_apply_l_atomic`

**功能**：应用分离逻辑引理变换前条件，需显式实例化所有变量。若引理形如 `H: forall x: T, C -> P ** Q |-- R`，使用 `sep_apply_l_atomic (H x)` 会：
1. 将前条件中的 `P ** Q` 替换为 `R`
2. 若引理有 Prop 前提 `C`，生成子目标 `前条件 |-- [| C |]` 供手动证明

注意：此 tactic 强制要求显式实例化引理中的所有变量，否则报错；但无需提供前提 `C` 的证明，会自动生成子目标。

**示例（证明状态变化）**：

**场景1：引理无 Prop 前提**
```coq
Lemma sllseg_sll: forall x y l1 l2,
  sllseg x y l1 ** sll y l2 |--
  sll x (l1 ++ l2).
```

使用前：
```proof state
p: Z
l1, l2: list
===============================
sllseg p q l1 ** sll q l2 ** M |-- N
```

使用：`sep_apply_l_atomic (sllseg_sll p q l1 l2).`

使用后（只有一个目标）：
```proof state
p: Z
l1, l2: list
===============================
sll p (l1 ++ l2) ** M |-- N
```

**场景2：引理有 Prop 前提**
```coq
Lemma sll_not_zero: forall x l,
  x <> NULL ->
  sll x l |--
    EX y a l0,
      [| l = a :: l0 |] &&
      &(x # "list" ->ₛ "data") # Int |-> a **
      &(x # "list" ->ₛ "next") # Ptr |-> y **
      sll y l0.
```

使用前：
```proof state
p: Z
l: list
===============================
sll p l ** M |-- N
```

使用：`sep_apply_l_atomic (sll_not_zero p l).`

使用后（生成两个子目标）：

子目标1（纯命题子目标，需手动证明）：
```proof state
p: Z
l: list
===============================
sll p l ** M |-- [| p <> NULL |]
```

子目标2（主目标，假设前提成立后的结果）：
```proof state
p: Z
l: list
===============================
(EX y a l0,
  [| l = a :: l0 |] &&
  &(p # "list" ->ₛ "data") # Int |-> a **
  &(p # "list" ->ₛ "next") # Ptr |-> y **
  sll y l0) ** M |-- N
```

## 7. `sep_apply_r_atomic`

**功能**：应用分离逻辑引理变换后条件，需显式实例化所有变量。若引理形如 `H: forall x: T, C -> P ** Q |-- R`，使用 `sep_apply_r_atomic (H x)` 会：
1. 将后条件中的 `R` 替换为 `P ** Q`
2. 若引理有 Prop 前提 `C`，生成子目标 `前条件 |-- [| C |]` 供手动证明

注意：此 tactic 强制要求显式实例化引理中的所有变量，否则报错；但无需提供前提 `C` 的证明，会自动生成子目标。

**示例（证明状态变化）**：

**场景1：引理无 Prop 前提**
```coq
Lemma nil_sllseg_l: forall p q,
  [| p = q |] && emp |-- sllseg p q nil.
```

使用前：
```proof state
p: Z
===============================
M |-- N ** sllseg p p nil
```

使用：`sep_apply_r_atomic (nil_sllseg_l p p).`

使用后（只有一个目标）：
```proof state
p: Z
===============================
M |-- N ** ([| p = p |] && emp)
```

**场景2：引理有 Prop 前提**
```coq
Lemma cons_sll_l: forall x a l y,
  x <> NULL ->
  &(x # "list" ->ₛ "data") # Int |-> a **
  &(x # "list" ->ₛ "next") # Ptr |-> y **
  sll y l |--
  sll x (a :: l).
```

使用前：
```proof state
p: Z
a: Z
l: list
y: addr
===============================
M |-- N ** sll p (a :: l)
```

使用：`sep_apply_r_atomic (cons_sll_l p a l y).`

使用后（生成两个子目标）：

子目标1（纯命题子目标）：
```proof state
p: Z
a: Z
l: list
y: addr
===============================
M |-- [| p <> NULL |]
```

子目标2（主目标）：
```proof state
p: Z
a: Z
l: list
y: addr
===============================
M |-- N ** (&(p # "list" ->ₛ "data") # Int |-> a **
            &(p # "list" ->ₛ "next") # Ptr |-> y **
            sll y l)
```

## 8. `prop_apply_p`

**功能**：利用前条件中的命题推导新纯命题并加入前条件。若引理形如 `H: forall x: T, C -> P ** Q |-- [| R |]`，且证明目标形如 `P ** Q ** M |-- N`，使用 `prop_apply_p (H x C)` 会在前条件中添加 `[| R |]`。

注意：此 tactic 强制要求显式实例化引理中的所有变量和前提，否则报错。

**示例（证明状态变化）**：
```coq
Lemma sll_not_zero': forall x l,
  x <> NULL ->
  sll x l |-- [| l <> nil |].
```

使用前：
```proof state
p: Z
l: list
H: x <> NULL
===============================
sll p l ** Q |-- R
```

使用：`prop_apply_p (sll_not_zero' p l H).`

使用后：
```proof state
p: Z
l: list
H: x <> NULL
===============================
[| l <> nil |] && sll p l ** Q |-- R
```

## 9. `Left` / `Right` / `Split`

- **`Left`**：将 `P |-- Q || R` 变为 `P |-- Q`
- **`Right`**：将 `P |-- Q || R` 变为 `P |-- R`
- **`Split`**：将 `P || Q |-- R` 拆为两个子目标：`P |-- R` 和 `Q |-- R`

**示例（`Left` 证明状态变化）**：

使用前：
```proof state
===============================
P |-- Q || R
```

使用：`Left.`

使用后：
```proof state
===============================
P |-- Q
```

## 10. `split_pures.`

**功能**：将合取的纯命题目标拆分为多个子目标，逐一处理。

**用途**：纯命题证明开头必用。

**示例（证明状态变化）**：

使用前：
```proof state
条件...
H: n = 0
===============================
sll p l |-- [| l1 = l2 |] && [| n = 0 |]
```

使用：`split_pures.`

使用后：

子目标1：
```proof state
条件...
H: n = 0
===============================
sll p l |-- [| l1 = l2 |]
```

子目标2：
```proof state
条件...
H: n = 0
===============================
sll p l |-- [| n = 0 |]
```

## 11. `dump_pre_spatial`

**功能**：在准备好所有纯命题前提后，丢弃前条件中的空间命题，进入纯命题证明模式。即在条件不变的情况下，将证明状态从 `P |-- [| Q |]` 变为 `Q`。

**示例（证明状态变化）**：

使用前：
```proof state
条件...
===============================
sll p l |-- [| l1 = l2 |]
```

使用：`dump_pre_spatial.`

使用后：
```proof state
条件...
===============================
l1 = l2
```

## 示例证明

```rocq
Definition length_entail_wit_2 :=
forall (p_pre: Z) (l: (@list Z)) (p: Z) (n: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (p_next: Z) (p_data: Z) (l3: (@list Z)) ,
  [| (l2_2 = (cons (p_data) (l3))) |]
  &&  [| (p <> 0) |]
  &&  [| (l = (app (l1_2) (l2_2))) |]
  &&  [| (n = (Zlength (l1_2))) |]
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> p_data)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l3 )
  **  (sllseg p_pre p l1_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (l = (app (l1) (l2))) |]
  &&  [| ((n + 1 ) = (Zlength (l1))) |]
  &&  [| ((Zlength (l)) <= INT_MAX) |]
  &&  (sllseg p_pre p_next l1 )
  **  (sll p_next l2 )
.

Lemma proof_of_length_entail_wit_2 : length_entail_wit_2.
Proof.
  pre_process.
  Exists (l1_2 ++ (p_data :: nil)) l3.
  split_pure_spatial.
  - cancel (sll p_next l3).
    sep_apply_l_atomic (sllseg_len1 p p_data p_next).
    + dump_pre_spatial.
      unfold NULL.
      assumption.
    + sep_apply_l_atomic (sllseg_sllseg p_pre p p_next l1_2 (p_data :: nil)).
      cancel (sllseg p_pre p_next (l1_2 ++ (p_data :: nil))).
  - split_pures.
    + dump_pre_spatial.
      rewrite H in H1.
      rewrite H1.
      assert (forall (A: Type) (l1: list A) (a: A) (l2: list A), (l1 ++ a :: nil) ++ l2 = l1 ++ a :: l2).
      { intros A l1 a l2.
        induction l1; simpl.
        - reflexivity.
        - rewrite IHl1.
          reflexivity. }
      rewrite (H4 _ l1_2 p_data l3).
      reflexivity.
    + dump_pre_spatial.
      rewrite Zlength_app.
      rewrite Zlength_cons, Zlength_nil.
      rewrite H2.
      lia.
    + dump_pre_spatial.
      assumption.
Qed.
```

---

# Step-by-step Tactics

自动化程度更高，适合局部使用。相比 whole-proof 版本，参数实例化要求更宽松，剩余参数可由 Coq 自动推断。

**术语说明**（同 whole-proof tactics）

## `Intros` / `Intros x` / `Intros x y ...`

- `Intros`：将前条件中的纯命题引入到前提中
- `Intros x`：将前条件中 `EX` 修饰的变量实例化，命名为 x 引入前提
- `Intros_any`：同上，名字由 Coq 自动生成

## `Intros_r x` / `Intros_r_any`

**功能**：将后条件中的 forall 变量实例化引入前提。

## `Exists x` / `Exists_l x`

- `Exists x`：将后条件中的存在变量填为 x
- `Exists_l x`：将前条件中的 forall 变量填为 x

## `entailer!`

**功能**：强力自动化 tactic，可自动消去前后条件中相同的空间谓词、处理纯命题、化简目标。不确定下一步时可优先尝试。**请单步使用**

## `sep_apply H`

**功能**：使用引理 H 变换前条件，形如 `P ** Q |-- R`，将前条件中的 `P ** Q` 替换为 `R`。相比 whole-proof 版本，无需完整实例化参数，Coq 可自动推断剩余参数。**请单步使用**

## `prop_apply H`

**功能**：使用引理 H 变换结论，形如 `P ** Q |-- [| R |]`，将 `[| R |]` 添加到前条件。相比 whole-proof 版本，无需完整实例化参数，Coq 可自动推断剩余参数。**请单步使用**

## 示例证明

```rocq
Lemma proof_of_length_entail_wit_2 : length_entail_wit_2.
Proof.
  pre_process.
  Exists (l1_2 ++ (p_data::nil)) l3.
  entailer!; simpl.
  - sep_apply sllseg_len1; try easy.
    rewrite logic_equiv_sepcon_comm.
    sep_apply sllseg_sllseg.
    easy.
  - rewrite Zlength_app.
    rewrite <- H1.
    rewrite Zlength_cons. rewrite Zlength_nil. lia.
  - rewrite H0, H; clear H H0.
    rename l1_2 into l1.
    revert l1 H1.
    induction l3; intros; simpl.
    + rewrite app_nil_r. auto.
    + rewrite <- app_assoc. simpl. f_equal.
Qed.
```

---

# 标准 Rocq Tactics

除上述 QCP 专用 tactics 外，还可以并且推荐使用以下标准 Rocq tactics：

```
lia.  nia.  intros  pose proof  unfold  reflexivity.  apply  assert
rewrite  destruct  discriminate  injection  induction  revert
inversion  symmetry  auto  tauto  easy  split
```

## `destruct`， `induction`
在使用这两个tactic的时候要注意 `as [ | ]`的写法中`|`与`[]`之间要有空格，不然会有notation冲突。
