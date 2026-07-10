Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.LiteOS_shape.lib.glob_vars_and_defs.
Require Import SimpleC.EE.Applications_human.LiteOS_shape.lib.Los_Verify_State_def.
Require Import SimpleC.EE.Applications_human.LiteOS_shape.lib.dll.
Require Import SimpleC.EE.Applications_human.LiteOS_shape.lib.sortlink.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition los_sortlink_shape_strategy7 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (l0 : (@list (@DL_Node A))) (x : Z),
    TT &&
    emp **
    ((store_dll storeA x l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list (@DL_Node A))),
      TT &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((store_dll storeA x l1))
      ).

Definition los_sortlink_shape_strategy14 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (l0 : (@list (@DL_Node (@sortedLinkNode A)))) (x : Z),
    TT &&
    emp **
    ((store_sorted_dll storeA x l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list (@DL_Node (@sortedLinkNode A)))),
      TT &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((store_sorted_dll storeA x l1))
      ).

Definition los_sortlink_shape_strategy15 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (py : Z) (l0 : (@list (@DL_Node A))) (px : Z),
    TT &&
    emp **
    ((dllseg_shift storeA px py l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list (@DL_Node A))),
      TT &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((dllseg_shift storeA px py l1))
      ).

Definition los_sortlink_shape_strategy18 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (a : (@sortedLinkNode A)) (x : Z),
    TT &&
    emp **
    ((storesortedLinkNode storeA x a))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((storesortedLinkNode storeA x a))
    ).

Definition los_sortlink_shape_strategy19 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (A : Type) (l : (@list (@DL_Node (@sortedLinkNode A)))) (l1 : (@list (@DL_Node (@sortedLinkNode A)))) (b : (@DL_Node (@sortedLinkNode A))) (a : (@DL_Node (@sortedLinkNode A))),
    TT &&
    (“ (a = b) ”) &&
    (“ (l = l1) ”) &&
    emp -*
    TT &&
    (“ ((@cons (@DL_Node (@sortedLinkNode A)) a l) = (@cons (@DL_Node (@sortedLinkNode A)) b l1)) ”) &&
    emp
    ).

Definition los_sortlink_shape_strategy6 :=
  forall (A : Type) (p : Z) (x : A) (storeA : (Z -> (A -> Assertion))),
    TT &&
    emp **
    ((storeA p x))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (y : A),
      TT &&
      (“ (x = y) ”) &&
      emp -*
      TT &&
      emp **
      ((storeA p y))
      ).

Definition los_sortlink_shape_strategy20 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (A1 : Type) (t : Z) (a1 : (@DL_Node (@sortedLinkNode A1))) (x : Z) (b1 : A1),
    TT &&
    (“ (x = (@ptr (@sortedLinkNode A1) a1)) ”) &&
    (“ (b1 = (@sl_data A1 (@data (@sortedLinkNode A1) a1))) ”) &&
    (“ (t = (@responseTime A1 (@data (@sortedLinkNode A1) a1))) ”) &&
    emp -*
    TT &&
    (“ (a1 = (@Build_DL_Node (@sortedLinkNode A1) (@mksortedLinkNode A1 b1 t) x)) ”) &&
    emp
    ).

Definition los_sortlink_shape_strategy21 :=
  forall (rt : Z) (h : Z) (px : Z),
    TT &&
    (“ (&( ((rt)) # "SortLinkList" ->ₛ "sortLinkNode") = h) ”) &&
    emp **
    ((poly_store FET_ptr &( ((&( ((rt)) # "SortLinkList" ->ₛ "sortLinkNode"))) # "LOS_DL_LIST" ->ₛ "pstNext") px))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = px) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_ptr &( ((h)) # "LOS_DL_LIST" ->ₛ "pstNext") v))
      ).

Definition los_sortlink_shape_strategy22 :=
  forall (A : Type) (la : Z) (re : Z) (sa : Z) (storeA : (Z -> (A -> Assertion))) (sp : Z) (l : (@list (@DL_Node (@sortedLinkNode A)))) (h : Z),
    TT &&
    emp **
    ((poly_store FET_ptr sa sp)) **
    ((poly_store FET_ptr la re)) **
    ((dllseg_shift_rev (@storesortedLinkNode A storeA) h &( ((sp)) # "SortLinkAttribute" ->ₛ "sortLink") l))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_ptr sa sp)) **
    ((poly_store FET_ptr la re))
    ) ** (
    TT &&
    (“ (h = &( ((re)) # "SortLinkList" ->ₛ "sortLinkNode")) ”) &&
    emp -*
    TT &&
    emp **
    ((dllseg_shift_rev (@storesortedLinkNode A storeA) &( ((re)) # "SortLinkList" ->ₛ "sortLinkNode") &( ((sp)) # "SortLinkAttribute" ->ₛ "sortLink") l))
    ).

Definition los_sortlink_shape_strategy17 :=
  forall (A : Type) (l0 : (@list (@DL_Node A))) (py : Z) (a : A) (storeA : (Z -> (A -> Assertion))) (x : Z) (px : Z),
    TT &&
    emp **
    ((dllseg_shift storeA x py l0)) **
    ((storeA x a)) **
    ((poly_store FET_ptr &( ((x)) # "LOS_DL_LIST" ->ₛ "pstPrev") px)) **
    ((poly_store FET_ptr &( ((px)) # "LOS_DL_LIST" ->ₛ "pstNext") x))
    |--
    (
    TT &&
    emp **
    ((dllseg_shift storeA px py (@cons (@DL_Node A) (@Build_DL_Node A a x) l0)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition los_sortlink_shape_strategy3 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (l0 : (@list (@DL_Node A))) (p : Z),
    TT &&
    emp **
    ((store_dll storeA p l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list (@DL_Node A))),
      TT &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((store_dll storeA p l1))
      ).

Definition los_sortlink_shape_strategy8 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (px : Z) (py : Z) (l0 : (@list (@DL_Node A))) (y : Z) (x : Z),
    TT &&
    emp **
    ((dllseg storeA x px y py l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list (@DL_Node A))),
      TT &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((dllseg storeA x px y py l1))
      ).

Definition los_sortlink_shape_strategy11 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (l0 : (@list (@DL_Node (@sortedLinkNode A)))) (p : Z),
    TT &&
    emp **
    ((store_sorted_dll storeA p l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list (@DL_Node (@sortedLinkNode A)))),
      TT &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((store_sorted_dll storeA p l1))
      ).

Definition los_sortlink_shape_strategy46 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (y : Z) (l0 : (@list (@DL_Node A))) (x : Z),
    TT &&
    emp **
    ((dllseg_shift_rev storeA x y l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list (@DL_Node A))),
      TT &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((dllseg_shift_rev storeA x y l1))
      ).

Definition los_sortlink_shape_strategy47 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (y : Z) (l0 : (@list (@DL_Node A))) (x0 : Z),
    TT &&
    emp **
    ((dllseg_shift_rev storeA x0 y l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list (@DL_Node A))) (x1 : Z),
      TT &&
      (“ (x0 = x1) ”) &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((dllseg_shift_rev storeA x1 y l1))
      ).

Definition los_sortlink_shape_strategy39 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (A : Type) (z : Z) (l2 : (@list (@DL_Node (@sortedLinkNode A)))) (a : A) (t : Z) (pt : Z) (storeA : (Z -> (A -> Assertion))) (x : Z) (py : Z) (l1 : (@list (@DL_Node (@sortedLinkNode A)))) (sortList : Z) (h : Z),
    TT &&
    emp **
    ((storeA &( ((sortList)) # "SortLinkList" ->ₛ "sortLinkNode") a)) **
    ((poly_store FET_uint64 &( ((sortList)) # "SortLinkList" ->ₛ "responseTime") t)) **
    ((poly_store FET_ptr &( ((&( ((sortList)) # "SortLinkList" ->ₛ "sortLinkNode"))) # "LOS_DL_LIST" ->ₛ "pstPrev") py)) **
    ((poly_store FET_ptr &( ((&( ((sortList)) # "SortLinkList" ->ₛ "sortLinkNode"))) # "LOS_DL_LIST" ->ₛ "pstNext") z)) **
    ((dllseg (@storesortedLinkNode A storeA) z &( ((sortList)) # "SortLinkList" ->ₛ "sortLinkNode") x pt (@sortedLinkNodeMappingList A l2))) **
    ((poly_store FET_ptr &( ((x)) # "LOS_DL_LIST" ->ₛ "pstPrev") pt)) **
    ((poly_store FET_ptr &( ((x)) # "LOS_DL_LIST" ->ₛ "pstNext") h)) **
    ((dllseg (@storesortedLinkNode A storeA) h x &( ((sortList)) # "SortLinkList" ->ₛ "sortLinkNode") py (@sortedLinkNodeMappingList A l1))) -*
    TT &&
    emp **
    ((store_sorted_dll storeA x (@app (@DL_Node (@sortedLinkNode A)) l1 (@cons (@DL_Node (@sortedLinkNode A)) (@Build_DL_Node (@sortedLinkNode A) (@mksortedLinkNode A a t) sortList) l2))))
    ).

Definition los_sortlink_shape_strategy44 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (task_storeA : (StableGlobVars -> (Z -> (Z -> Assertion)))) (a : Z) (sg : StableGlobVars) (t : Z) (p : Z),
    TT &&
    emp **
    ((task_storeA sg &( ((p)) # "SortLinkList" ->ₛ "sortLinkNode") a)) **
    ((poly_store FET_uint64 &( ((p)) # "SortLinkList" ->ₛ "responseTime") t)) -*
    TT &&
    emp **
    ((storesortedLinkTaskNode task_storeA sg &( ((p)) # "SortLinkList" ->ₛ "sortLinkNode") (@mksortedLinkNode Z a t)))
    ).

Definition los_sortlink_shape_strategy16 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (py : Z) (x : Z) (a : A) (l0 : (@list (@DL_Node A))) (px : Z),
    TT &&
    emp **
    ((dllseg_shift storeA px py (@cons (@DL_Node A) (@Build_DL_Node A a x) l0)))
    |--
    (
    TT &&
    emp **
    ((storeA x a)) **
    ((poly_store FET_ptr &( ((x)) # "LOS_DL_LIST" ->ₛ "pstPrev") px)) **
    ((poly_store FET_ptr &( ((px)) # "LOS_DL_LIST" ->ₛ "pstNext") x)) **
    ((dllseg_shift storeA x py l0))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition los_sortlink_shape_strategy34 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (A : Type) (storeA : (Z -> (A -> Assertion))) (x : Z) (pt : Z) (l : (@list (@DL_Node A))) (h : Z),
    TT &&
    emp **
    ((poly_store FET_ptr &( ((x)) # "LOS_DL_LIST" ->ₛ "pstPrev") pt)) **
    ((poly_store FET_ptr &( ((x)) # "LOS_DL_LIST" ->ₛ "pstNext") h)) **
    ((dllseg storeA h x x pt l)) -*
    TT &&
    emp **
    ((store_dll storeA x l))
    ).

Definition los_sortlink_shape_strategy36 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (A : Type) (storeA : (Z -> (A -> Assertion))) (l : (@list (@DL_Node (@sortedLinkNode A)))) (x : Z),
    TT &&
    emp **
    ((store_dll (@storesortedLinkNode A storeA) x (@sortedLinkNodeMappingList A l))) -*
    TT &&
    emp **
    ((store_sorted_dll storeA x l))
    ).

Definition los_sortlink_shape_strategy38 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (l2 : (@list (@DL_Node (@sortedLinkNode A)))) (t : Z) (a : A) (sortList : Z) (l1 : (@list (@DL_Node (@sortedLinkNode A)))) (x : Z),
    TT &&
    emp **
    ((store_sorted_dll storeA x (@app (@DL_Node (@sortedLinkNode A)) l1 (@cons (@DL_Node (@sortedLinkNode A)) (@Build_DL_Node (@sortedLinkNode A) (@mksortedLinkNode A a t) sortList) l2))))
    |--
    EX (h : Z) (pt : Z) (py : Z) (z : Z),
      (
      TT &&
      emp **
      ((storeA &( ((sortList)) # "SortLinkList" ->ₛ "sortLinkNode") a)) **
      ((poly_store FET_uint64 &( ((sortList)) # "SortLinkList" ->ₛ "responseTime") t)) **
      ((poly_store FET_ptr &( ((&( ((sortList)) # "SortLinkList" ->ₛ "sortLinkNode"))) # "LOS_DL_LIST" ->ₛ "pstPrev") py)) **
      ((poly_store FET_ptr &( ((&( ((sortList)) # "SortLinkList" ->ₛ "sortLinkNode"))) # "LOS_DL_LIST" ->ₛ "pstNext") z)) **
      ((dllseg (@storesortedLinkNode A storeA) z &( ((sortList)) # "SortLinkList" ->ₛ "sortLinkNode") x pt (@sortedLinkNodeMappingList A l2))) **
      ((poly_store FET_ptr &( ((x)) # "LOS_DL_LIST" ->ₛ "pstPrev") pt)) **
      ((poly_store FET_ptr &( ((x)) # "LOS_DL_LIST" ->ₛ "pstNext") h)) **
      ((dllseg (@storesortedLinkNode A storeA) h x &( ((sortList)) # "SortLinkList" ->ₛ "sortLinkNode") py (@sortedLinkNodeMappingList A l1)))
      ) ** (
      ALL (v : Z),
        TT &&
        emp **
        ((poly_store FET_uint64 &( ((sortList)) # "SortLinkList" ->ₛ "responseTime") v)) -*
        TT &&
        emp **
        ((poly_store FET_uint64 &( ((sortList)) # "SortLinkList" ->ₛ "responseTime") v))
        ).

Definition los_sortlink_shape_strategy40 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (l : (@list (@DL_Node (@sortedLinkNode A)))) (a : (@DL_Node (@sortedLinkNode A))) (x : Z),
    TT &&
    emp **
    ((store_dll (@storesortedLinkNode A storeA) x (@cons (@DL_Node (@sortedLinkNode A)) a l)))
    |--
    EX (pt : Z) (z : Z),
      (
      TT &&
      emp **
      ((poly_store FET_ptr &( ((x)) # "LOS_DL_LIST" ->ₛ "pstPrev") pt)) **
      ((poly_store FET_ptr &( ((x)) # "LOS_DL_LIST" ->ₛ "pstNext") (@ptr (@sortedLinkNode A) a))) **
      ((storesortedLinkNode storeA (@ptr (@sortedLinkNode A) a) (@data (@sortedLinkNode A) a))) **
      ((poly_store FET_ptr &( (((@ptr (@sortedLinkNode A) a))) # "LOS_DL_LIST" ->ₛ "pstPrev") x)) **
      ((poly_store FET_ptr &( (((@ptr (@sortedLinkNode A) a))) # "LOS_DL_LIST" ->ₛ "pstNext") z)) **
      ((dllseg (@storesortedLinkNode A storeA) z (@ptr (@sortedLinkNode A) a) x pt l))
      ) ** (
      ALL (v : Z) (p : Z),
        TT &&
        emp **
        ((poly_store FET_uint64 &( ((p)) # "SortLinkList" ->ₛ "responseTime") v)) -*
        TT &&
        emp **
        ((poly_store FET_uint64 &( ((p)) # "SortLinkList" ->ₛ "responseTime") v))
        ).

Definition los_sortlink_shape_strategy41 :=
  forall (A : Type) (p : Z) (nodeptr : Z) (storeA : (Z -> (A -> Assertion))) (sl : (@sortedLinkNode A)),
    TT &&
    (“ (&( ((p)) # "SortLinkList" ->ₛ "sortLinkNode") = nodeptr) ”) &&
    emp **
    ((storesortedLinkNode storeA nodeptr sl))
    |--
    (
    TT &&
    (“ (&( ((p)) # "SortLinkList" ->ₛ "sortLinkNode") = nodeptr) ”) &&
    emp **
    ((storeA nodeptr (@sl_data A sl))) **
    ((poly_store FET_uint64 &( ((p)) # "SortLinkList" ->ₛ "responseTime") (@responseTime A sl)))
    ) ** (
    ALL (v : Z),
      TT &&
      emp **
      ((poly_store FET_uint64 &( ((p)) # "SortLinkList" ->ₛ "responseTime") v)) -*
      TT &&
      emp **
      ((poly_store FET_uint64 &( ((p)) # "SortLinkList" ->ₛ "responseTime") v))
      ).

Definition los_sortlink_shape_strategy42 :=
  forall (A : Type) (p : Z) (x : Z) (mp : (@list (@DL_Node (@sortedLinkNode A)))) (l : (@list (@DL_Node (@sortedLinkNode A)))) (a : (@DL_Node (@sortedLinkNode A))),
    TT &&
    (“ (mp = (@cons (@DL_Node (@sortedLinkNode A)) a l)) ”) &&
    (“ (&( ((p)) # "SortLinkList" ->ₛ "sortLinkNode") = (@obtian_first_pointer A x mp)) ”) &&
    emp
    |--
    (
    TT &&
    (“ (mp = (@cons (@DL_Node (@sortedLinkNode A)) a l)) ”) &&
    (“ (&( ((p)) # "SortLinkList" ->ₛ "sortLinkNode") = (@obtian_first_pointer A x mp)) ”) &&
    (“ (&( ((p)) # "SortLinkList" ->ₛ "sortLinkNode") = (@ptr (@sortedLinkNode A) a)) ”) &&
    emp
    ) ** (
    ALL (v : Z),
      TT &&
      emp **
      ((poly_store FET_uint64 &( ((p)) # "SortLinkList" ->ₛ "responseTime") v)) -*
      TT &&
      emp **
      ((poly_store FET_uint64 &( ((p)) # "SortLinkList" ->ₛ "responseTime") v))
      ).

Definition los_sortlink_shape_strategy43 :=
  forall (task_storeA : (StableGlobVars -> (Z -> (Z -> Assertion)))) (p : Z) (a : Z) (t : Z) (sg : StableGlobVars),
    TT &&
    emp **
    ((storesortedLinkTaskNode task_storeA sg &( ((p)) # "SortLinkList" ->ₛ "sortLinkNode") (@mksortedLinkNode Z a t)))
    |--
    (
    TT &&
    emp **
    ((task_storeA sg &( ((p)) # "SortLinkList" ->ₛ "sortLinkNode") a)) **
    ((poly_store FET_uint64 &( ((p)) # "SortLinkList" ->ₛ "responseTime") t))
    ) ** (
    ALL (v : Z),
      TT &&
      emp **
      ((poly_store FET_uint64 &( ((p)) # "SortLinkList" ->ₛ "responseTime") v)) -*
      TT &&
      emp **
      ((poly_store FET_uint64 &( ((p)) # "SortLinkList" ->ₛ "responseTime") v))
      ).

Definition los_sortlink_shape_strategy45 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (l : (@list (@DL_Node A))) (x : Z),
    TT &&
    emp **
    ((store_dll storeA x l))
    |--
    EX (xn : Z),
      (
      TT &&
      emp **
      ((poly_store FET_ptr &( ((x)) # "LOS_DL_LIST" ->ₛ "pstNext") xn)) **
      ((poly_store FET_ptr &( ((xn)) # "LOS_DL_LIST" ->ₛ "pstPrev") x)) **
      ((dllseg_shift_rev storeA xn x l))
      ) ** (
      ALL (target_l : (@list (@DL_Node A))),
        TT &&
        emp **
        ((dllseg_shift_rev storeA xn x target_l)) -*
        TT &&
        emp **
        ((dllseg_shift_rev storeA xn x target_l))
        ).

Definition los_sortlink_shape_strategy33 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (l : (@list (@DL_Node A))) (x : Z),
    TT &&
    emp **
    ((store_dll storeA x l))
    |--
    EX (h : Z) (pt : Z),
      (
      TT &&
      emp **
      ((poly_store FET_ptr &( ((x)) # "LOS_DL_LIST" ->ₛ "pstPrev") pt)) **
      ((poly_store FET_ptr &( ((x)) # "LOS_DL_LIST" ->ₛ "pstNext") h)) **
      ((dllseg storeA h x x pt l))
      ) ** (
      ALL (q : Z),
        TT &&
        emp **
        ((poly_store FET_ptr &( ((x)) # "LOS_DL_LIST" ->ₛ "pstNext") q)) -*
        TT &&
        emp **
        ((poly_store FET_ptr &( ((x)) # "LOS_DL_LIST" ->ₛ "pstNext") q))
        ).

Definition los_sortlink_shape_strategy35 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (l : (@list (@DL_Node (@sortedLinkNode A)))) (x : Z),
    TT &&
    emp **
    ((store_sorted_dll storeA x l))
    |--
    (
    TT &&
    emp **
    ((store_dll (@storesortedLinkNode A storeA) x (@sortedLinkNodeMappingList A l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition los_sortlink_shape_strategy31 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (t : Z) (a : A) (p : Z),
    TT &&
    emp **
    ((storesortedLinkNode storeA &( ((p)) # "SortLinkList" ->ₛ "sortLinkNode") (@mksortedLinkNode A a t)))
    |--
    (
    TT &&
    emp **
    ((storeA &( ((p)) # "SortLinkList" ->ₛ "sortLinkNode") a)) **
    ((poly_store FET_uint64 &( ((p)) # "SortLinkList" ->ₛ "responseTime") t))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition los_sortlink_shape_strategy32 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (A : Type) (storeA : (Z -> (A -> Assertion))) (a : A) (t : Z) (p : Z),
    TT &&
    emp **
    ((storeA &( ((p)) # "SortLinkList" ->ₛ "sortLinkNode") a)) **
    ((poly_store FET_uint64 &( ((p)) # "SortLinkList" ->ₛ "responseTime") t)) -*
    TT &&
    emp **
    ((storesortedLinkNode storeA &( ((p)) # "SortLinkList" ->ₛ "sortLinkNode") (@mksortedLinkNode A a t)))
    ).

Definition los_sortlink_shape_strategy37 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (l : (@list (@DL_Node A))) (x : Z),
    TT &&
    emp **
    ((store_dll storeA x l))
    |--
    EX (pt : Z),
      (
      TT &&
      emp **
      ((poly_store FET_ptr &( ((x)) # "LOS_DL_LIST" ->ₛ "pstPrev") pt)) **
      ((poly_store FET_ptr &( ((pt)) # "LOS_DL_LIST" ->ₛ "pstNext") x)) **
      ((dllseg_shift storeA x pt l))
      ) ** (
      TT &&
      emp **
      ((poly_store FET_ptr &( ((x)) # "LOS_DL_LIST" ->ₛ "pstPrev") pt)) -*
      TT &&
      emp **
      ((poly_store FET_ptr &( ((x)) # "LOS_DL_LIST" ->ₛ "pstPrev") pt))
      ).

Definition los_sortlink_shape_strategy48 :=
  forall (A : Type) (px : Z) (py : Z) (y : Z) (x : Z) (storeA : (Z -> (A -> Assertion))),
    TT &&
    emp **
    ((dllseg storeA x px y py (@nil (@DL_Node A))))
    |--
    (
    TT &&
    (“ (x = y) ”) &&
    (“ (px = py) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition los_sortlink_shape_strategy49 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (A : Type) (px : Z) (py : Z) (y : Z) (x : Z) (storeA : (Z -> (A -> Assertion))),
    TT &&
    (“ (x = y) ”) &&
    (“ (px = py) ”) &&
    emp -*
    TT &&
    emp **
    ((dllseg storeA x px y py (@nil (@DL_Node A))))
    ).

Definition los_sortlink_shape_strategy50 :=
  forall (A : Type) (px : Z) (py : Z) (storeA : (Z -> (A -> Assertion))),
    TT &&
    emp **
    ((dllseg_shift storeA px py (@nil (@DL_Node A))))
    |--
    (
    TT &&
    (“ (px = py) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition los_sortlink_shape_strategy51 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (A : Type) (px : Z) (py : Z) (storeA : (Z -> (A -> Assertion))),
    TT &&
    (“ (px = py) ”) &&
    emp -*
    TT &&
    emp **
    ((dllseg_shift storeA px py (@nil (@DL_Node A))))
    ).

Definition los_sortlink_shape_strategy52 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (A : Type) (x : Z) (py : Z) (a : A) (storeA : (Z -> (A -> Assertion))) (px : Z),
    TT &&
    (“ (x = py) ”) &&
    emp **
    ((storeA x a)) **
    ((poly_store FET_ptr &( ((x)) # "LOS_DL_LIST" ->ₛ "pstPrev") px)) **
    ((poly_store FET_ptr &( ((px)) # "LOS_DL_LIST" ->ₛ "pstNext") x)) -*
    TT &&
    emp **
    ((dllseg_shift storeA px py (@cons (@DL_Node A) (@Build_DL_Node A a x) (@nil (@DL_Node A)))))
    ).

Module Type los_sortlink_shape_Strategy_Correct.

  Axiom los_sortlink_shape_strategy7_correctness : los_sortlink_shape_strategy7.
  Axiom los_sortlink_shape_strategy14_correctness : los_sortlink_shape_strategy14.
  Axiom los_sortlink_shape_strategy15_correctness : los_sortlink_shape_strategy15.
  Axiom los_sortlink_shape_strategy18_correctness : los_sortlink_shape_strategy18.
  Axiom los_sortlink_shape_strategy19_correctness : los_sortlink_shape_strategy19.
  Axiom los_sortlink_shape_strategy6_correctness : los_sortlink_shape_strategy6.
  Axiom los_sortlink_shape_strategy20_correctness : los_sortlink_shape_strategy20.
  Axiom los_sortlink_shape_strategy21_correctness : los_sortlink_shape_strategy21.
  Axiom los_sortlink_shape_strategy22_correctness : los_sortlink_shape_strategy22.
  Axiom los_sortlink_shape_strategy17_correctness : los_sortlink_shape_strategy17.
  Axiom los_sortlink_shape_strategy3_correctness : los_sortlink_shape_strategy3.
  Axiom los_sortlink_shape_strategy8_correctness : los_sortlink_shape_strategy8.
  Axiom los_sortlink_shape_strategy11_correctness : los_sortlink_shape_strategy11.
  Axiom los_sortlink_shape_strategy46_correctness : los_sortlink_shape_strategy46.
  Axiom los_sortlink_shape_strategy47_correctness : los_sortlink_shape_strategy47.
  Axiom los_sortlink_shape_strategy39_correctness : los_sortlink_shape_strategy39.
  Axiom los_sortlink_shape_strategy44_correctness : los_sortlink_shape_strategy44.
  Axiom los_sortlink_shape_strategy16_correctness : los_sortlink_shape_strategy16.
  Axiom los_sortlink_shape_strategy34_correctness : los_sortlink_shape_strategy34.
  Axiom los_sortlink_shape_strategy36_correctness : los_sortlink_shape_strategy36.
  Axiom los_sortlink_shape_strategy38_correctness : los_sortlink_shape_strategy38.
  Axiom los_sortlink_shape_strategy40_correctness : los_sortlink_shape_strategy40.
  Axiom los_sortlink_shape_strategy41_correctness : los_sortlink_shape_strategy41.
  Axiom los_sortlink_shape_strategy42_correctness : los_sortlink_shape_strategy42.
  Axiom los_sortlink_shape_strategy43_correctness : los_sortlink_shape_strategy43.
  Axiom los_sortlink_shape_strategy45_correctness : los_sortlink_shape_strategy45.
  Axiom los_sortlink_shape_strategy33_correctness : los_sortlink_shape_strategy33.
  Axiom los_sortlink_shape_strategy35_correctness : los_sortlink_shape_strategy35.
  Axiom los_sortlink_shape_strategy31_correctness : los_sortlink_shape_strategy31.
  Axiom los_sortlink_shape_strategy32_correctness : los_sortlink_shape_strategy32.
  Axiom los_sortlink_shape_strategy37_correctness : los_sortlink_shape_strategy37.
  Axiom los_sortlink_shape_strategy48_correctness : los_sortlink_shape_strategy48.
  Axiom los_sortlink_shape_strategy49_correctness : los_sortlink_shape_strategy49.
  Axiom los_sortlink_shape_strategy50_correctness : los_sortlink_shape_strategy50.
  Axiom los_sortlink_shape_strategy51_correctness : los_sortlink_shape_strategy51.
  Axiom los_sortlink_shape_strategy52_correctness : los_sortlink_shape_strategy52.

End los_sortlink_shape_Strategy_Correct.
