Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.LiteOS_shape.lib.glob_vars_and_defs.
Require Import SimpleC.EE.Applications_human.LiteOS_shape.lib.Los_Verify_State_def.
Require Import SimpleC.EE.Applications_human.LiteOS_shape.lib.sortlink.
Require Import SimpleC.EE.Applications_human.LiteOS_shape.lib.dll.
Require Import SimpleC.EE.Applications_human.LiteOS_shape.lib.tick_backup.
Local Open Scope sac.
From SimpleC.EE.Applications_human Require Import los_sortlink_shape_strategy_goal.
From SimpleC.EE.Applications_human Require Import los_sortlink_shape_strategy_proof.

(*----- Function LOS_ListAdd -----*)

Definition LOS_ListAdd_return_wit_1 := 
forall (A: Type) (node_pre: Z) (list_pre: Z) (list_pstNext_low_level_spec: Z) (a_low_level_spec: A) (storeA_low_level_spec: (Z -> (A -> Assertion))) ,
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> list_pre)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pstNext_low_level_spec)
  **  (storeA_low_level_spec node_pre a_low_level_spec )
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> node_pre)
  **  ((&((list_pstNext_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> node_pre)
|--
  ((&((list_pstNext_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pstNext_low_level_spec)
  **  (dllseg_shift storeA_low_level_spec list_pre node_pre (cons ((Build_DL_Node (a_low_level_spec) (node_pre))) ((@nil (@DL_Node A)))) )
.

(*----- Function LOS_ListTailInsert -----*)

Definition LOS_ListTailInsert_return_wit_1 := 
forall (A: Type) (node_pre: Z) (list_pre: Z) (a: A) (l: (@list (@DL_Node A))) (storeA: (Z -> (A -> Assertion))) (pt_2: Z) ,
  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pre)
  **  (dllseg_shift storeA pt_2 node_pre (cons ((Build_DL_Node (a) (node_pre))) ((@nil (@DL_Node A)))) )
  **  (dllseg_shift storeA list_pre pt_2 l )
|--
  EX (pt: Z) ,
  (dllseg_shift storeA list_pre pt l )
  **  (dllseg_shift storeA pt node_pre (cons ((Build_DL_Node (a) (node_pre))) ((@nil (@DL_Node A)))) )
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pre)
.

Definition LOS_ListTailInsert_partial_solve_wit_1 := 
forall (A: Type) (node_pre: Z) (list_pre: Z) (a: A) (l: (@list (@DL_Node A))) (storeA: (Z -> (A -> Assertion))) (pu: Z) (un: Z) ,
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> un)
  **  (storeA node_pre a )
  **  (store_dll storeA list_pre l )
|--
  EX (pt: Z) ,
  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg_shift storeA list_pre pt l )
  **  ((&((pt)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pre)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> un)
  **  (storeA node_pre a )
.

Definition LOS_ListTailInsert_partial_solve_wit_2 := 
forall (A: Type) (node_pre: Z) (list_pre: Z) (a: A) (l: (@list (@DL_Node A))) (storeA: (Z -> (A -> Assertion))) (pu: Z) (un: Z) (pt: Z) ,
  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg_shift storeA list_pre pt l )
  **  ((&((pt)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pre)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> un)
  **  (storeA node_pre a )
|--
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> un)
  **  (storeA node_pre a )
  **  ((&((pt)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pre)
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg_shift storeA list_pre pt l )
.

(*----- Function LOS_ListHeadInsert -----*)

Definition LOS_ListHeadInsert_return_wit_1 := 
forall (A: Type) (node_pre: Z) (list_pre: Z) (l: (@list (@DL_Node A))) (storeA: (Z -> (A -> Assertion))) (a: A) ,
  (store_dll storeA list_pre (cons ((Build_DL_Node (a) (node_pre))) (l)) )
|--
  (store_dll storeA list_pre (cons ((Build_DL_Node (a) (node_pre))) (l)) )
.

Definition LOS_ListHeadInsert_partial_solve_wit_1 := 
forall (A: Type) (node_pre: Z) (list_pre: Z) (l: (@list (@DL_Node A))) (storeA: (Z -> (A -> Assertion))) (a: A) (pu: Z) (un: Z) ,
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> un)
  **  (storeA node_pre a )
  **  (store_dll storeA list_pre l )
|--
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> un)
  **  (storeA node_pre a )
  **  (store_dll storeA list_pre l )
.

Definition LOS_ListAdd_derive_high_level_spec_by_low_level_spec := 
forall (A: Type) ,
forall (node_pre: Z) (list_pre: Z) (a_high_level_spec: A) (l_high_level_spec: (@list (@DL_Node A))) (storeA1_high_level_spec: (Z -> (A -> Assertion))) ,
  EX un pu,
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> un)
  **  (storeA1_high_level_spec node_pre a_high_level_spec )
  **  (store_dll storeA1_high_level_spec list_pre l_high_level_spec )
|--
EX (A: Type) ,
EX (storeA_low_level_spec: (Z -> (A -> Assertion))) (a_low_level_spec: A) (list_pstNext_low_level_spec: Z) ,
  (EX un_2 pu_2,
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pu_2)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> un_2)
  **  (storeA_low_level_spec node_pre a_low_level_spec )
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pstNext_low_level_spec)
  **  ((&((list_pstNext_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> list_pre))
  **
  ((((&((list_pstNext_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pstNext_low_level_spec)
  **  (dllseg_shift storeA_low_level_spec list_pre node_pre (cons ((Build_DL_Node (a_low_level_spec) (node_pre))) (nil)) ))
  -*
  ((store_dll storeA1_high_level_spec list_pre (cons ((Build_DL_Node (a_high_level_spec) (node_pre))) (l_high_level_spec)) )))
.

Module Type VC_Correct.

Include los_sortlink_shape_Strategy_Correct.

Axiom proof_of_LOS_ListAdd_return_wit_1 : LOS_ListAdd_return_wit_1.
Axiom proof_of_LOS_ListTailInsert_return_wit_1 : LOS_ListTailInsert_return_wit_1.
Axiom proof_of_LOS_ListTailInsert_partial_solve_wit_1 : LOS_ListTailInsert_partial_solve_wit_1.
Axiom proof_of_LOS_ListTailInsert_partial_solve_wit_2 : LOS_ListTailInsert_partial_solve_wit_2.
Axiom proof_of_LOS_ListHeadInsert_return_wit_1 : LOS_ListHeadInsert_return_wit_1.
Axiom proof_of_LOS_ListHeadInsert_partial_solve_wit_1 : LOS_ListHeadInsert_partial_solve_wit_1.
Axiom proof_of_LOS_ListAdd_derive_high_level_spec_by_low_level_spec : LOS_ListAdd_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
