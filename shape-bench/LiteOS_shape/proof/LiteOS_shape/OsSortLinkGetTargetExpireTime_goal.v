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

(*----- Function OsSortLinkGetTargetExpireTime -----*)

Definition OsSortLinkGetTargetExpireTime_safety_wit_1 := 
forall (A: Type) (targetSortList_pre: Z) (currTime_pre: Z) (t: Z) (a: A) (storeA: (Z -> (A -> Assertion))) (PreH1 : (currTime_pre >= t)) (PreH2 : (currTime_pre >= 0)) ,
  ((&((targetSortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  (storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((( &( "targetSortList" ) )) # Ptr  |-> targetSortList_pre)
  **  ((( &( "currTime" ) )) # UInt64  |-> currTime_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OsSortLinkGetTargetExpireTime_return_wit_1 := 
forall (A: Type) (targetSortList_pre: Z) (currTime_pre: Z) (t: Z) (a: A) (storeA: (Z -> (A -> Assertion))) (PreH1 : (currTime_pre < t)) (PreH2 : (currTime_pre >= 0)) ,
  ((&((targetSortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  (storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
|--
  (storesortedLinkNode storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
.

Definition OsSortLinkGetTargetExpireTime_return_wit_2 := 
forall (A: Type) (targetSortList_pre: Z) (currTime_pre: Z) (t: Z) (a: A) (storeA: (Z -> (A -> Assertion))) (PreH1 : (currTime_pre >= t)) (PreH2 : (currTime_pre >= 0)) ,
  ((&((targetSortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  (storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
|--
  (storesortedLinkNode storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
.

Definition OsSortLinkGetTargetExpireTime_partial_solve_wit_1 := 
forall (A: Type) (targetSortList_pre: Z) (currTime_pre: Z) (t: Z) (a: A) (storeA: (Z -> (A -> Assertion))) (PreH1 : (currTime_pre >= 0)) ,
  (storesortedLinkNode storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  “ (currTime_pre >= 0) ”
  &&  ((&((targetSortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  (storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
.

Module Type VC_Correct.

Include los_sortlink_shape_Strategy_Correct.

Axiom proof_of_OsSortLinkGetTargetExpireTime_safety_wit_1 : OsSortLinkGetTargetExpireTime_safety_wit_1.
Axiom proof_of_OsSortLinkGetTargetExpireTime_return_wit_1 : OsSortLinkGetTargetExpireTime_return_wit_1.
Axiom proof_of_OsSortLinkGetTargetExpireTime_return_wit_2 : OsSortLinkGetTargetExpireTime_return_wit_2.
Axiom proof_of_OsSortLinkGetTargetExpireTime_partial_solve_wit_1 : OsSortLinkGetTargetExpireTime_partial_solve_wit_1.

End VC_Correct.
