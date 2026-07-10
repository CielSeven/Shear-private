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

(*----- Function GET_SORTLIST_VALUE -----*)

Definition GET_SORTLIST_VALUE_return_wit_1 := 
forall (A: Type) (sortList_pre: Z) (storeA: (Z -> (A -> Assertion))) (t: Z) (a: A) ,
  ((&((sortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  (storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
|--
  “ (t = t) ”
  &&  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
.

Definition GET_SORTLIST_VALUE_partial_solve_wit_1 := 
forall (A: Type) (sortList_pre: Z) (storeA: (Z -> (A -> Assertion))) (t: Z) (a: A) ,
  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  ((&((sortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  (storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
.

(*----- Function SET_SORTLIST_VALUE -----*)

Definition SET_SORTLIST_VALUE_return_wit_1 := 
forall (A: Type) (value_pre: Z) (sortList_pre: Z) (storeA: (Z -> (A -> Assertion))) (a: A) ,
  ((&((sortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> value_pre)
  **  (storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
|--
  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (value_pre)) )
.

Definition SET_SORTLIST_VALUE_partial_solve_wit_1 := 
forall (A: Type) (sortList_pre: Z) (storeA: (Z -> (A -> Assertion))) (t: Z) (a: A) ,
  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  ((&((sortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |->_)
  **  (storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
.

Module Type VC_Correct.

Include los_sortlink_shape_Strategy_Correct.

Axiom proof_of_GET_SORTLIST_VALUE_return_wit_1 : GET_SORTLIST_VALUE_return_wit_1.
Axiom proof_of_GET_SORTLIST_VALUE_partial_solve_wit_1 : GET_SORTLIST_VALUE_partial_solve_wit_1.
Axiom proof_of_SET_SORTLIST_VALUE_return_wit_1 : SET_SORTLIST_VALUE_return_wit_1.
Axiom proof_of_SET_SORTLIST_VALUE_partial_solve_wit_1 : SET_SORTLIST_VALUE_partial_solve_wit_1.

End VC_Correct.
