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

(*----- Function OsGetNextExpireTime -----*)

Definition OsGetNextExpireTime_return_wit_1 := 
forall (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (retval: Z) (retval_2: Z) (PreH1 : (retval >= retval_2)) ,
  (store_swtmr_sorted_dll sg l2 )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))
  **  (store_task_sorted_dll sg l1 )
|--
  (store_task_sorted_dll sg l1 )
  **  (store_swtmr_sorted_dll sg l2 )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))
.

Definition OsGetNextExpireTime_return_wit_2 := 
forall (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (retval: Z) (retval_2: Z) (PreH1 : (retval < retval_2)) ,
  (store_swtmr_sorted_dll sg l2 )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))
  **  (store_task_sorted_dll sg l1 )
|--
  (store_task_sorted_dll sg l1 )
  **  (store_swtmr_sorted_dll sg l2 )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))
.

Definition OsGetNextExpireTime_partial_solve_wit_1_pure := 
forall (tickPrecision_pre: Z) (startTime_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) ,
  ((( &( "taskExpireTime" ) )) # UInt64  |->_)
  **  ((( &( "tickPrecision" ) )) # UInt64  |-> tickPrecision_pre)
  **  ((( &( "startTime" ) )) # UInt64  |-> startTime_pre)
  **  (store_task_sorted_dll sg l1 )
  **  (store_swtmr_sorted_dll sg l2 )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))
|--
  “ (( &( "g_taskSortLink" ) ) = ( &( "g_taskSortLink" ) )) ”
.

Definition OsGetNextExpireTime_partial_solve_wit_1_aux := 
forall (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) ,
  (store_task_sorted_dll sg l1 )
  **  (store_swtmr_sorted_dll sg l2 )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))
|--
  “ (( &( "g_taskSortLink" ) ) = ( &( "g_taskSortLink" ) )) ”
  &&  (store_task_sorted_dll sg l1 )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))
  **  (store_swtmr_sorted_dll sg l2 )
.

Definition OsGetNextExpireTime_partial_solve_wit_1 := OsGetNextExpireTime_partial_solve_wit_1_pure -> OsGetNextExpireTime_partial_solve_wit_1_aux.

Definition OsGetNextExpireTime_partial_solve_wit_2_pure := 
forall (tickPrecision_pre: Z) (startTime_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (retval: Z) ,
  ((( &( "swtmrExpireTime" ) )) # UInt64  |->_)
  **  (store_task_sorted_dll sg l1 )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))
  **  ((( &( "taskExpireTime" ) )) # UInt64  |-> retval)
  **  ((( &( "tickPrecision" ) )) # UInt64  |-> tickPrecision_pre)
  **  ((( &( "startTime" ) )) # UInt64  |-> startTime_pre)
  **  (store_swtmr_sorted_dll sg l2 )
|--
  “ (( &( "g_swtmrSortLink" ) ) = ( &( "g_swtmrSortLink" ) )) ”
.

Definition OsGetNextExpireTime_partial_solve_wit_2_aux := 
forall (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) ,
  (store_task_sorted_dll sg l1 )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))
  **  (store_swtmr_sorted_dll sg l2 )
|--
  “ (( &( "g_swtmrSortLink" ) ) = ( &( "g_swtmrSortLink" ) )) ”
  &&  (store_swtmr_sorted_dll sg l2 )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))
  **  (store_task_sorted_dll sg l1 )
.

Definition OsGetNextExpireTime_partial_solve_wit_2 := OsGetNextExpireTime_partial_solve_wit_2_pure -> OsGetNextExpireTime_partial_solve_wit_2_aux.

Definition GetSortLinkNextExpireTime_derive_swmtrSpec_by_highSpec := 
forall (sortHead_pre: Z) (l_swmtrSpec: (@list (@DL_Node (@sortedLinkNode Z)))) (sg_swmtrSpec: StableGlobVars) ,
  “ (sortHead_pre = ( &( "g_swtmrSortLink" ) )) ”
  &&  (store_swtmr_sorted_dll sg_swmtrSpec l_swmtrSpec )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))
|--
EX (A: Type) ,
EX (storeA_highSpec: (Z -> (A -> Assertion))) (l_highSpec: (@list (@DL_Node (@sortedLinkNode A)))) ,
  ((store_sorted_dll storeA_highSpec &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l_highSpec )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 )))
  **
  (((store_sorted_dll storeA_highSpec &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l_highSpec )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 )))
  -*
  ((store_swtmr_sorted_dll sg_swmtrSpec l_swmtrSpec )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))))
.

Definition GetSortLinkNextExpireTime_derive_taskSpec_by_highSpec := 
forall (sortHead_pre: Z) (l_taskSpec: (@list (@DL_Node (@sortedLinkNode Z)))) (sg_taskSpec: StableGlobVars) ,
  “ (sortHead_pre = ( &( "g_taskSortLink" ) )) ”
  &&  (store_task_sorted_dll sg_taskSpec l_taskSpec )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))
|--
EX (A: Type) ,
EX (storeA_highSpec: (Z -> (A -> Assertion))) (l_highSpec: (@list (@DL_Node (@sortedLinkNode A)))) ,
  ((store_sorted_dll storeA_highSpec &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l_highSpec )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 )))
  **
  (((store_sorted_dll storeA_highSpec &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l_highSpec )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 )))
  -*
  ((store_task_sorted_dll sg_taskSpec l_taskSpec )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))))
.

Module Type VC_Correct.

Include los_sortlink_shape_Strategy_Correct.

Axiom proof_of_OsGetNextExpireTime_return_wit_1 : OsGetNextExpireTime_return_wit_1.
Axiom proof_of_OsGetNextExpireTime_return_wit_2 : OsGetNextExpireTime_return_wit_2.
Axiom proof_of_OsGetNextExpireTime_partial_solve_wit_1_pure : OsGetNextExpireTime_partial_solve_wit_1_pure.
Axiom proof_of_OsGetNextExpireTime_partial_solve_wit_1 : OsGetNextExpireTime_partial_solve_wit_1.
Axiom proof_of_OsGetNextExpireTime_partial_solve_wit_2_pure : OsGetNextExpireTime_partial_solve_wit_2_pure.
Axiom proof_of_OsGetNextExpireTime_partial_solve_wit_2 : OsGetNextExpireTime_partial_solve_wit_2.
Axiom proof_of_GetSortLinkNextExpireTime_derive_swmtrSpec_by_highSpec : GetSortLinkNextExpireTime_derive_swmtrSpec_by_highSpec.
Axiom proof_of_GetSortLinkNextExpireTime_derive_taskSpec_by_highSpec : GetSortLinkNextExpireTime_derive_taskSpec_by_highSpec.

End VC_Correct.
