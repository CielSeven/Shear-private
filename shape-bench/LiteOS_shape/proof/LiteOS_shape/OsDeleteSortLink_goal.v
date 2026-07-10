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

(*----- Function OsDeleteSortLink -----*)

Definition OsDeleteSortLink_safety_wit_1 := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (h: Z) (pt: Z) (py: Z) (z: Z) ,
  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  (dllseg (storesortedLinkNode (storeA)) h x &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") py (sortedLinkNodeMappingList (l1)) )
  **  ((&((x)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((x)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) z &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") x pt (sortedLinkNodeMappingList (l2)) )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> z)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> py)
  **  (storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition OsDeleteSortLink_safety_wit_2 := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (h: Z) (pt: Z) (py: Z) (z: Z) ,
  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  (dllseg (storesortedLinkNode (storeA)) h x &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") py (sortedLinkNodeMappingList (l1)) )
  **  ((&((x)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((x)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) z &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") x pt (sortedLinkNodeMappingList (l2)) )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> z)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> py)
  **  (storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition OsDeleteSortLink_return_wit_1 := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (v_5: Z) (v_6: Z) (PreH1 : (v_6 = 0)) (PreH2 : (v_5 = 0)) (PreH3 : (t <= g)) (PreH4 : (t <> (unsigned_last_nbits ((-1)) (64)))) ,
  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_6)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v_5)
  **  (storesortedLinkNode storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) ((unsigned_last_nbits ((-1)) (64)))) )
  **  (store_sorted_dll storeA x (app (l1) (l2)) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> o)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  EX (v_4: Z)  (v_3: Z) ,
  “ (t <> (unsigned_last_nbits ((-1)) (64))) ” 
  &&  “ (t <= g) ” 
  &&  “ (v_3 = 0) ” 
  &&  “ (v_4 = 0) ”
  &&  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> o)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_3)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v_4)
  **  (storesortedLinkNode storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) ((unsigned_last_nbits ((-1)) (64)))) )
  **  (store_sorted_dll storeA x (app (l1) (l2)) )
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
.

Definition OsDeleteSortLink_return_wit_2 := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (v_5: Z) (v_6: Z) (PreH1 : (v_6 = 0)) (PreH2 : (v_5 = 0)) (PreH3 : (t > g)) (PreH4 : (t <> (unsigned_last_nbits ((-1)) (64)))) ,
  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_6)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v_5)
  **  (storesortedLinkNode storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) ((unsigned_last_nbits ((-1)) (64)))) )
  **  (store_sorted_dll storeA x (app (l1) (l2)) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  EX (v_2: Z)  (v: Z) ,
  “ (t <> (unsigned_last_nbits ((-1)) (64))) ” 
  &&  “ (t > g) ” 
  &&  “ (v = 0) ” 
  &&  “ (v_2 = 0) ”
  &&  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v_2)
  **  (storesortedLinkNode storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) ((unsigned_last_nbits ((-1)) (64)))) )
  **  (store_sorted_dll storeA x (app (l1) (l2)) )
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
.

Definition OsDeleteSortLink_return_wit_3 := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (h: Z) (pt: Z) (py: Z) (z: Z) (PreH1 : (t = (unsigned_last_nbits ((-1)) (64)))) ,
  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  (dllseg (storesortedLinkNode (storeA)) h x &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") py (sortedLinkNodeMappingList (l1)) )
  **  ((&((x)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((x)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) z &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") x pt (sortedLinkNodeMappingList (l2)) )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> z)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> py)
  **  (storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  “ (t = (unsigned_last_nbits ((-1)) (64))) ”
  &&  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
.

Definition OsDeleteSortLink_partial_solve_wit_1 := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) ,
  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
  **  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )
|--
  EX (z: Z)  (py: Z)  (pt: Z)  (h: Z) ,
  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  (dllseg (storesortedLinkNode (storeA)) h x &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") py (sortedLinkNodeMappingList (l1)) )
  **  ((&((x)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((x)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) z &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") x pt (sortedLinkNodeMappingList (l2)) )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> z)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> py)
  **  (storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
.

Definition OsDeleteSortLink_partial_solve_wit_2 := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (h: Z) (pt: Z) (py: Z) (z: Z) (PreH1 : (t <= g)) (PreH2 : (t <> (unsigned_last_nbits ((-1)) (64)))) ,
  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  (dllseg (storesortedLinkNode (storeA)) h x &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") py (sortedLinkNodeMappingList (l1)) )
  **  ((&((x)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((x)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) z &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") x pt (sortedLinkNodeMappingList (l2)) )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> z)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> py)
  **  (storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> o)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  “ (t <= g) ” 
  &&  “ (t <> (unsigned_last_nbits ((-1)) (64))) ”
  &&  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> o)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
.

Definition OsDeleteSortLink_partial_solve_wit_3 := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (h: Z) (pt: Z) (py: Z) (z: Z) (PreH1 : (t > g)) (PreH2 : (t <> (unsigned_last_nbits ((-1)) (64)))) ,
  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  (dllseg (storesortedLinkNode (storeA)) h x &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") py (sortedLinkNodeMappingList (l1)) )
  **  ((&((x)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((x)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) z &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") x pt (sortedLinkNodeMappingList (l2)) )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> z)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> py)
  **  (storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  “ (t > g) ” 
  &&  “ (t <> (unsigned_last_nbits ((-1)) (64))) ”
  &&  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
.

Module Type VC_Correct.

Include los_sortlink_shape_Strategy_Correct.

Axiom proof_of_OsDeleteSortLink_safety_wit_1 : OsDeleteSortLink_safety_wit_1.
Axiom proof_of_OsDeleteSortLink_safety_wit_2 : OsDeleteSortLink_safety_wit_2.
Axiom proof_of_OsDeleteSortLink_return_wit_1 : OsDeleteSortLink_return_wit_1.
Axiom proof_of_OsDeleteSortLink_return_wit_2 : OsDeleteSortLink_return_wit_2.
Axiom proof_of_OsDeleteSortLink_return_wit_3 : OsDeleteSortLink_return_wit_3.
Axiom proof_of_OsDeleteSortLink_partial_solve_wit_1 : OsDeleteSortLink_partial_solve_wit_1.
Axiom proof_of_OsDeleteSortLink_partial_solve_wit_2 : OsDeleteSortLink_partial_solve_wit_2.
Axiom proof_of_OsDeleteSortLink_partial_solve_wit_3 : OsDeleteSortLink_partial_solve_wit_3.

End VC_Correct.
