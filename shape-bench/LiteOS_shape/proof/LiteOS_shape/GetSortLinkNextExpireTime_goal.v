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

(*----- Function GetSortLinkNextExpireTime -----*)

Definition GetSortLinkNextExpireTime_safety_wit_1 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 1)) (PreH3 : ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX)) (PreH4 : (startTime_pre >= 0)) (PreH5 : (startTime_pre <= ULLONG_MAX)) (PreH6 : (tickPrecision_pre >= 0)) (PreH7 : (tickPrecision_pre <= ULLONG_MAX)) (PreH8 : (retval = 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "sortHead" ) )) # Ptr  |-> sortHead_pre)
  **  ((( &( "head" ) )) # Ptr  |-> &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "tickPrecision" ) )) # UInt64  |-> tickPrecision_pre)
  **  ((( &( "startTime" ) )) # UInt64  |-> startTime_pre)
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  “ False ”
.

Definition GetSortLinkNextExpireTime_safety_wit_2 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 0)) (PreH3 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH4 : ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX)) (PreH5 : (startTime_pre >= 0)) (PreH6 : (startTime_pre <= ULLONG_MAX)) (PreH7 : (tickPrecision_pre >= 0)) (PreH8 : (tickPrecision_pre <= ULLONG_MAX)) (PreH9 : (retval <> 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "sortHead" ) )) # Ptr  |-> sortHead_pre)
  **  ((( &( "head" ) )) # Ptr  |-> &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "tickPrecision" ) )) # UInt64  |-> tickPrecision_pre)
  **  ((( &( "startTime" ) )) # UInt64  |-> startTime_pre)
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  “ False ”
.

Definition GetSortLinkNextExpireTime_entail_wit_1 := 
(
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (h: Z) (pt: Z) (PreH1 : ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX)) (PreH2 : (startTime_pre >= 0)) (PreH3 : (startTime_pre <= ULLONG_MAX)) (PreH4 : (tickPrecision_pre >= 0)) (PreH5 : (tickPrecision_pre <= ULLONG_MAX)) ,
  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (sortedLinkNodeMappingList (l)) )
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  ((( &( "list" ) )) # Ptr  |-> h)
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  “ ((obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))) = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) ” 
  &&  “ ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) ” 
  &&  “ (startTime_pre >= 0) ” 
  &&  “ (startTime_pre <= ULLONG_MAX) ” 
  &&  “ (tickPrecision_pre >= 0) ” 
  &&  “ (tickPrecision_pre <= ULLONG_MAX) ”
  &&  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (sortedLinkNodeMappingList (l)) )
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
) \/
(
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (h: Z) (PreH1 : ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX)) (PreH2 : (startTime_pre >= 0)) (PreH3 : (startTime_pre <= ULLONG_MAX)) (PreH4 : (tickPrecision_pre >= 0)) (PreH5 : (tickPrecision_pre <= ULLONG_MAX)) ,
  TT && emp 
|--
  “ (h = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) ”
  &&  emp
).

Definition GetSortLinkNextExpireTime_entail_wit_1_split_goal_1 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (h: Z) (PreH1 : ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX)) (PreH2 : (startTime_pre >= 0)) (PreH3 : (startTime_pre <= ULLONG_MAX)) (PreH4 : (tickPrecision_pre >= 0)) (PreH5 : (tickPrecision_pre <= ULLONG_MAX)) ,
  (h = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
.

Definition GetSortLinkNextExpireTime_entail_wit_2_1 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (retval_2: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval_2 = 1)) (PreH3 : ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX)) (PreH4 : (startTime_pre >= 0)) (PreH5 : (startTime_pre <= ULLONG_MAX)) (PreH6 : (tickPrecision_pre >= 0)) (PreH7 : (tickPrecision_pre <= ULLONG_MAX)) (PreH8 : (retval_2 = 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  EX (a: (@DL_Node (@sortedLinkNode A)))  (l1: (@list (@DL_Node (@sortedLinkNode A))))  (retval: Z) ,
  “ ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) ” 
  &&  “ ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) ” 
  &&  “ (startTime_pre >= 0) ” 
  &&  “ (startTime_pre <= ULLONG_MAX) ” 
  &&  “ (tickPrecision_pre >= 0) ” 
  &&  “ (tickPrecision_pre <= ULLONG_MAX) ” 
  &&  “ (retval = 0) ”
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
.

Definition GetSortLinkNextExpireTime_entail_wit_2_2 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 0)) (PreH3 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH4 : ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX)) (PreH5 : (startTime_pre >= 0)) (PreH6 : (startTime_pre <= ULLONG_MAX)) (PreH7 : (tickPrecision_pre >= 0)) (PreH8 : (tickPrecision_pre <= ULLONG_MAX)) (PreH9 : (retval = 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  “ ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) ” 
  &&  “ ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) ” 
  &&  “ (startTime_pre >= 0) ” 
  &&  “ (startTime_pre <= ULLONG_MAX) ” 
  &&  “ (tickPrecision_pre >= 0) ” 
  &&  “ (tickPrecision_pre <= ULLONG_MAX) ” 
  &&  “ (retval = 0) ”
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
.

Definition GetSortLinkNextExpireTime_entail_wit_3_1 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 1)) (PreH3 : ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX)) (PreH4 : (startTime_pre >= 0)) (PreH5 : (startTime_pre <= ULLONG_MAX)) (PreH6 : (tickPrecision_pre >= 0)) (PreH7 : (tickPrecision_pre <= ULLONG_MAX)) (PreH8 : (retval <> 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  “ ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) ” 
  &&  “ (startTime_pre >= 0) ” 
  &&  “ (startTime_pre <= ULLONG_MAX) ” 
  &&  “ (tickPrecision_pre >= 0) ” 
  &&  “ (tickPrecision_pre <= ULLONG_MAX) ” 
  &&  “ (retval <> 0) ”
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
.

Definition GetSortLinkNextExpireTime_entail_wit_3_2 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval_2 = 0)) (PreH3 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH4 : ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX)) (PreH5 : (startTime_pre >= 0)) (PreH6 : (startTime_pre <= ULLONG_MAX)) (PreH7 : (tickPrecision_pre >= 0)) (PreH8 : (tickPrecision_pre <= ULLONG_MAX)) (PreH9 : (retval_2 <> 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  EX (retval: Z) ,
  “ ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) ” 
  &&  “ (startTime_pre >= 0) ” 
  &&  “ (startTime_pre <= ULLONG_MAX) ” 
  &&  “ (tickPrecision_pre >= 0) ” 
  &&  “ (tickPrecision_pre <= ULLONG_MAX) ” 
  &&  “ (retval <> 0) ”
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
.

Definition GetSortLinkNextExpireTime_return_wit_1 := 
(
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) (pt: Z) (z: Z) (PreH1 : ((responseTime ((data (a)))) > (unsigned_last_nbits ((startTime_pre + tickPrecision_pre )) (64)))) (PreH2 : (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (ptr (a)))) (PreH3 : (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH4 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH5 : (retval = 0)) (PreH6 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH7 : ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX)) (PreH8 : (startTime_pre >= 0)) (PreH9 : (startTime_pre <= ULLONG_MAX)) (PreH10 : (tickPrecision_pre >= 0)) (PreH11 : (tickPrecision_pre <= ULLONG_MAX)) (PreH12 : (retval = 0)) ,
  ((&((retval_2)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> (responseTime ((data (a)))))
  **  (storeA (ptr (a)) (sl_data ((data (a)))) )
  **  (dllseg (storesortedLinkNode (storeA)) z (ptr (a)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt l1 )
  **  ((&(((ptr (a)))  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> z)
  **  ((&(((ptr (a)))  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> (ptr (a)))
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  (store_sorted_dll storeA &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
) \/
(
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) (pt: Z) (z: Z) (PreH1 : ((responseTime ((data (a)))) > (unsigned_last_nbits ((startTime_pre + tickPrecision_pre )) (64)))) (PreH2 : (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (ptr (a)))) (PreH3 : (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH4 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH5 : (retval = 0)) (PreH6 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH7 : ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX)) (PreH8 : (startTime_pre >= 0)) (PreH9 : (startTime_pre <= ULLONG_MAX)) (PreH10 : (tickPrecision_pre >= 0)) (PreH11 : (tickPrecision_pre <= ULLONG_MAX)) (PreH12 : (retval = 0)) ,
  ((&((retval_2)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> (responseTime ((data (a)))))
  **  (storeA (ptr (a)) (sl_data ((data (a)))) )
  **  (dllseg (storesortedLinkNode (storeA)) z (ptr (a)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt l1 )
  **  ((&(((ptr (a)))  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> z)
  **  ((&(((ptr (a)))  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
|--
  (dllseg (storesortedLinkNode (storeA)) (ptr (a)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (sortedLinkNodeMappingList (l)) )
).

Definition GetSortLinkNextExpireTime_return_wit_1_split_goal_spatial := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) (pt: Z) (z: Z) (PreH1 : ((responseTime ((data (a)))) > (unsigned_last_nbits ((startTime_pre + tickPrecision_pre )) (64)))) (PreH2 : (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (ptr (a)))) (PreH3 : (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH4 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH5 : (retval = 0)) (PreH6 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH7 : ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX)) (PreH8 : (startTime_pre >= 0)) (PreH9 : (startTime_pre <= ULLONG_MAX)) (PreH10 : (tickPrecision_pre >= 0)) (PreH11 : (tickPrecision_pre <= ULLONG_MAX)) (PreH12 : (retval = 0)) ,
  ((&((retval_2)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> (responseTime ((data (a)))))
  **  (storeA (ptr (a)) (sl_data ((data (a)))) )
  **  (dllseg (storesortedLinkNode (storeA)) z (ptr (a)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt l1 )
  **  ((&(((ptr (a)))  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> z)
  **  ((&(((ptr (a)))  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
|--
  (dllseg (storesortedLinkNode (storeA)) (ptr (a)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (sortedLinkNodeMappingList (l)) )
.

Definition GetSortLinkNextExpireTime_return_wit_2 := 
(
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) (pt: Z) (z: Z) (PreH1 : ((responseTime ((data (a)))) <= (unsigned_last_nbits ((startTime_pre + tickPrecision_pre )) (64)))) (PreH2 : (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (ptr (a)))) (PreH3 : (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH4 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH5 : (retval = 0)) (PreH6 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH7 : ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX)) (PreH8 : (startTime_pre >= 0)) (PreH9 : (startTime_pre <= ULLONG_MAX)) (PreH10 : (tickPrecision_pre >= 0)) (PreH11 : (tickPrecision_pre <= ULLONG_MAX)) (PreH12 : (retval = 0)) ,
  ((&((retval_2)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> (responseTime ((data (a)))))
  **  (storeA (ptr (a)) (sl_data ((data (a)))) )
  **  (dllseg (storesortedLinkNode (storeA)) z (ptr (a)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt l1 )
  **  ((&(((ptr (a)))  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> z)
  **  ((&(((ptr (a)))  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> (ptr (a)))
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  (store_sorted_dll storeA &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
) \/
(
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) (pt: Z) (z: Z) (PreH1 : ((responseTime ((data (a)))) <= (unsigned_last_nbits ((startTime_pre + tickPrecision_pre )) (64)))) (PreH2 : (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (ptr (a)))) (PreH3 : (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH4 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH5 : (retval = 0)) (PreH6 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH7 : ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX)) (PreH8 : (startTime_pre >= 0)) (PreH9 : (startTime_pre <= ULLONG_MAX)) (PreH10 : (tickPrecision_pre >= 0)) (PreH11 : (tickPrecision_pre <= ULLONG_MAX)) (PreH12 : (retval = 0)) ,
  ((&((retval_2)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> (responseTime ((data (a)))))
  **  (storeA (ptr (a)) (sl_data ((data (a)))) )
  **  (dllseg (storesortedLinkNode (storeA)) z (ptr (a)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt l1 )
  **  ((&(((ptr (a)))  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> z)
  **  ((&(((ptr (a)))  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
|--
  (dllseg (storesortedLinkNode (storeA)) (ptr (a)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (sortedLinkNodeMappingList (l)) )
).

Definition GetSortLinkNextExpireTime_return_wit_2_split_goal_spatial := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) (pt: Z) (z: Z) (PreH1 : ((responseTime ((data (a)))) <= (unsigned_last_nbits ((startTime_pre + tickPrecision_pre )) (64)))) (PreH2 : (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (ptr (a)))) (PreH3 : (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH4 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH5 : (retval = 0)) (PreH6 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH7 : ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX)) (PreH8 : (startTime_pre >= 0)) (PreH9 : (startTime_pre <= ULLONG_MAX)) (PreH10 : (tickPrecision_pre >= 0)) (PreH11 : (tickPrecision_pre <= ULLONG_MAX)) (PreH12 : (retval = 0)) ,
  ((&((retval_2)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> (responseTime ((data (a)))))
  **  (storeA (ptr (a)) (sl_data ((data (a)))) )
  **  (dllseg (storesortedLinkNode (storeA)) z (ptr (a)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt l1 )
  **  ((&(((ptr (a)))  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> z)
  **  ((&(((ptr (a)))  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
|--
  (dllseg (storesortedLinkNode (storeA)) (ptr (a)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (sortedLinkNodeMappingList (l)) )
.

Definition GetSortLinkNextExpireTime_return_wit_3 := 
(
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 1)) (PreH3 : ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX)) (PreH4 : (startTime_pre >= 0)) (PreH5 : (startTime_pre <= ULLONG_MAX)) (PreH6 : (tickPrecision_pre >= 0)) (PreH7 : (tickPrecision_pre <= ULLONG_MAX)) (PreH8 : (retval <> 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  (store_sorted_dll storeA &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
) \/
(
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 1)) (PreH3 : ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX)) (PreH4 : (startTime_pre >= 0)) (PreH5 : (startTime_pre <= ULLONG_MAX)) (PreH6 : (tickPrecision_pre >= 0)) (PreH7 : (tickPrecision_pre <= ULLONG_MAX)) (PreH8 : (retval <> 0)) ,
  TT && emp 
|--
  “ ((map (sortedLinkNodeMapping) (l)) = (sortedLinkNodeMappingList (l))) ”
  &&  emp
).

Definition GetSortLinkNextExpireTime_return_wit_3_split_goal_1 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 1)) (PreH3 : ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX)) (PreH4 : (startTime_pre >= 0)) (PreH5 : (startTime_pre <= ULLONG_MAX)) (PreH6 : (tickPrecision_pre >= 0)) (PreH7 : (tickPrecision_pre <= ULLONG_MAX)) (PreH8 : (retval <> 0)) ,
  ((map (sortedLinkNodeMapping) (l)) = (sortedLinkNodeMappingList (l)))
.

Definition GetSortLinkNextExpireTime_partial_solve_wit_1 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (PreH1 : ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX)) (PreH2 : (startTime_pre >= 0)) (PreH3 : (startTime_pre <= ULLONG_MAX)) (PreH4 : (tickPrecision_pre >= 0)) (PreH5 : (tickPrecision_pre <= ULLONG_MAX)) ,
  (store_sorted_dll storeA &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  EX (pt: Z)  (h: Z) ,
  “ ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) ” 
  &&  “ (startTime_pre >= 0) ” 
  &&  “ (startTime_pre <= ULLONG_MAX) ” 
  &&  “ (tickPrecision_pre >= 0) ” 
  &&  “ (tickPrecision_pre <= ULLONG_MAX) ”
  &&  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (sortedLinkNodeMappingList (l)) )
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
.

Definition GetSortLinkNextExpireTime_partial_solve_wit_2_pure := 
(
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (h: Z) (pt: Z) (PreH1 : ((obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))) = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH2 : ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX)) (PreH3 : (startTime_pre >= 0)) (PreH4 : (startTime_pre <= ULLONG_MAX)) (PreH5 : (tickPrecision_pre >= 0)) (PreH6 : (tickPrecision_pre <= ULLONG_MAX)) ,
  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "sortHead" ) )) # Ptr  |-> sortHead_pre)
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (sortedLinkNodeMappingList (l)) )
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  ((( &( "head" ) )) # Ptr  |-> &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "tickPrecision" ) )) # UInt64  |-> tickPrecision_pre)
  **  ((( &( "startTime" ) )) # UInt64  |-> startTime_pre)
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  “ ((sortedLinkNodeMappingList (l)) = (map (sortedLinkNodeMapping) (l))) ”
) \/
(
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (h: Z) (pt: Z) (PreH1 : ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX)) (PreH2 : (startTime_pre >= 0)) (PreH3 : (startTime_pre <= ULLONG_MAX)) (PreH4 : (tickPrecision_pre >= 0)) (PreH5 : (tickPrecision_pre <= ULLONG_MAX)) ,
  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "sortHead" ) )) # Ptr  |-> sortHead_pre)
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (sortedLinkNodeMappingList (l)) )
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  ((( &( "head" ) )) # Ptr  |-> &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "tickPrecision" ) )) # UInt64  |-> tickPrecision_pre)
  **  ((( &( "startTime" ) )) # UInt64  |-> startTime_pre)
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  “ ((sortedLinkNodeMappingList (l)) = (map (sortedLinkNodeMapping) (l))) ”
).

Definition GetSortLinkNextExpireTime_partial_solve_wit_2_pure_split_goal_1 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (h: Z) (pt: Z) (PreH1 : ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX)) (PreH2 : (startTime_pre >= 0)) (PreH3 : (startTime_pre <= ULLONG_MAX)) (PreH4 : (tickPrecision_pre >= 0)) (PreH5 : (tickPrecision_pre <= ULLONG_MAX)) ,
  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "sortHead" ) )) # Ptr  |-> sortHead_pre)
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (sortedLinkNodeMappingList (l)) )
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  ((( &( "head" ) )) # Ptr  |-> &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "tickPrecision" ) )) # UInt64  |-> tickPrecision_pre)
  **  ((( &( "startTime" ) )) # UInt64  |-> startTime_pre)
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  “ ((sortedLinkNodeMappingList (l)) = (map (sortedLinkNodeMapping) (l))) ”
.

Definition GetSortLinkNextExpireTime_partial_solve_wit_2_aux := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (h: Z) (pt: Z) (PreH1 : ((obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))) = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH2 : ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX)) (PreH3 : (startTime_pre >= 0)) (PreH4 : (startTime_pre <= ULLONG_MAX)) (PreH5 : (tickPrecision_pre >= 0)) (PreH6 : (tickPrecision_pre <= ULLONG_MAX)) ,
  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (sortedLinkNodeMappingList (l)) )
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  “ ((sortedLinkNodeMappingList (l)) = (map (sortedLinkNodeMapping) (l))) ” 
  &&  “ ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) ” 
  &&  “ (startTime_pre >= 0) ” 
  &&  “ (startTime_pre <= ULLONG_MAX) ” 
  &&  “ (tickPrecision_pre >= 0) ” 
  &&  “ (tickPrecision_pre <= ULLONG_MAX) ”
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
.

Definition GetSortLinkNextExpireTime_partial_solve_wit_2 := GetSortLinkNextExpireTime_partial_solve_wit_2_pure -> GetSortLinkNextExpireTime_partial_solve_wit_2_aux.

Definition GetSortLinkNextExpireTime_partial_solve_wit_3 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 0)) (PreH3 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH4 : ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX)) (PreH5 : (startTime_pre >= 0)) (PreH6 : (startTime_pre <= ULLONG_MAX)) (PreH7 : (tickPrecision_pre >= 0)) (PreH8 : (tickPrecision_pre <= ULLONG_MAX)) (PreH9 : (retval = 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  “ ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) ” 
  &&  “ ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) ” 
  &&  “ (startTime_pre >= 0) ” 
  &&  “ (startTime_pre <= ULLONG_MAX) ” 
  &&  “ (tickPrecision_pre >= 0) ” 
  &&  “ (tickPrecision_pre <= ULLONG_MAX) ” 
  &&  “ (retval = 0) ”
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
.

Definition GetSortLinkNextExpireTime_partial_solve_wit_4 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) (PreH1 : (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH2 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH3 : (retval = 0)) (PreH4 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH5 : ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX)) (PreH6 : (startTime_pre >= 0)) (PreH7 : (startTime_pre <= ULLONG_MAX)) (PreH8 : (tickPrecision_pre >= 0)) (PreH9 : (tickPrecision_pre <= ULLONG_MAX)) (PreH10 : (retval = 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  EX (z: Z)  (pt: Z) ,
  “ (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (ptr (a))) ” 
  &&  “ (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) ” 
  &&  “ ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) ” 
  &&  “ ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) ” 
  &&  “ (startTime_pre >= 0) ” 
  &&  “ (startTime_pre <= ULLONG_MAX) ” 
  &&  “ (tickPrecision_pre >= 0) ” 
  &&  “ (tickPrecision_pre <= ULLONG_MAX) ” 
  &&  “ (retval = 0) ”
  &&  ((&((retval_2)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> (responseTime ((data (a)))))
  **  (storeA (ptr (a)) (sl_data ((data (a)))) )
  **  (dllseg (storesortedLinkNode (storeA)) z (ptr (a)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt l1 )
  **  ((&(((ptr (a)))  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> z)
  **  ((&(((ptr (a)))  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> (ptr (a)))
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
.

Definition LOS_ListEmpty_derive_getfirstSpec_by_highSpec := 
forall (A: Type) ,
forall (node_pre: Z) (l_getfirstSpec: (@list (@DL_Node A))) (storeA_getfirstSpec: (Z -> (A -> Assertion))) ,
  (store_dll storeA_getfirstSpec node_pre l_getfirstSpec )
|--
EX (A: Type) ,
EX (storeA_highSpec: (Z -> (A -> Assertion))) (l_highSpec: (@list (@DL_Node A))) ,
  ((store_dll storeA_highSpec node_pre l_highSpec ))
  **
  (((EX retval_2,
  “ (l_highSpec <> nil) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_dll storeA_highSpec node_pre l_highSpec ))
  ||
  (EX retval_2,
  “ (l_highSpec = nil) ” 
  &&  “ (retval_2 = 1) ”
  &&  (store_dll storeA_highSpec node_pre l_highSpec )))
  -*
  ((EX retval,
  “ (l_getfirstSpec = nil) ” 
  &&  “ (retval = 1) ”
  &&  (store_dll storeA_getfirstSpec node_pre l_getfirstSpec ))
  ||
  (EX a l1 retval,
  “ (l_getfirstSpec <> nil) ” 
  &&  “ (retval = 0) ” 
  &&  “ (l_getfirstSpec = (cons (a) (l1))) ”
  &&  (store_dll storeA_getfirstSpec node_pre (cons (a) (l1)) ))))
.

Module Type VC_Correct.

Include los_sortlink_shape_Strategy_Correct.

Axiom proof_of_GetSortLinkNextExpireTime_safety_wit_1 : GetSortLinkNextExpireTime_safety_wit_1.
Axiom proof_of_GetSortLinkNextExpireTime_safety_wit_2 : GetSortLinkNextExpireTime_safety_wit_2.
Axiom proof_of_GetSortLinkNextExpireTime_entail_wit_1 : GetSortLinkNextExpireTime_entail_wit_1.
Axiom proof_of_GetSortLinkNextExpireTime_entail_wit_2_1 : GetSortLinkNextExpireTime_entail_wit_2_1.
Axiom proof_of_GetSortLinkNextExpireTime_entail_wit_2_2 : GetSortLinkNextExpireTime_entail_wit_2_2.
Axiom proof_of_GetSortLinkNextExpireTime_entail_wit_3_1 : GetSortLinkNextExpireTime_entail_wit_3_1.
Axiom proof_of_GetSortLinkNextExpireTime_entail_wit_3_2 : GetSortLinkNextExpireTime_entail_wit_3_2.
Axiom proof_of_GetSortLinkNextExpireTime_return_wit_1 : GetSortLinkNextExpireTime_return_wit_1.
Axiom proof_of_GetSortLinkNextExpireTime_return_wit_2 : GetSortLinkNextExpireTime_return_wit_2.
Axiom proof_of_GetSortLinkNextExpireTime_return_wit_3 : GetSortLinkNextExpireTime_return_wit_3.
Axiom proof_of_GetSortLinkNextExpireTime_partial_solve_wit_1 : GetSortLinkNextExpireTime_partial_solve_wit_1.
Axiom proof_of_GetSortLinkNextExpireTime_partial_solve_wit_2_pure : GetSortLinkNextExpireTime_partial_solve_wit_2_pure.
Axiom proof_of_GetSortLinkNextExpireTime_partial_solve_wit_2 : GetSortLinkNextExpireTime_partial_solve_wit_2.
Axiom proof_of_GetSortLinkNextExpireTime_partial_solve_wit_3 : GetSortLinkNextExpireTime_partial_solve_wit_3.
Axiom proof_of_GetSortLinkNextExpireTime_partial_solve_wit_4 : GetSortLinkNextExpireTime_partial_solve_wit_4.
Axiom proof_of_LOS_ListEmpty_derive_getfirstSpec_by_highSpec : LOS_ListEmpty_derive_getfirstSpec_by_highSpec.

End VC_Correct.
