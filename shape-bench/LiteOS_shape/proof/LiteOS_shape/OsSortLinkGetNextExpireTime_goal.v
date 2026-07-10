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

(*----- Function OsSortLinkGetNextExpireTime -----*)

Definition OsSortLinkGetNextExpireTime_safety_wit_1 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 1)) (PreH3 : (SysTick <> 0)) (PreH4 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH5 : (retval = 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "sortLinkHead" ) )) # Ptr  |-> sortLinkHead_pre)
  **  ((( &( "head" ) )) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ False ”
.

Definition OsSortLinkGetNextExpireTime_safety_wit_2 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 0)) (PreH3 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH4 : (SysTick <> 0)) (PreH5 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH6 : (retval <> 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "sortLinkHead" ) )) # Ptr  |-> sortLinkHead_pre)
  **  ((( &( "head" ) )) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ False ”
.

Definition OsSortLinkGetNextExpireTime_safety_wit_3 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 1)) (PreH3 : (SysTick <> 0)) (PreH4 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH5 : (retval <> 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "sortLinkHead" ) )) # Ptr  |-> sortLinkHead_pre)
  **  ((( &( "head" ) )) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OsSortLinkGetNextExpireTime_entail_wit_1 := 
(
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (h: Z) (pt: Z) (PreH1 : (SysTick <> 0)) (PreH2 : (( &( "g_archTickTimer" ) ) <> 0)) ,
  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (sortedLinkNodeMappingList (l)) )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  ((( &( "list" ) )) # Ptr  |-> h)
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ ((obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))) = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) ” 
  &&  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (sortedLinkNodeMappingList (l)) )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
) \/
(
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (SysTick: Z) (h: Z) (PreH1 : (SysTick <> 0)) (PreH2 : (( &( "g_archTickTimer" ) ) <> 0)) ,
  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) ”
  &&  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
).

Definition OsSortLinkGetNextExpireTime_entail_wit_1_split_goal_1 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (SysTick: Z) (h: Z) (PreH1 : (SysTick <> 0)) (PreH2 : (( &( "g_archTickTimer" ) ) <> 0)) ,
  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) ”
.

Definition OsSortLinkGetNextExpireTime_entail_wit_1_split_goal_spatial := 
forall (att: archTickTimer) (ts: tickState) (SysTick: Z) (PreH1 : (SysTick <> 0)) (PreH2 : (( &( "g_archTickTimer" ) ) <> 0)) ,
  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_entail_wit_2_1 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (retval_2: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval_2 = 1)) (PreH3 : (SysTick <> 0)) (PreH4 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH5 : (retval_2 = 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  EX (a: (@DL_Node (@sortedLinkNode A)))  (l1: (@list (@DL_Node (@sortedLinkNode A))))  (retval: Z) ,
  “ ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) ” 
  &&  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_entail_wit_2_2 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 0)) (PreH3 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH4 : (SysTick <> 0)) (PreH5 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH6 : (retval = 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) ” 
  &&  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_entail_wit_3_1 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 1)) (PreH3 : (SysTick <> 0)) (PreH4 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH5 : (retval <> 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ (retval = 1) ” 
  &&  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ” 
  &&  “ (retval <> 0) ”
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_entail_wit_3_2 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval_2 = 0)) (PreH3 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH4 : (SysTick <> 0)) (PreH5 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH6 : (retval_2 <> 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  EX (retval: Z) ,
  “ ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ (retval = 1) ” 
  &&  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ” 
  &&  “ (retval <> 0) ”
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_return_wit_1 := 
(
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick_2: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) (SysTick_3: Z) (retval_3: Z) (xn: Z) (x_lSpec_pstNext: Z) (PreH1 : (x_lSpec_pstNext = &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH2 : (SysTick_3 <> 0)) (PreH3 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH4 : (retval_3 = (tick_getcycle_ret (ts)))) (PreH5 : (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH6 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH7 : (retval = 0)) (PreH8 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH9 : (SysTick_2 <> 0)) (PreH10 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH11 : (retval = 0)) ,
  (dllseg_shift_rev (storesortedLinkNode (storeA)) &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> x_lSpec_pstNext)
  **  ((&((xn)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_3)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_3 (timebase_turnover (ts)) att )
|--
  EX (ts_post: tickState)  (SysTick: Z) ,
  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts_post att )
) \/
(
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick_2: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) (SysTick_3: Z) (retval_3: Z) (xn: Z) (x_lSpec_pstNext: Z) (PreH1 : (x_lSpec_pstNext = &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH2 : (SysTick_3 <> 0)) (PreH3 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH4 : (retval_3 = (tick_getcycle_ret (ts)))) (PreH5 : (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH6 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH7 : (retval = 0)) (PreH8 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH9 : (SysTick_2 <> 0)) (PreH10 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH11 : (retval = 0)) ,
  (dllseg_shift_rev (storesortedLinkNode (storeA)) &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((&((xn)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_3 (timebase_turnover (ts)) att )
|--
  EX (pt: Z)  (ts_post: tickState) ,
  “ (SysTick_3 <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  (dllseg (storesortedLinkNode (storeA)) x_lSpec_pstNext &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (sortedLinkNodeMappingList (l)) )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_3 ts_post att )
).

Definition OsSortLinkGetNextExpireTime_return_wit_2 := 
(
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick_2: Z) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 1)) (PreH3 : (SysTick_2 <> 0)) (PreH4 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH5 : (retval <> 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_2)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_2 ts att )
|--
  EX (ts_post: tickState)  (SysTick: Z) ,
  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts_post att )
) \/
(
forall (A: Type) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (SysTick_2: Z) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 1)) (PreH3 : (SysTick_2 <> 0)) (PreH4 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH5 : (retval <> 0)) ,
  (storeTick ( &( "g_archTickTimer" ) ) SysTick_2 ts att )
|--
  EX (ts_post: tickState) ,
  “ ((map (sortedLinkNodeMapping) (l)) = (sortedLinkNodeMappingList (l))) ” 
  &&  “ (SysTick_2 <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  (storeTick ( &( "g_archTickTimer" ) ) SysTick_2 ts_post att )
).

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_1 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (PreH1 : (SysTick <> 0)) (PreH2 : (( &( "g_archTickTimer" ) ) <> 0)) ,
  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  EX (pt: Z)  (h: Z) ,
  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (sortedLinkNodeMappingList (l)) )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_2_pure := 
(
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (h: Z) (pt: Z) (PreH1 : ((obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))) = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH2 : (SysTick <> 0)) (PreH3 : (( &( "g_archTickTimer" ) ) <> 0)) ,
  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "sortLinkHead" ) )) # Ptr  |-> sortLinkHead_pre)
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (sortedLinkNodeMappingList (l)) )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  ((( &( "head" ) )) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ ((sortedLinkNodeMappingList (l)) = (map (sortedLinkNodeMapping) (l))) ”
) \/
(
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (h: Z) (pt: Z) (PreH1 : (SysTick <> 0)) (PreH2 : (( &( "g_archTickTimer" ) ) <> 0)) ,
  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "sortLinkHead" ) )) # Ptr  |-> sortLinkHead_pre)
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (sortedLinkNodeMappingList (l)) )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  ((( &( "head" ) )) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ ((sortedLinkNodeMappingList (l)) = (map (sortedLinkNodeMapping) (l))) ”
).

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_2_pure_split_goal_1 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (h: Z) (pt: Z) (PreH1 : (SysTick <> 0)) (PreH2 : (( &( "g_archTickTimer" ) ) <> 0)) ,
  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "sortLinkHead" ) )) # Ptr  |-> sortLinkHead_pre)
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (sortedLinkNodeMappingList (l)) )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  ((( &( "head" ) )) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ ((sortedLinkNodeMappingList (l)) = (map (sortedLinkNodeMapping) (l))) ”
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_2_aux := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (h: Z) (pt: Z) (PreH1 : ((obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))) = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH2 : (SysTick <> 0)) (PreH3 : (( &( "g_archTickTimer" ) ) <> 0)) ,
  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (sortedLinkNodeMappingList (l)) )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ ((sortedLinkNodeMappingList (l)) = (map (sortedLinkNodeMapping) (l))) ” 
  &&  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_2 := OsSortLinkGetNextExpireTime_partial_solve_wit_2_pure -> OsSortLinkGetNextExpireTime_partial_solve_wit_2_aux.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_3 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 0)) (PreH3 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH4 : (SysTick <> 0)) (PreH5 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH6 : (retval = 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) ” 
  &&  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_4_pure := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) (PreH1 : (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH2 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH3 : (retval = 0)) (PreH4 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH5 : (SysTick <> 0)) (PreH6 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH7 : (retval = 0)) ,
  ((( &( "listSorted" ) )) # Ptr  |-> retval_2)
  **  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "sortLinkHead" ) )) # Ptr  |-> sortLinkHead_pre)
  **  ((( &( "head" ) )) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_4_aux := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) (PreH1 : (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH2 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH3 : (retval = 0)) (PreH4 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH5 : (SysTick <> 0)) (PreH6 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH7 : (retval = 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ” 
  &&  “ (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) ” 
  &&  “ ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) ” 
  &&  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ” 
  &&  “ (retval = 0) ”
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
  **  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_4 := OsSortLinkGetNextExpireTime_partial_solve_wit_4_pure -> OsSortLinkGetNextExpireTime_partial_solve_wit_4_aux.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_5_pure := 
(
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) (retval: Z) (SysTick_2: Z) (retval_3: Z) (xn: Z) (PreH1 : (SysTick_2 <> 0)) (PreH2 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH3 : (retval_3 = (tick_getcycle_ret (ts)))) (PreH4 : (&((retval)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH5 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH6 : (retval_2 = 0)) (PreH7 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH8 : (SysTick <> 0)) (PreH9 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH10 : (retval_2 = 0)) ,
  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_2)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_2 (timebase_turnover (ts)) att )
  **  ((( &( "listSorted" ) )) # Ptr  |-> retval)
  **  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "sortLinkHead" ) )) # Ptr  |-> sortLinkHead_pre)
  **  ((( &( "head" ) )) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
|--
  “ (&((retval)  # "SortLinkList" ->ₛ "sortLinkNode") = &((retval)  # "SortLinkList" ->ₛ "sortLinkNode")) ” 
  &&  “ ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ (xn = &((retval)  # "SortLinkList" ->ₛ "sortLinkNode")) ” 
  &&  “ (xn = &((retval)  # "SortLinkList" ->ₛ "sortLinkNode")) ”
) \/
(
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) (retval: Z) (SysTick_2: Z) (retval_3: Z) (xn: Z) (PreH1 : (SysTick_2 <> 0)) (PreH2 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH3 : (retval_3 = (tick_getcycle_ret (ts)))) (PreH4 : (&((retval)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH5 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH6 : (retval_2 = 0)) (PreH7 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH8 : (SysTick <> 0)) (PreH9 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH10 : (retval_2 = 0)) ,
  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_2)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_2 (timebase_turnover (ts)) att )
  **  ((( &( "listSorted" ) )) # Ptr  |-> retval)
  **  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "sortLinkHead" ) )) # Ptr  |-> sortLinkHead_pre)
  **  ((( &( "head" ) )) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
|--
  “ (xn = &((retval)  # "SortLinkList" ->ₛ "sortLinkNode")) ” 
  &&  “ (xn = &((retval)  # "SortLinkList" ->ₛ "sortLinkNode")) ”
).

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_5_pure_split_goal_1 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) (retval: Z) (SysTick_2: Z) (retval_3: Z) (xn: Z) (PreH1 : (SysTick_2 <> 0)) (PreH2 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH3 : (retval_3 = (tick_getcycle_ret (ts)))) (PreH4 : (&((retval)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH5 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH6 : (retval_2 = 0)) (PreH7 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH8 : (SysTick <> 0)) (PreH9 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH10 : (retval_2 = 0)) ,
  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_2)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_2 (timebase_turnover (ts)) att )
  **  ((( &( "listSorted" ) )) # Ptr  |-> retval)
  **  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "sortLinkHead" ) )) # Ptr  |-> sortLinkHead_pre)
  **  ((( &( "head" ) )) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
|--
  “ (xn = &((retval)  # "SortLinkList" ->ₛ "sortLinkNode")) ”
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_5_pure_split_goal_2 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) (retval: Z) (SysTick_2: Z) (retval_3: Z) (xn: Z) (PreH1 : (SysTick_2 <> 0)) (PreH2 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH3 : (retval_3 = (tick_getcycle_ret (ts)))) (PreH4 : (&((retval)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH5 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH6 : (retval_2 = 0)) (PreH7 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH8 : (SysTick <> 0)) (PreH9 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH10 : (retval_2 = 0)) ,
  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_2)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_2 (timebase_turnover (ts)) att )
  **  ((( &( "listSorted" ) )) # Ptr  |-> retval)
  **  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "sortLinkHead" ) )) # Ptr  |-> sortLinkHead_pre)
  **  ((( &( "head" ) )) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
|--
  “ (xn = &((retval)  # "SortLinkList" ->ₛ "sortLinkNode")) ”
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_5_aux := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) (retval: Z) (SysTick_2: Z) (retval_3: Z) (PreH1 : (SysTick_2 <> 0)) (PreH2 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH3 : (retval_3 = (tick_getcycle_ret (ts)))) (PreH4 : (&((retval)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH5 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH6 : (retval_2 = 0)) (PreH7 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH8 : (SysTick <> 0)) (PreH9 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH10 : (retval_2 = 0)) ,
  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_2)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_2 (timebase_turnover (ts)) att )
  **  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
|--
  EX (xn: Z) ,
  “ (&((retval)  # "SortLinkList" ->ₛ "sortLinkNode") = &((retval)  # "SortLinkList" ->ₛ "sortLinkNode")) ” 
  &&  “ ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ (xn = &((retval)  # "SortLinkList" ->ₛ "sortLinkNode")) ” 
  &&  “ (xn = &((retval)  # "SortLinkList" ->ₛ "sortLinkNode")) ” 
  &&  “ (SysTick_2 <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ” 
  &&  “ (retval_3 = (tick_getcycle_ret (ts))) ” 
  &&  “ (&((retval)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) ” 
  &&  “ ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) ” 
  &&  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (dllseg_shift_rev (storesortedLinkNode (storeA)) &((retval)  # "SortLinkList" ->ₛ "sortLinkNode") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> &((retval)  # "SortLinkList" ->ₛ "sortLinkNode"))
  **  ((&((xn)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_2)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_2 (timebase_turnover (ts)) att )
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_5 := OsSortLinkGetNextExpireTime_partial_solve_wit_5_pure -> OsSortLinkGetNextExpireTime_partial_solve_wit_5_aux.

Definition OsSortLinkGetTargetExpireTime_derive_lSpec_by_highSpec := 
forall (A: Type) ,
forall (targetSortList_pre: Z) (l_lSpec: (@list (@DL_Node (@sortedLinkNode A)))) (x_lSpec: Z) (storeA_lSpec: (Z -> (A -> Assertion))) ,
  EX x_lSpec_pstNext,
  “ (x_lSpec_pstNext = &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ” 
  &&  “ (l_lSpec <> nil) ”
  &&  (dllseg_shift_rev (storesortedLinkNode (storeA_lSpec)) &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") x_lSpec l_lSpec )
  **  ((&((x_lSpec)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> x_lSpec_pstNext)
|--
EX (A: Type) ,
EX (storeA_highSpec: (Z -> (A -> Assertion))) (a_highSpec: A) (t_highSpec: Z) ,
  ((storesortedLinkNode storeA_highSpec &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a_highSpec) (t_highSpec)) ))
  **
  (((storesortedLinkNode storeA_highSpec &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a_highSpec) (t_highSpec)) ))
  -*
  (EX x_lSpec_pstNext_2,
  “ (x_lSpec_pstNext_2 = &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ”
  &&  (dllseg_shift_rev (storesortedLinkNode (storeA_lSpec)) &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") x_lSpec l_lSpec )
  **  ((&((x_lSpec)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> x_lSpec_pstNext_2)))
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

Axiom proof_of_OsSortLinkGetNextExpireTime_safety_wit_1 : OsSortLinkGetNextExpireTime_safety_wit_1.
Axiom proof_of_OsSortLinkGetNextExpireTime_safety_wit_2 : OsSortLinkGetNextExpireTime_safety_wit_2.
Axiom proof_of_OsSortLinkGetNextExpireTime_safety_wit_3 : OsSortLinkGetNextExpireTime_safety_wit_3.
Axiom proof_of_OsSortLinkGetNextExpireTime_entail_wit_1 : OsSortLinkGetNextExpireTime_entail_wit_1.
Axiom proof_of_OsSortLinkGetNextExpireTime_entail_wit_2_1 : OsSortLinkGetNextExpireTime_entail_wit_2_1.
Axiom proof_of_OsSortLinkGetNextExpireTime_entail_wit_2_2 : OsSortLinkGetNextExpireTime_entail_wit_2_2.
Axiom proof_of_OsSortLinkGetNextExpireTime_entail_wit_3_1 : OsSortLinkGetNextExpireTime_entail_wit_3_1.
Axiom proof_of_OsSortLinkGetNextExpireTime_entail_wit_3_2 : OsSortLinkGetNextExpireTime_entail_wit_3_2.
Axiom proof_of_OsSortLinkGetNextExpireTime_return_wit_1 : OsSortLinkGetNextExpireTime_return_wit_1.
Axiom proof_of_OsSortLinkGetNextExpireTime_return_wit_2 : OsSortLinkGetNextExpireTime_return_wit_2.
Axiom proof_of_OsSortLinkGetNextExpireTime_partial_solve_wit_1 : OsSortLinkGetNextExpireTime_partial_solve_wit_1.
Axiom proof_of_OsSortLinkGetNextExpireTime_partial_solve_wit_2_pure : OsSortLinkGetNextExpireTime_partial_solve_wit_2_pure.
Axiom proof_of_OsSortLinkGetNextExpireTime_partial_solve_wit_2 : OsSortLinkGetNextExpireTime_partial_solve_wit_2.
Axiom proof_of_OsSortLinkGetNextExpireTime_partial_solve_wit_3 : OsSortLinkGetNextExpireTime_partial_solve_wit_3.
Axiom proof_of_OsSortLinkGetNextExpireTime_partial_solve_wit_4_pure : OsSortLinkGetNextExpireTime_partial_solve_wit_4_pure.
Axiom proof_of_OsSortLinkGetNextExpireTime_partial_solve_wit_4 : OsSortLinkGetNextExpireTime_partial_solve_wit_4.
Axiom proof_of_OsSortLinkGetNextExpireTime_partial_solve_wit_5_pure : OsSortLinkGetNextExpireTime_partial_solve_wit_5_pure.
Axiom proof_of_OsSortLinkGetNextExpireTime_partial_solve_wit_5 : OsSortLinkGetNextExpireTime_partial_solve_wit_5.
Axiom proof_of_OsSortLinkGetTargetExpireTime_derive_lSpec_by_highSpec : OsSortLinkGetTargetExpireTime_derive_lSpec_by_highSpec.
Axiom proof_of_LOS_ListEmpty_derive_getfirstSpec_by_highSpec : LOS_ListEmpty_derive_getfirstSpec_by_highSpec.

End VC_Correct.
