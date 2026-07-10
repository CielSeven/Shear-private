
typedef unsigned short UINT16;
typedef unsigned int UINT32;
typedef unsigned long long UINT64;
typedef int INT32;//not support signed int
typedef char CHAR;
typedef unsigned int UINTPTR;
/*@ Extern Coq TaskID := Z  */
/*@ Extern Coq TaskID := Z */
/*@ Extern Coq SwtmrID := Z */
/*@ Extern Coq addr := Z */
//@ Extern Coq (StableGlobVars :: * )
/*@ Extern Coq Record StableGlobVars {
  g_taskCBArray: addr;
  g_swtmrCBArray: addr;
  g_allSem: addr;
  g_allQueue: addr;
  g_allMux: addr;
  g_priQueueList : addr;
}
*/
/*@ Extern Coq Record tickState {
  ts_period : Z;
  ts_val : Z;
  ts_ctrl : Z;
  ts_startTime : Z;
  ts_timeBase : Z;
  ts_oldTimeBase : Z;
  ts_timeBaseUpdate : Z;
} */
/*@ Extern Coq Record archTickTimer {
  freqNum : Z;
  irqNum : Z;
  periodMax : Z;
} */
typedef struct LOS_DL_LIST {
    struct LOS_DL_LIST *pstPrev; /**< Current node's pointer to the previous node */
    struct LOS_DL_LIST *pstNext; /**< Current node's pointer to the next node */
} LOS_DL_LIST;
/*@ Import Coq Require Import SimpleC.EE.Applications_human.LiteOS.lib.glob_vars_and_defs */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.LiteOS.lib.Los_Verify_State_def*/
/*@ Import Coq Require Import SimpleC.EE.Applications_human.LiteOS.lib.dll*/
/*@ Extern Coq (sortedLinkNode :: * => *) */
/*@ Extern Coq (DL_Node :: * => *) */
/*@ Extern Coq (sl_data: {A} -> sortedLinkNode A -> A)
               (responseTime: {A} -> sortedLinkNode A -> Z)*/
/*@ Extern Coq (data: {A} -> DL_Node A -> A)
               (ptr: {A} -> DL_Node A -> Z)*/
/*@ Extern Coq (storesortedLinkNode: {A} -> (Z -> A -> Assertion) -> Z -> sortedLinkNode A -> Assertion)
               (task_store: StableGlobVars -> Z -> TaskID -> Assertion)
               (storesortedLinkTaskNode: (StableGlobVars -> Z -> TaskID -> Assertion) -> StableGlobVars -> Z -> sortedLinkNode TaskID -> Assertion)
               (store_sorted_dll: {A} -> (Z -> A -> Assertion)  -> Z -> list (DL_Node(sortedLinkNode A)) -> Assertion)
               (store_task_sorted_dll: StableGlobVars -> list (DL_Node(sortedLinkNode TaskID)) -> Assertion)
               (store_swtmr_sorted_dll: StableGlobVars -> list (DL_Node(sortedLinkNode SwtmrID)) -> Assertion)
               (mksortedLinkNode: {A} -> A -> Z -> sortedLinkNode A)
               (getFirstNodeExpireTime: {A} -> list (DL_Node(sortedLinkNode A)) -> Z -> Z -> Z) 
               (increasingSortedNode: {A} -> list (DL_Node(sortedLinkNode A)) -> Prop)
               (getNodeExpireTime: {A} -> DL_Node(sortedLinkNode A) -> Z -> Z -> Z)
               (getminExpireTime: {A} -> list (DL_Node(sortedLinkNode A)) -> list (DL_Node(sortedLinkNode A)) -> Z -> Z -> Z)
               (updateNodeTime: {A} -> list (DL_Node(sortedLinkNode A)) -> Z -> Z -> list (DL_Node(sortedLinkNode A)))
               (getFirstNodeResponseTime: {A} -> list (DL_Node(sortedLinkNode A)) -> Z)
               (sortedLinkNodeMapping : {A} -> (DL_Node(sortedLinkNode A)) -> (DL_Node(sortedLinkNode A)))
               (getFirstNodeData: {A} -> list (DL_Node(sortedLinkNode A)) -> A) 
               (storeTick: Z -> Z -> tickState -> archTickTimer -> Assertion)
               (timebase_turnover: tickState -> tickState)
               (tick_getcycle_ret: tickState -> Z)
               (ULLONG_MAX : Z)
               (obtian_first_pointer: {A} -> Z -> list (DL_Node(sortedLinkNode A)) -> Z)
*/
/*@ Extern Coq (DL_Node :: * => *) */
/*@ Extern Coq (data: {A} -> DL_Node A -> A )

               (ptr: {A} -> DL_Node A -> Z )*/
/*@ Extern Coq (Build_DL_Node: {A} -> A -> Z -> DL_Node A)

               (store_dll: {A} -> (Z -> A -> Assertion) -> Z -> (list (DL_Node A)) -> Assertion)

               (dllseg: {A} -> (Z -> A -> Assertion) -> Z -> Z -> Z -> Z -> (list (DL_Node A)) -> Assertion)

               (dllseg_shift: {A} -> (Z -> A -> Assertion) -> Z -> Z -> (list (DL_Node A)) -> Assertion)
               (dllseg_shift_rev: {A} -> (Z -> A -> Assertion) -> Z -> Z-> list (DL_Node A) -> Assertion)
               (store_map: {A} {B} -> (A -> B -> Assertion) -> (A -> option B) -> Assertion)

               (store_pend_list_dll: StableGlobVars -> Z -> list(TaskID) -> Assertion)

 */
typedef struct {
    LOS_DL_LIST sortLinkNode;
    UINT64 responseTime;
} SortLinkList;
typedef struct SortLinkAttribute{
    LOS_DL_LIST sortLink;
} SortLinkAttribute;
/*@ Import Coq Require Import SimpleC.EE.Applications_human.LiteOS.lib.sortlink */
