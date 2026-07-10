From SimpleC.EE.Applications_human.LiteOS_shape Require Import OsGetSortLinkAttribute_goal OsGetSortLinkAttribute_proof_auto OsGetSortLinkAttribute_proof_manual.

Module VC_Correctness : VC_Correct.
  Include los_sortlink_shape_strategy_proof.
  Include OsGetSortLinkAttribute_proof_auto.
  Include OsGetSortLinkAttribute_proof_manual.
End VC_Correctness.
