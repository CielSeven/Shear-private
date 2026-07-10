From SimpleC.EE.Applications_human.LiteOS_shape Require Import OsSortLinkInit_goal OsSortLinkInit_proof_auto OsSortLinkInit_proof_manual.

Module VC_Correctness : VC_Correct.
  Include los_sortlink_shape_strategy_proof.
  Include OsSortLinkInit_proof_auto.
  Include OsSortLinkInit_proof_manual.
End VC_Correctness.
