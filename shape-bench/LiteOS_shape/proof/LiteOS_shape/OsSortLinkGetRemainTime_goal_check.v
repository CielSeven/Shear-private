From SimpleC.EE.Applications_human.LiteOS_shape Require Import OsSortLinkGetRemainTime_goal OsSortLinkGetRemainTime_proof_auto OsSortLinkGetRemainTime_proof_manual.

Module VC_Correctness : VC_Correct.
  Include los_sortlink_shape_strategy_proof.
  Include OsSortLinkGetRemainTime_proof_auto.
  Include OsSortLinkGetRemainTime_proof_manual.
End VC_Correctness.
