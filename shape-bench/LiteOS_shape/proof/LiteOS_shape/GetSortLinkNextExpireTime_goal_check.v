From SimpleC.EE.Applications_human.LiteOS_shape Require Import GetSortLinkNextExpireTime_goal GetSortLinkNextExpireTime_proof_auto GetSortLinkNextExpireTime_proof_manual.

Module VC_Correctness : VC_Correct.
  Include los_sortlink_shape_strategy_proof.
  Include GetSortLinkNextExpireTime_proof_auto.
  Include GetSortLinkNextExpireTime_proof_manual.
End VC_Correctness.
