From SimpleC.EE.Applications_human.LiteOS_shape Require Import LOS_ListEmpty_goal LOS_ListEmpty_proof_auto LOS_ListEmpty_proof_manual.

Module VC_Correctness : VC_Correct.
  Include los_sortlink_shape_strategy_proof.
  Include LOS_ListEmpty_proof_auto.
  Include LOS_ListEmpty_proof_manual.
End VC_Correctness.
