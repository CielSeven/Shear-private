From SimpleC.EE.Applications_human.LiteOS_shape Require Import List_Add_goal List_Add_proof_auto List_Add_proof_manual.

Module VC_Correctness : VC_Correct.
  Include los_sortlink_shape_strategy_proof.
  Include List_Add_proof_auto.
  Include List_Add_proof_manual.
End VC_Correctness.
