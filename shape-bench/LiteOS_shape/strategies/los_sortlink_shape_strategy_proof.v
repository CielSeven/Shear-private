Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human Require Import los_sortlink_shape_strategy_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.LiteOS_shape.lib.glob_vars_and_defs.
Require Import SimpleC.EE.Applications_human.LiteOS_shape.lib.Los_Verify_State_def.
Require Import SimpleC.EE.Applications_human.LiteOS_shape.lib.dll.
Require Import SimpleC.EE.Applications_human.LiteOS_shape.lib.sortlink.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma los_sortlink_shape_strategy7_correctness : los_sortlink_shape_strategy7.
Proof.
  pre_process_default.
  intros.
  entailer!.
  rewrite H.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy14_correctness : los_sortlink_shape_strategy14.
Proof.
  pre_process_default.
  intros.
  entailer!.
  rewrite H.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy15_correctness : los_sortlink_shape_strategy15.
Proof.
  pre_process_default.
  intros.
  entailer!.
  rewrite H.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy18_correctness : los_sortlink_shape_strategy18.
Proof.
  pre_process_default.
Qed.

Lemma los_sortlink_shape_strategy19_correctness : los_sortlink_shape_strategy19.
Proof.
  pre_process_default.
  entailer!.
  rewrite H.
  rewrite H0.
  congruence.
Qed.

Lemma los_sortlink_shape_strategy6_correctness : los_sortlink_shape_strategy6.
Proof.
  pre_process_default.
  intros.
  entailer!.
  rewrite H.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy20_correctness : los_sortlink_shape_strategy20.
Proof.
  pre_process_default.
  intros.
  entailer!.
  rewrite H.
  rewrite H0.
  rewrite H1.
  simpl.
  csimpl.
  destruct a1.
  simpl.
  destruct data0.
  simpl.
  congruence.
Qed.

Lemma los_sortlink_shape_strategy21_correctness : los_sortlink_shape_strategy21.
Proof.
  pre_process_default.
  intros.
  entailer!.
  simpl.
  rewrite H.
  Intros_r v.
  pre_process_default.
  Intros.
  subst v.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy22_correctness : los_sortlink_shape_strategy22.
Proof.
  pre_process_default.
  intros.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
  rewrite H.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy17_correctness : los_sortlink_shape_strategy17.
Proof.
  pre_process_default.
  intros.
  entailer!.
  Exists x.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy3_correctness : los_sortlink_shape_strategy3.
Proof.
  pre_process_default.
  intros.
  entailer!.
  rewrite H.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy8_correctness : los_sortlink_shape_strategy8.
Proof.
  pre_process_default.
  intros.
  entailer!.
  rewrite H.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy11_correctness : los_sortlink_shape_strategy11.
Proof.
  pre_process_default.
  intros.
  entailer!.
  rewrite H.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy46_correctness : los_sortlink_shape_strategy46.
Proof.
  pre_process_default.
  intros.
  entailer!.
  rewrite H.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy47_correctness : los_sortlink_shape_strategy47.
Proof.
  pre_process_default.
  intros.
  entailer!.
  rewrite H.
  rewrite H0.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy39_correctness : los_sortlink_shape_strategy39.
Proof.
  pre_process_default.
  intros.
  entailer!.
  apply store_sorted_dll_concat_shape.
Qed.

Lemma los_sortlink_shape_strategy44_correctness : los_sortlink_shape_strategy44.
Proof.
  pre_process_default.
  intros.
  entailer!.
  unfold storesortedLinkTaskNode.
  Exists p.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy16_correctness : los_sortlink_shape_strategy16.
Proof.
  pre_process_default.
  intros.
  entailer!.
  Intros x0.
  rewrite H.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy34_correctness : los_sortlink_shape_strategy34.
Proof.
  pre_process_default.
  intros.
  entailer!.
  unfold store_dll.
  Exists h pt.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy36_correctness : los_sortlink_shape_strategy36.
Proof.
  pre_process_default.
  intros.
  entailer!.
  unfold store_sorted_dll.
  unfold sortedLinkNodeMappingList.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy38_correctness : los_sortlink_shape_strategy38.
Proof.
  pre_process_default.
  intros.
  sep_apply store_sorted_dll_split_shape.
  Intros h pt py z.
  Exists h pt py z.
  unfold sortedLinkNodeMappingList.
  entailer!.
  Intros_r v.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy40_correctness : los_sortlink_shape_strategy40.
Proof.
  pre_process_default.
  intros.
  unfold store_dll.
  Intros h pt.
  simpl dllseg.
  Intros z.
  subst.
  Exists pt z.
  entailer!.
  Intros_r v p.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy41_correctness : los_sortlink_shape_strategy41.
Proof.
  pre_process_default.
  intros.
  subst.
  unfold storesortedLinkNode.
  Intros y.
  apply addr_of_arrow_field_inv in H.
  inversion H.
  subst.
  entailer!.
  Intros_r v.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy42_correctness : los_sortlink_shape_strategy42.
Proof.
  pre_process_default.
  intros.
  subst.
  unfold obtian_first_pointer in H0.
  entailer!.
  Intros_r v.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy43_correctness : los_sortlink_shape_strategy43.
Proof.
  pre_process_default.
  intros.
  unfold storesortedLinkTaskNode.
  Intros y.
  apply addr_of_arrow_field_inv in H.
  inversion H.
  subst.
  simpl.
  entailer!.
  Intros_r v.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy45_correctness : los_sortlink_shape_strategy45.
Proof.
  pre_process_default.
  intros.
  sep_apply (@store_dll_shift_rev_unfold A storeA x l).
  Intros xn.
  Exists xn.
  entailer!.
  Intros_r target_l.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy33_correctness : los_sortlink_shape_strategy33.
Proof.
  pre_process_default.
  intros.
  unfold store_dll.
  Intros h pt.
  Exists h pt.
  entailer!.
  Intros_r q.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy35_correctness : los_sortlink_shape_strategy35.
Proof.
  pre_process_default.
Qed.

Lemma los_sortlink_shape_strategy31_correctness : los_sortlink_shape_strategy31.
Proof.
  pre_process_default.
  intros.
  unfold storesortedLinkNode.
  Intros y.
  apply addr_of_arrow_field_inv in H.
  inversion H.
  subst.
  simpl.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy32_correctness : los_sortlink_shape_strategy32.
Proof.
  pre_process_default.
  intros.
  unfold storesortedLinkNode.
  Exists p.
  simpl.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy37_correctness : los_sortlink_shape_strategy37.
Proof.
  pre_process_default.
  intros.
  sep_apply (@store_dll_shift_unfold A storeA x l).
  Intros pt.
  Exists pt.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy48_correctness : los_sortlink_shape_strategy48.
Proof.
  pre_process_default.
  intros.
  simpl.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy49_correctness : los_sortlink_shape_strategy49.
Proof.
  pre_process_default.
  intros.
  simpl.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy50_correctness : los_sortlink_shape_strategy50.
Proof.
  pre_process_default.
  intros.
  simpl.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy51_correctness : los_sortlink_shape_strategy51.
Proof.
  pre_process_default.
  intros.
  simpl.
  entailer!.
Qed.

Lemma los_sortlink_shape_strategy52_correctness : los_sortlink_shape_strategy52.
Proof.
  pre_process_default.
  intros.
  simpl.
  Exists x.
  entailer!.
Qed.
