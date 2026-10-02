(** Soundness of the three IF and two SUM constructors. Their recursive
    premises are semantic validities, ready for the final derivation induction. *)
From Stdlib Require Import Reals.
Require Import CPHL Soundness.AssertionLogic Soundness.ConditioningAssertions
  Soundness.InputDecomposition Soundness.SplitCommandFacts.
Import CommandSemantics.

(** Conditioning transfers each arbitrary precondition to its own input
    piece. It is the measures, rather than the formulas, that are split. *)
Lemma if_precondition_states eta1 eta2 guard ps :
  psatisfies ps (if_precondition eta1 eta2 guard) <->
  psatisfies (condition_state guard ps) eta1 /\
  psatisfies (condition_state (c_not guard) ps) eta2.
Proof.
  unfold if_precondition; rewrite psatisfies_and, !condition_pformula_correct; reflexivity.
Qed.

(** Each SUM piece additionally satisfies its concentration premise.
    Almost-sure union coverage is retained for input decomposition. *)
Lemma sum_precondition_states eta1 eta2 gamma delta ps :
  psatisfies ps (sum_precondition eta1 eta2 gamma delta) <->
  psatisfies (condition_state gamma ps) (p_and eta1 (p_almost_sure gamma)) /\
  psatisfies (condition_state delta ps) (p_and eta2 (p_almost_sure delta)) /\
  psatisfies ps (p_almost_sure (c_or gamma delta)).
Proof.
  unfold sum_precondition; rewrite !psatisfies_and, !condition_pformula_correct.
  pose proof (condition_state_almost_sure gamma ps).
  pose proof (condition_state_almost_sure delta ps); tauto.
Qed.

(** All five proofs keep the same external assignment on both pieces and
    on execution. Admissibility of the restrictions licenses both premises.
    Event expectations add even when the output supports overlap. *)
Lemma hoare_valid_if_le eta1 eta2 guard gamma y1 y2 c1 c2 :
  hoare_valid eta1 c1 (PFLe (PVar y1) (PExpect (QIndicator gamma))) ->
  hoare_valid eta2 c2 (PFLe (PVar y2) (PExpect (QIndicator gamma))) ->
  hoare_valid (if_precondition eta1 eta2 guard) (CIf guard c1 c2)
    (PFLe (PAdd (PVar y1) (PVar y2)) (PExpect (QIndicator gamma))).
Proof.
  intros H1 H2 ps Hps Hpre.
  destruct (proj1 (if_precondition_states _ _ _ _) Hpre) as [Ha Hb].
  pose proof (H1 _ (condition_state_admissible _ _ Hps) Ha) as Ho1.
  pose proof (H2 _ (condition_state_admissible _ _ Hps) Hb) as Ho2.
  cbn [psatisfies pterm_eval] in Ho1, Ho2 |- *.
  rewrite (run_if_expectation guard c1 c2 ps (QIndicator gamma) Hps).
  apply Rplus_le_compat; assumption.
Qed.

Lemma hoare_valid_if_ge eta1 eta2 guard gamma y1 y2 c1 c2 :
  hoare_valid eta1 c1 (PFLe (PExpect (QIndicator gamma)) (PVar y1)) ->
  hoare_valid eta2 c2 (PFLe (PExpect (QIndicator gamma)) (PVar y2)) ->
  hoare_valid (if_precondition eta1 eta2 guard) (CIf guard c1 c2)
    (PFLe (PExpect (QIndicator gamma)) (PAdd (PVar y1) (PVar y2))).
Proof.
  intros H1 H2 ps Hps Hpre.
  destruct (proj1 (if_precondition_states _ _ _ _) Hpre) as [Ha Hb].
  pose proof (H1 _ (condition_state_admissible _ _ Hps) Ha) as Ho1.
  pose proof (H2 _ (condition_state_admissible _ _ Hps) Hb) as Ho2.
  cbn [psatisfies pterm_eval] in Ho1, Ho2 |- *.
  rewrite (run_if_expectation guard c1 c2 ps (QIndicator gamma) Hps).
  apply Rplus_le_compat; assumption.
Qed.

Lemma hoare_valid_if_eq eta1 eta2 guard gamma y1 y2 c1 c2 :
  hoare_valid eta1 c1 (p_eq (PVar y1) (PExpect (QIndicator gamma))) ->
  hoare_valid eta2 c2 (p_eq (PVar y2) (PExpect (QIndicator gamma))) ->
  hoare_valid (if_precondition eta1 eta2 guard) (CIf guard c1 c2)
    (p_eq (PAdd (PVar y1) (PVar y2)) (PExpect (QIndicator gamma))).
Proof.
  intros H1 H2 ps Hps Hpre.
  destruct (proj1 (if_precondition_states _ _ _ _) Hpre) as [Ha Hb].
  pose proof (H1 _ (condition_state_admissible _ _ Hps) Ha) as Ho1.
  pose proof (H2 _ (condition_state_admissible _ _ Hps) Hb) as Ho2.
  apply (proj2 (psatisfies_eq _ _ _)).
  apply (proj1 (psatisfies_eq _ _ _)) in Ho1, Ho2.
  cbn [pterm_eval] in Ho1, Ho2 |- *.
  rewrite (run_if_expectation guard c1 c2 ps (QIndicator gamma) Hps).
  exact (f_equal2 Rplus Ho1 Ho2).
Qed.

(** SUM retains its global classical disjointness premise and requires
    coverage only on the current input. Empty pieces and zero total mass
    need no special rule: both recursive premises still apply to those states. *)
Lemma hoare_valid_sum_le eta1 eta2 gamma1 gamma2 gamma y1 y2 c :
  cformula_valid (c_not (c_and gamma1 gamma2)) ->
  hoare_valid (p_and eta1 (p_almost_sure gamma1)) c
    (PFLe (PVar y1) (PExpect (QIndicator gamma))) ->
  hoare_valid (p_and eta2 (p_almost_sure gamma2)) c
    (PFLe (PVar y2) (PExpect (QIndicator gamma))) ->
  hoare_valid (sum_precondition eta1 eta2 gamma1 gamma2) c
    (PFLe (PAdd (PVar y1) (PVar y2)) (PExpect (QIndicator gamma))).
Proof.
  intros Hd H1 H2 ps Hps Hpre.
  destruct (proj1 (sum_precondition_states _ _ _ _ _) Hpre) as [Ha [Hb Hcover] ].
  pose proof (H1 _ (condition_state_admissible _ _ Hps) Ha) as Ho1.
  pose proof (H2 _ (condition_state_admissible _ _ Hps) Hb) as Ho2.
  cbn [psatisfies pterm_eval] in Ho1, Ho2 |- *.
  rewrite (run_sum_expectation gamma1 gamma2 c ps (QIndicator gamma) Hd Hps Hcover).
  apply Rplus_le_compat; assumption.
Qed.

Lemma hoare_valid_sum_ge eta1 eta2 gamma1 gamma2 gamma y1 y2 c :
  cformula_valid (c_not (c_and gamma1 gamma2)) ->
  hoare_valid (p_and eta1 (p_almost_sure gamma1)) c
    (PFLe (PExpect (QIndicator gamma)) (PVar y1)) ->
  hoare_valid (p_and eta2 (p_almost_sure gamma2)) c
    (PFLe (PExpect (QIndicator gamma)) (PVar y2)) ->
  hoare_valid (sum_precondition eta1 eta2 gamma1 gamma2) c
    (PFLe (PExpect (QIndicator gamma)) (PAdd (PVar y1) (PVar y2))).
Proof.
  intros Hd H1 H2 ps Hps Hpre.
  destruct (proj1 (sum_precondition_states _ _ _ _ _) Hpre) as [Ha [Hb Hcover] ].
  pose proof (H1 _ (condition_state_admissible _ _ Hps) Ha) as Ho1.
  pose proof (H2 _ (condition_state_admissible _ _ Hps) Hb) as Ho2.
  cbn [psatisfies pterm_eval] in Ho1, Ho2 |- *.
  rewrite (run_sum_expectation gamma1 gamma2 c ps (QIndicator gamma) Hd Hps Hcover).
  apply Rplus_le_compat; assumption.
Qed.
