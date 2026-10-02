(** Semantic soundness of FREE, SKIP, ELIMV, SEQ, CONSEQ, OR, and AND.
    Recursive rule premises are semantic validities: the final induction on
    hoare_derivable will supply them. No derivation soundness is assumed here. *)
From Stdlib Require Import Reals.
Require Import CPHL Soundness.CommandFacts Soundness.TransformerFacts
  Soundness.SemanticValidity Soundness.AssertionLogic Soundness.ProbabilisticSubstitution.

Import CommandSemantics.

(** SKIP and composition agree with their expected state transformers on
    measurable events. Assertion extensionality avoids measure-record equality. *)
Lemma run_skip_equiv ps : pstate_equiv (run CSkip ps) ps.
Proof.
  split.
  - intros A HA; apply transform_skip; exact HA.
  - intro y; reflexivity.
Qed.

Lemma run_seq_equiv c1 c2 ps : pstate_admissible ps ->
  pstate_equiv (run (CSeq c1 c2) ps) (run c2 (run c1 ps)).
Proof.
  intros Hps; split.
  - intros A HA; apply transform_sequence; assumption.
  - intro y; reflexivity.
Qed.

(** Analytical formulas observe only the unchanged external assignment.
    FREE therefore applies even when the command loses all input mass. *)
Lemma hoare_valid_free eta c : pformula_analytical eta -> hoare_valid eta c eta.
Proof.
  intros Han ps Hps Hpre.
  apply (proj1 (psatisfies_analytical_measure_independent eta ps (run c ps)
    Han (fun _ => eq_refl))).
  exact Hpre.
Qed.

Lemma hoare_valid_skip eta : hoare_valid eta CSkip eta.
Proof.
  intros ps Hps Hpre.
  apply (proj2 (psatisfies_equiv eta (run CSkip ps) ps (run_skip_equiv ps))).
  exact Hpre.
Qed.

(** The second premise is instantiated at an admissible intermediate state;
    this also covers zero intermediate mass and commands containing loops. *)
Lemma hoare_valid_seq eta1 eta2 eta3 c1 c2 :
  hoare_valid eta1 c1 eta2 -> hoare_valid eta2 c2 eta3 ->
  hoare_valid eta1 (CSeq c1 c2) eta3.
Proof.
  intros H1 H2 ps Hps Hpre.
  apply (proj2 (psatisfies_equiv eta3 _ _ (run_seq_equiv c1 c2 ps Hps))).
  apply H2.
  - apply run_admissible; exact Hps.
  - exact (H1 ps Hps Hpre).
Qed.

(** Assertion premises use pformula_valid on admissible states. In particular,
    the post-implication needs the output-admissibility theorem. *)
Lemma hoare_valid_conseq eta0 eta1 eta2 eta3 c :
  pformula_valid (PFImpl eta0 eta1) -> hoare_valid eta1 c eta2 ->
  pformula_valid (PFImpl eta2 eta3) -> hoare_valid eta0 c eta3.
Proof.
  intros Hpre Hbody Hpost ps Hps Heta.
  assert (Hout : pstate_admissible (run c ps)).
  { apply run_admissible; exact Hps. }
  exact (Hpost _ Hout (Hbody ps Hps (Hpre ps Hps Heta))).
Qed.

(** OR selects a valid premise for the whole input; it does not split or
    normalize the input measure. AND uses the same output for both premises. *)
Lemma hoare_valid_or eta0 eta1 eta2 c :
  hoare_valid eta0 c eta2 -> hoare_valid eta1 c eta2 ->
  hoare_valid (p_or eta0 eta1) c eta2.
Proof.
  intros H0 H1 ps Hps Hpre.
  destruct (proj1 (psatisfies_or ps eta0 eta1) Hpre) as [Heta | Heta].
  - exact (H0 ps Hps Heta).
  - exact (H1 ps Hps Heta).
Qed.

Lemma hoare_valid_and eta0 eta1 eta2 c :
  hoare_valid eta0 c eta1 -> hoare_valid eta0 c eta2 ->
  hoare_valid eta0 c (p_and eta1 eta2).
Proof.
  intros H1 H2 ps Hps Hpre.
  apply (proj2 (psatisfies_and (run c ps) eta1 eta2)); split.
  - exact (H1 ps Hps Hpre).
  - exact (H2 ps Hps Hpre).
Qed.

(** Freeze p's input value in rho(y). Freshness of p establishes y=p in
    that state; freshness of eta2 restores the original assignment afterward.
    Execution commutes with this fixed-value update, even when p contains an
    expectation whose value changes during execution. *)
Lemma hoare_valid_elimv eta1 eta2 y p c :
  hoare_valid (p_and eta1 (p_eq (PVar y) p)) c eta2 ->
  ~ prob_logic_var_occurs_pterm y p ->
  ~ prob_logic_var_occurs_pformula y eta2 ->
  hoare_valid (subst_prob_pformula y p eta1) c eta2.
Proof.
  intros Hbody Hfresh_p Hfresh_post ps Hps Hpre.
  apply (proj1 (psatisfies_update_prob_fresh y eta2 (run c ps)
    (pterm_eval p ps) Hfresh_post)).
  rewrite <- run_update_prob_state.
  apply Hbody.
  - apply (proj2 (update_prob_state_admissible ps y (pterm_eval p ps))); exact Hps.
  - apply (proj2 (psatisfies_and _ eta1 (p_eq (PVar y) p))); split.
    + apply (proj1 (subst_prob_pformula_correct y p eta1 ps)); exact Hpre.
    + apply (proj2 (psatisfies_eq _ (PVar y) p)).
      rewrite (pterm_eval_update_prob_fresh y p ps (pterm_eval p ps) Hfresh_p).
      apply update_prob_assignment_here.
Qed.
