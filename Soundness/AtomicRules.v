(** Soundness of the four atomic Hoare constructors. All assertion premises
    are interpreted through pformula_valid on admissible joint states. *)
Require Import CPHL Soundness.AssertionLogic Soundness.RealSubstitutionAssertions
  Soundness.BoolSubstitutionAssertions Soundness.AtomicCommandFacts.

Import CommandSemantics.

(** The substitution theorems describe pushforward states; the kernel
    bridges transport their assertions to the actual command outputs. *)
Lemma hoare_valid_real_assign eta x t :
  hoare_valid (subst_real_pformula x t eta) (CRealAssign x t) eta.
Proof.
  intros ps Hps Hpre.
  apply (proj2 (psatisfies_equiv eta _ _ (run_real_assign_equiv x t ps))).
  apply (proj1 (subst_real_pformula_correct x t eta ps)); exact Hpre.
Qed.

Lemma hoare_valid_bool_assign eta b beta :
  hoare_valid (subst_bool_pformula b beta eta) (CBoolAssign b beta) eta.
Proof.
  intros ps Hps Hpre.
  apply (proj2 (psatisfies_equiv eta _ _ (run_bool_assign_equiv b beta ps))).
  apply (proj1 (subst_bool_pformula_correct b beta eta ps)); exact Hpre.
Qed.

(** Valid probabilities, including endpoints zero and one, give precisely
    the weighted expectations used by toss_pformula. *)
Lemma hoare_valid_bool_toss eta b r : coin_probability_valid r ->
  hoare_valid (toss_pformula b r eta) (CBoolToss b r) eta.
Proof.
  intros Hr ps Hps Hpre.
  apply (proj1 (toss_pformula_correct b r eta ps Hps Hr)); exact Hpre.
Qed.

(** The semantic sampling identity includes invalid parameters via the
    shared zero-law convention. It gives this stronger supporting triple. *)
Lemma hoare_valid_sample_wp eta x d :
  hoare_valid (sample_pformula x d eta) (CRealSample x d) eta.
Proof.
  intros ps Hps Hpre.
  apply (proj1 (sample_pformula_correct x d eta ps Hps)); exact Hpre.
Qed.

(** Keep both HRealSample premises unchanged. The second premise restricts
    uses of that syntactic rule, although the total semantic identity above
    already proves its conclusion from the first premise. *)
Lemma hoare_valid_real_sample pre eta x d :
  pformula_valid (PFImpl pre (sample_pformula x d eta)) ->
  pformula_valid (PFImpl pre (p_almost_sure (distribution_valid_formula d))) ->
  hoare_valid pre (CRealSample x d) eta.
Proof.
  intros Hpre Hvalid ps Hps Heta.
  apply (hoare_valid_sample_wp eta x d ps Hps).
  exact (Hpre ps Hps Heta).
Qed.
