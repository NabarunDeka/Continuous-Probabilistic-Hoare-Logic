(** The intended semantic judgment, unpacked over the concrete state space.
    These are interface facts, not an induction proving Hoare-rule soundness. *)
From Stdlib Require Import Reals.
Require Import CPHL Soundness.TransformerFacts Soundness.AssertionFacts.

Lemma hoare_valid_spec pre c post : hoare_valid pre c post <->
  forall (mu : Measure) (rho : ProbLogicVar -> R), Subprob mu ->
    psatisfies {| pstate_measure := mu; pstate_prob_logic_values := rho |} pre ->
    psatisfies {| pstate_measure := CommandSemantics.transform_cmd c mu;
                 pstate_prob_logic_values := rho |} post.
Proof.
  split.
  - intros H mu rho Hmu Hpre.
    exact (H {| pstate_measure := mu; pstate_prob_logic_values := rho |} Hmu Hpre).
  - intros H [mu rho] Hmu Hpre; exact (H mu rho Hmu Hpre).
Qed.

Lemma hoare_valid_at pre c post ps : hoare_valid pre c post ->
  pstate_admissible ps -> psatisfies ps pre ->
  psatisfies (CommandSemantics.run c ps) post.
Proof. intros H Hps Hpre; exact (H ps Hps Hpre). Qed.

(** Including output admissibility would give an equivalent judgment, but
    would duplicate an invariant already supplied by the command semantics. *)
Lemma hoare_valid_admissible_result pre c post : hoare_valid pre c post <->
  forall ps, pstate_admissible ps -> psatisfies ps pre ->
    pstate_admissible (CommandSemantics.run c ps) /\
    psatisfies (CommandSemantics.run c ps) post.
Proof.
  split.
  - intros H ps Hps Hpre; split.
    + apply run_admissible; exact Hps.
    + exact (H ps Hps Hpre).
  - intros H ps Hps Hpre; exact (proj2 (H ps Hps Hpre)).
Qed.

(** Semantic assertion premises may be instantiated at intermediate or final
    states using the proved invariant, without a proof field in Pstate. *)
Lemma pformula_valid_at_output eta c ps : pformula_valid eta ->
  pstate_admissible ps -> psatisfies (CommandSemantics.run c ps) eta.
Proof.
  intros Heta Hps; apply Heta; apply run_admissible; exact Hps.
Qed.
