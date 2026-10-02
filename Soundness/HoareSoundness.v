(** Soundness of the shared Hoare calculus over concrete joint measures.
    Assertion premises already mean semantic validity; no separate EPPL
    derivability-to-validity theorem is assumed. *)
From Stdlib Require Import Reals.
Require Import CPHL Soundness.SemanticValidity
  Soundness.StructuralRules Soundness.AtomicRules Soundness.SplitRules
  Soundness.WhileNonentry Soundness.WhileUpper Soundness.WhileLower
  Soundness.WhileExact.

(** Induct on the derivation, not the command: structural rules may have
    recursive premises for the same program. In each while case, the
    generated induction hypothesis supplies semantic validity for every
    indexed body premise. Command semantics is defined independently. *)
Theorem hoare_derivable_sound pre c post :
  hoare_derivable pre c post -> hoare_valid pre c post.
Proof.
  intro derivation; induction derivation.
  - apply hoare_valid_free; assumption.
  - apply hoare_valid_skip.
  - apply hoare_valid_real_assign.
  - apply hoare_valid_bool_assign.
  - apply hoare_valid_bool_toss; assumption.
  - eapply hoare_valid_real_sample; eassumption.
  - eapply hoare_valid_if_le; eassumption.
  - eapply hoare_valid_if_ge; eassumption.
  - eapply hoare_valid_if_eq; eassumption.
  - eapply hoare_valid_elimv; eassumption.
  - eapply hoare_valid_seq; eassumption.
  - eapply hoare_valid_conseq; eassumption.
  - eapply hoare_valid_or; eassumption.
  - eapply hoare_valid_and; eassumption.
  - eapply hoare_valid_sum_le; eassumption.
  - eapply hoare_valid_sum_ge; eassumption.
  - apply hoare_valid_while_not; assumption.
  - eapply hoare_valid_while; eassumption.
  - eapply hoare_valid_while_upper; eassumption.
  - eapply hoare_valid_while_lower; eassumption.
Qed.

(** This exposes the agreed theorem on an arbitrary joint subprobability
    measure and external assignment. Program and classical coordinates may
    be correlated; the same rho interprets the input and output assertions. *)
Corollary hoare_derivable_sound_joint pre c post :
  hoare_derivable pre c post ->
  forall (mu : Measure) (rho : ProbLogicVar -> R), Subprob mu ->
    psatisfies {| pstate_measure := mu; pstate_prob_logic_values := rho |} pre ->
    psatisfies {| pstate_measure := CommandSemantics.transform_cmd c mu;
                 pstate_prob_logic_values := rho |} post.
Proof.
  intro derivation; apply (proj1 (hoare_valid_spec pre c post)).
  exact (hoare_derivable_sound pre c post derivation).
Qed.

(** Output admissibility comes from the previously proved command invariant,
    without a proof field in Pstate or an added derivation premise. *)
Corollary hoare_derivable_sound_result pre c post :
  hoare_derivable pre c post ->
  forall ps, pstate_admissible ps -> psatisfies ps pre ->
    pstate_admissible (CommandSemantics.run c ps) /\
    psatisfies (CommandSemantics.run c ps) post.
Proof.
  intro derivation; apply (proj1 (hoare_valid_admissible_result pre c post)).
  exact (hoare_derivable_sound pre c post derivation).
Qed.
