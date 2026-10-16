(** Sequential closure for arbitrary certified commands. No loop-free
    premise is required, including for intermediate-state admissibility. *)
Require Import CPHL Soundness.AssertionLogic Soundness.StructuralRules
  Soundness.TransformerFacts Completeness.Interface Completeness.WeakestPreterm.

Definition seq_expectation_transformer C1 (T1 T2 : PConstruct -> Pterm) q :=
  wpt C1 T1 (T2 q).

Theorem seq_certificate C1 C2 T1 T2 :
  exact_expectation_certificate C1 T1 -> exact_expectation_certificate C2 T2 ->
  exact_expectation_certificate (CSeq C1 C2) (seq_expectation_transformer C1 T1 T2).
Proof.
  intros H1 H2; constructor.
  - intros q y; unfold seq_expectation_transformer.
    rewrite (wpt_occurs C1 T1 (certificate_no_prob_vars _ _ H1)).
    apply (certificate_no_prob_vars _ _ H2).
  - intros ps q Hps; unfold seq_expectation_transformer.
    rewrite (wpt_correct C1 T1 (certificate_correct _ _ H1) (T2 q) ps Hps).
    rewrite (certificate_correct _ _ H2 _ q (@run_admissible C1 ps Hps)).
    change (pterm_eval (PExpect q) (CommandSemantics.run C2 (CommandSemantics.run C1 ps)) =
      pterm_eval (PExpect q) (CommandSemantics.run (CSeq C1 C2) ps)).
    symmetry; apply pterm_eval_equiv; apply run_seq_equiv; exact Hps.
  - intros q y; unfold seq_expectation_transformer.
    eapply HSeq with (eta2 := p_eq (PVar y) (T2 q)).
    + apply wpt_transfer; [exact H1 | apply (certificate_no_prob_vars _ _ H2)].
    + apply (certificate_derivable _ _ H2).
Qed.
