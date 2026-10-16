(** Exact sampling certificates, including mixed-validity input measures. *)
From Stdlib Require Import List Reals Lra.
Require Import CPHL Soundness.AssertionLogic Soundness.ProbabilisticSubstitution Soundness.AtomicCommandFacts
  Soundness.CommandFacts Soundness.InvalidSampling Soundness.ConditioningAssertions Soundness.InputDecomposition
  Completeness.Interface Completeness.Freshness Completeness.StructuralRules
  Completeness.AtomicCertificates.
Import ListNotations.

Definition sample_expectation_transformer x d (q : PConstruct) : Pterm :=
  PExpect (QIntegral x d q).

(** The invalid restriction contributes zero; hence the valid restriction
    retains the entire pre-expectation, without normalizing either part. *)
Lemma sample_preexpectation_valid_restriction x d q ps : pstate_admissible ps ->
  pterm_eval (sample_expectation_transformer x d q)
    (condition_state (distribution_valid_formula d) ps) =
  pterm_eval (sample_expectation_transformer x d q) ps.
Proof.
  intro Hps.
  pose proof (condition_expectation_partition (QIntegral x d q)
    (distribution_valid_formula d) (pstate_measure ps) Hps) as Hsplit.
  rewrite !condition_expectation_correct in Hsplit.
  assert (Hz : expectation
    (pstate_measure (condition_state (c_not (distribution_valid_formula d)) ps))
    (q_eval (QIntegral x d q)) = 0%R).
  { change (pterm_eval (sample_pterm x d (PExpect q))
      (condition_state (c_not (distribution_valid_formula d)) ps) = 0%R).
    rewrite sample_pterm_correct by (apply condition_state_admissible; exact Hps).
    apply run_sample_invalid_expectation.
    - apply condition_state_admissible; exact Hps.
    - apply condition_state_almost_sure. }
  change (expectation (pstate_measure ps) (q_eval (QIntegral x d q)) =
    Rplus (expectation (pstate_measure (condition_state (distribution_valid_formula d) ps))
      (q_eval (QIntegral x d q)))
    (expectation (pstate_measure (condition_state (c_not (distribution_valid_formula d)) ps))
      (q_eval (QIntegral x d q)))) in Hsplit.
  rewrite Hz, Rplus_0_r in Hsplit; symmetry; exact Hsplit.
Qed.

Lemma sample_invalid_transfer x d q z :
  hoare_derivable
    (p_and (p_eq (PVar z) (PConst 0%R))
      (p_almost_sure (c_not (distribution_valid_formula d))))
    (CRealSample x d) (p_eq (PVar z) (PExpect q)).
Proof.
  eapply derive_post with (post := p_and
    (p_eq (PExpect (QIndicator c_true)) (PConst 0%R))
    (p_eq (PVar z) (PConst 0%R))).
  - apply HAnd.
    + apply HRealSampleInvalid; intros ps Hps H; apply psatisfies_and in H; tauto.
    + eapply derive_pre; [| apply HFree].
      * intros ps Hps H; apply psatisfies_and in H; tauto.
      * cbn [p_eq p_and p_not pformula_analytical pterm_analytical]; tauto.
  - intros ps Hps H; apply psatisfies_and in H; destruct H as [Hm Hz].
    apply psatisfies_eq in Hz; apply psatisfies_eq.
    rewrite (zero_mass_expectation q ps Hps Hm); exact Hz.
Qed.

Theorem sample_certificate x d :
  exact_expectation_certificate (CRealSample x d) (sample_expectation_transformer x d).
Proof.
  constructor.
  - intros q y; cbn [sample_expectation_transformer prob_logic_var_occurs_pterm]; tauto.
  - intros ps q Hps; symmetry; apply transform_sample_q_eval; exact Hps.
  - intros q y.
    set (z := fresh_prob_logic_var [y]).
    assert (Hzy : y <> z).
    { pose proof (fresh_prob_logic_var_not_in [y]); unfold z; cbn in *; tauto. }
    set (pre := p_eq (PVar y) (sample_expectation_transformer x d q)).
    set (zero := p_eq (PVar z) (PConst 0%R)).
    set (g := distribution_valid_formula d).
    assert (D : hoare_derivable (p_and pre zero) (CRealSample x d)
      (p_eq (PVar y) (PExpect q))).
    { eapply derive_post with (post := p_and
        (p_eq (PAdd (PVar y) (PVar z)) (PExpect q)) zero).
      - apply HAnd.
        + eapply derive_pre with (pre' := sum_precondition pre zero g (c_not g)).
          * intros ps Hps H; apply psatisfies_and in H; destruct H as [Hy Hz].
            unfold sum_precondition; apply psatisfies_and; split.
            -- apply psatisfies_and; split; apply condition_pformula_correct.
               ++ unfold pre in *; apply psatisfies_eq in Hy; apply psatisfies_eq.
                  change (pstate_prob_logic_values ps y =
                    pterm_eval (sample_expectation_transformer x d q)
                      (condition_state (distribution_valid_formula d) ps)).
                  rewrite (sample_preexpectation_valid_restriction x d q ps Hps).
                  exact Hy.
               ++ exact Hz.
            -- apply psatisfies_almost_sure; rewrite !expectation_indicator.
               apply measure_extensional; intro v.
               unfold formula_assertion, c_or, c_not, c_true; cbn [satisfies].
               destruct (cformula_satisfies_dec g v); tauto.
          * apply derive_sum_eq.
            -- intro v; cbn [c_not c_and satisfies]; tauto.
            -- apply HRealSample.
               ++ intros ps Hps H; apply psatisfies_and in H; exact (proj1 H).
               ++ intros ps Hps H; apply psatisfies_and in H; exact (proj2 H).
            -- apply sample_invalid_transfer.
        + eapply derive_pre with (pre' := zero).
          * intros ps Hps H; apply psatisfies_and in H; tauto.
          * apply HFree; unfold zero;
              cbn [p_eq p_and p_not pformula_analytical pterm_analytical]; tauto.
      - intros ps Hps H; apply psatisfies_and in H; destruct H as [Hsum Hz].
        apply psatisfies_eq in Hsum; unfold zero in Hz; apply psatisfies_eq in Hz.
        apply psatisfies_eq; cbn [pterm_eval] in *; lra. }
    assert (Hzpre : ~ prob_logic_var_occurs_pformula z pre).
    { unfold pre; cbn [p_eq p_and p_not sample_expectation_transformer
        prob_logic_var_occurs_pformula prob_logic_var_occurs_pterm]; intuition congruence. }
    pose proof (HElimv pre (p_eq (PVar y) (PExpect q)) z (PConst 0%R)
      (CRealSample x d) D (ltac:(cbn; tauto))
      (ltac:(cbn [p_eq p_and p_not prob_logic_var_occurs_pformula
        prob_logic_var_occurs_pterm]; intuition congruence))) as Helim.
    rewrite (subst_prob_pformula_fresh z (PConst 0%R) pre Hzpre) in Helim.
    exact Helim.
Qed.
