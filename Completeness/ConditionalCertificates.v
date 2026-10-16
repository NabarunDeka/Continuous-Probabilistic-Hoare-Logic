(** Conditional closure applies to any certified branches, including future
    loop classes; it does not require a loop-free premise. *)
From Stdlib Require Import List Reals Lra.
Require Import CPHL Soundness.AssertionLogic Soundness.ProbabilisticSubstitution
  Soundness.ConditioningAssertions Soundness.SplitCommandFacts
  Completeness.Interface Completeness.Freshness Completeness.StructuralRules.
Import ListNotations.

Definition if_expectation_transformer guard (T1 T2 : PConstruct -> Pterm) q :=
  PAdd (condition_pterm (T1 q) guard) (condition_pterm (T2 q) (c_not guard)).

Lemma condition_pterm_occurs p guard y :
  prob_logic_var_occurs_pterm y (condition_pterm p guard) <->
  prob_logic_var_occurs_pterm y p.
Proof.
  induction p; cbn [condition_pterm prob_logic_var_occurs_pterm];
    try tauto; now rewrite IHp1, IHp2.
Qed.

Theorem if_certificate guard C1 C2 T1 T2 :
  exact_expectation_certificate C1 T1 -> exact_expectation_certificate C2 T2 ->
  exact_expectation_certificate (CIf guard C1 C2) (if_expectation_transformer guard T1 T2).
Proof.
  intros H1 H2; constructor.
  - intros q y; cbn [if_expectation_transformer prob_logic_var_occurs_pterm].
    rewrite !condition_pterm_occurs.
    pose proof (certificate_no_prob_vars _ _ H1 q y).
    pose proof (certificate_no_prob_vars _ _ H2 q y); tauto.
  - intros ps q Hps; cbn [if_expectation_transformer pterm_eval].
    rewrite !condition_pterm_correct.
    rewrite (certificate_correct _ _ H1 _ q (condition_state_admissible _ _ Hps)).
    rewrite (certificate_correct _ _ H2 _ q (condition_state_admissible _ _ Hps)).
    symmetry; apply run_if_expectation; exact Hps.
  - intros q y.
    set (a := condition_pterm (T1 q) guard).
    set (b := condition_pterm (T2 q) (c_not guard)).
    assert (Ha : forall z, ~ prob_logic_var_occurs_pterm z a).
    { intro z; unfold a; rewrite condition_pterm_occurs; apply (certificate_no_prob_vars _ _ H1). }
    assert (Hb : forall z, ~ prob_logic_var_occurs_pterm z b).
    { intro z; unfold b; rewrite condition_pterm_occurs; apply (certificate_no_prob_vars _ _ H2). }
    set (u := fresh_prob_logic_var [y]).
    set (v := fresh_prob_logic_var [u;y]).
    assert (Hu : ~ In u [y]) by apply fresh_prob_logic_var_not_in.
    assert (Hv : ~ In v [u;y]) by apply fresh_prob_logic_var_not_in.
    cbn in Hu, Hv.
    assert (Huy : y <> u) by tauto.
    assert (Hvy : y <> v) by tauto.
    assert (Huv : u <> v) by tauto.
    set (frame := p_eq (PVar y) (PAdd (PVar u) (PVar v))).
    set (bindings := [(u,a);(v,b)]).
    assert (Hind : independent_bindings bindings).
    { split.
      - cbn [bindings map]; repeat constructor; cbn; intuition congruence.
      - intros z r w t Hz Ht; cbn [bindings] in Ht.
        destruct Ht as [Ht | Ht]; [inversion Ht; subst w t; apply Ha |].
        destruct Ht as [Ht | Ht]; [inversion Ht; subst w t; apply Hb | contradiction]. }
    assert (Hpost : forall z r, In (z,r) bindings ->
      ~ prob_logic_var_occurs_pformula z (p_eq (PVar y) (PExpect q))).
    { intros z r Hz; cbn [bindings] in Hz.
      destruct Hz as [Hz | Hz]; [inversion Hz; subst z r |].
      - cbn [p_eq p_and p_not prob_logic_var_occurs_pformula prob_logic_var_occurs_pterm];
          intuition congruence.
      - destruct Hz as [Hz | Hz]; [inversion Hz; subst z r | contradiction].
        cbn [p_eq p_and p_not prob_logic_var_occurs_pformula prob_logic_var_occurs_pterm];
          intuition congruence. }
    assert (D : hoare_derivable (bindings_precondition bindings frame)
      (CIf guard C1 C2) (p_eq (PVar y) (PExpect q))).
    { eapply derive_post with (post := p_and
        (p_eq (PAdd (PVar u) (PVar v)) (PExpect q)) frame).
      - apply HAnd.
        + eapply derive_pre with (pre' := if_precondition
            (p_eq (PVar u) (T1 q)) (p_eq (PVar v) (T2 q)) guard).
          * intros ps Hps H; cbn [bindings bindings_precondition] in H.
            rewrite !psatisfies_and in H.
            unfold if_precondition; apply psatisfies_and; split.
            -- change (psatisfies ps (p_eq (PVar u) a)); tauto.
            -- change (psatisfies ps (p_eq (PVar v) b)); tauto.
          * apply HIfEq; [apply (certificate_derivable _ _ H1) | apply (certificate_derivable _ _ H2)].
        + eapply derive_pre with (pre' := frame).
          * intros ps Hps H; cbn [bindings bindings_precondition] in H.
            rewrite !psatisfies_and in H; tauto.
          * apply HFree; unfold frame;
              cbn [p_eq p_and p_not pformula_analytical pterm_analytical]; tauto.
      - intros ps Hps H; apply psatisfies_and in H; destruct H as [Hsum Hframe].
        apply psatisfies_eq in Hsum; unfold frame in Hframe; apply psatisfies_eq in Hframe.
        apply psatisfies_eq; cbn [pterm_eval] in *; congruence. }
    pose proof (derive_eliminate_bindings bindings frame _ _ Hind Hpost D) as Hresult.
    assert (Heq : substitute_bindings bindings frame = p_eq (PVar y) (PAdd a b)).
    { unfold bindings, frame; cbn [substitute_bindings subst_prob_pformula p_eq p_and p_not subst_prob_pterm].
      repeat match goal with
      | |- context [prob_logic_var_eq_dec ?z ?w] =>
          destruct (prob_logic_var_eq_dec z w); cbn [subst_prob_pterm]
      end; try congruence;
      rewrite (subst_prob_pterm_fresh v b a (Ha v)); reflexivity. }
    rewrite Heq in Hresult; exact Hresult.
Qed.
