(** Extend the expectation transformer T_C to all probabilistic terms.
    C stays explicit in the public interface; the generic arithmetic lifting
    depends only on its chosen T_C. No loop-free hypothesis is needed. *)
From Stdlib Require Import List Reals.
Require Import CPHL Soundness.AssertionLogic Soundness.ProbabilisticSubstitution
  Completeness.Interface Completeness.Freshness Completeness.StructuralRules.
Import ListNotations.

Fixpoint lift_preterm (T_C : PConstruct -> Pterm) (p : Pterm) : Pterm :=
  match p with
  | PVar y => PVar y
  | PConst r => PConst r
  | PExpect q => T_C q
  | PAdd a b => PAdd (lift_preterm T_C a) (lift_preterm T_C b)
  | PMul a b => PMul (lift_preterm T_C a) (lift_preterm T_C b)
  end.

Definition wpt (C : Cmd) (T_C : PConstruct -> Pterm) (p : Pterm) : Pterm :=
  lift_preterm T_C p.

Lemma wpt_correct C T_C : expectation_transformer_correct C T_C ->
  forall p ps, pstate_admissible ps ->
    pterm_eval (wpt C T_C p) ps = pterm_eval p (CommandSemantics.run C ps).
Proof.
  intros Hcorrect p ps Hps; unfold wpt; induction p; cbn [lift_preterm pterm_eval].
  - reflexivity.
  - reflexivity.
  - apply Hcorrect; exact Hps.
  - now rewrite IHp1, IHp2.
  - now rewrite IHp1, IHp2.
Qed.

Lemma wpt_occurs C T_C : expectation_transformer_no_prob_vars T_C ->
  forall p y, prob_logic_var_occurs_pterm y (wpt C T_C p) <->
    prob_logic_var_occurs_pterm y p.
Proof.
  intros Hfresh p y; unfold wpt; induction p; cbn [lift_preterm prob_logic_var_occurs_pterm].
  - reflexivity.
  - reflexivity.
  - pose proof (Hfresh q y); tauto.
  - now rewrite IHp1, IHp2.
  - now rewrite IHp1, IHp2.
Qed.

(** A common arithmetic proof for addition and multiplication. *)
Definition combine_preterms (multiply : bool) (a b : Pterm) : Pterm :=
  if multiply then PMul a b else PAdd a b.

Lemma combine_preterms_subst multiply y r a b :
  subst_prob_pterm y r (combine_preterms multiply a b) =
  combine_preterms multiply (subst_prob_pterm y r a) (subst_prob_pterm y r b).
Proof. destruct multiply; reflexivity. Qed.

Lemma derive_combine_preterms multiply C a b a' b' y :
  (forall z, ~ prob_logic_var_occurs_pterm z a ->
    hoare_derivable (p_eq (PVar z) a') C (p_eq (PVar z) a)) ->
  (forall z, ~ prob_logic_var_occurs_pterm z b ->
    hoare_derivable (p_eq (PVar z) b') C (p_eq (PVar z) b)) ->
  hoare_derivable (p_eq (PVar y) (combine_preterms multiply a' b')) C
    (p_eq (PVar y) (combine_preterms multiply a b)).
Proof.
  intros Ha Hb.
  set (avoid := y :: (pterm_prob_vars a ++ pterm_prob_vars b ++
    pterm_prob_vars a' ++ pterm_prob_vars b')).
  set (u := fresh_prob_logic_var avoid).
  set (v := fresh_prob_logic_var (u :: avoid)).
  assert (Hu : ~ In u avoid) by (apply fresh_prob_logic_var_not_in).
  assert (Hv : ~ In v (u :: avoid)) by (apply fresh_prob_logic_var_not_in).
  unfold avoid in Hu, Hv; cbn in Hu, Hv.
  repeat rewrite in_app_iff in Hu, Hv.
  repeat rewrite pterm_prob_vars_spec in Hu, Hv.
  assert (Huy : y <> u) by tauto.
  assert (Hvy : y <> v) by tauto.
  assert (Huv : u <> v) by tauto.
  assert (Hua : ~ prob_logic_var_occurs_pterm u a) by tauto.
  assert (Hvb : ~ prob_logic_var_occurs_pterm v b) by tauto.
  assert (HuA : ~ prob_logic_var_occurs_pterm u a') by tauto.
  assert (HuB : ~ prob_logic_var_occurs_pterm u b') by tauto.
  assert (HvA : ~ prob_logic_var_occurs_pterm v a') by tauto.
  assert (HvB : ~ prob_logic_var_occurs_pterm v b') by tauto.
  set (frame := p_eq (PVar y) (combine_preterms multiply (PVar u) (PVar v))).
  set (bindings := [(u,a');(v,b')]).
  assert (Hind : independent_bindings bindings).
  { split.
    - cbn [bindings map]; repeat constructor; cbn; intuition congruence.
    - intros z r w t Hz Ht; cbn [bindings] in Hz, Ht.
      destruct Hz as [Hz | Hz]; [inversion Hz; subst z r |].
      + destruct Ht as [Ht | Ht]; [inversion Ht; subst w t |]; tauto ||
          (destruct Ht as [Ht | Ht]; [inversion Ht; subst w t; tauto | contradiction]).
      + destruct Hz as [Hz | Hz]; [inversion Hz; subst z r | contradiction].
        destruct Ht as [Ht | Ht]; [inversion Ht; subst w t; tauto |].
        destruct Ht as [Ht | Ht]; [inversion Ht; subst w t; tauto | contradiction]. }
  assert (Hpost : forall z r, In (z,r) bindings ->
    ~ prob_logic_var_occurs_pformula z (p_eq (PVar y) (combine_preterms multiply a b))).
  { intros z r Hz; cbn [bindings] in Hz.
    destruct Hz as [Hz | Hz]; [inversion Hz; subst z r |].
    - destruct multiply; cbn [combine_preterms p_eq p_and p_not
        prob_logic_var_occurs_pformula prob_logic_var_occurs_pterm]; intuition congruence.
    - destruct Hz as [Hz | Hz]; [inversion Hz; subst z r | contradiction].
      destruct multiply; cbn [combine_preterms p_eq p_and p_not
        prob_logic_var_occurs_pformula prob_logic_var_occurs_pterm]; intuition congruence. }
  assert (D : hoare_derivable (bindings_precondition bindings frame) C
    (p_eq (PVar y) (combine_preterms multiply a b))).
  { eapply derive_post with (post := p_and (p_eq (PVar u) a)
      (p_and (p_eq (PVar v) b) frame)).
    - apply HAnd.
      + eapply derive_pre; [| apply Ha; exact Hua].
        intros ps Hps H; cbn [bindings bindings_precondition] in H.
        rewrite !psatisfies_and in H; tauto.
      + apply HAnd.
        * eapply derive_pre; [| apply Hb; exact Hvb].
          intros ps Hps H; cbn [bindings bindings_precondition] in H.
          rewrite !psatisfies_and in H; tauto.
        * eapply derive_pre with (pre' := frame).
          -- intros ps Hps H; cbn [bindings bindings_precondition] in H.
             rewrite !psatisfies_and in H; tauto.
          -- apply HFree; unfold frame; destruct multiply;
             cbn [combine_preterms p_eq p_and p_not pformula_analytical pterm_analytical]; tauto.
    - intros ps Hps H; rewrite !psatisfies_and in H.
      destruct H as [H1 Hrest]; destruct Hrest as [H2 H3].
      apply (proj1 (psatisfies_eq _ _ _)) in H1, H2.
      unfold frame in H3; apply (proj1 (psatisfies_eq _ _ _)) in H3.
      apply (proj2 (psatisfies_eq _ _ _)); destruct multiply;
        cbn [combine_preterms pterm_eval] in *; congruence. }
  pose proof (derive_eliminate_bindings bindings frame C _ Hind Hpost D) as Hresult.
  assert (Heq : substitute_bindings bindings frame =
    p_eq (PVar y) (combine_preterms multiply a' b')).
  { unfold bindings, frame; cbn [substitute_bindings].
    destruct multiply; cbn [combine_preterms subst_prob_pformula p_eq p_and p_not subst_prob_pterm];
      repeat match goal with
      | |- context [prob_logic_var_eq_dec ?z ?w] =>
          destruct (prob_logic_var_eq_dec z w); cbn [subst_prob_pterm]
      end; try congruence;
      rewrite (subst_prob_pterm_fresh v b' a' HvA); reflexivity. }
  rewrite Heq in Hresult; exact Hresult.
Qed.

Theorem wpt_transfer C T_C : exact_expectation_certificate C T_C ->
  forall p y, ~ prob_logic_var_occurs_pterm y p ->
  hoare_derivable (p_eq (PVar y) (wpt C T_C p)) C (p_eq (PVar y) p).
Proof.
  intros Hcert p; induction p as [z | r | q | p1 IHp1 p2 IHp2 | p1 IHp1 p2 IHp2];
    intros y Hy; cbn [wpt lift_preterm].
  - apply HFree; cbn [p_eq p_and p_not pformula_analytical pterm_analytical]; tauto.
  - apply HFree; cbn [p_eq p_and p_not pformula_analytical pterm_analytical]; tauto.
  - apply (certificate_derivable _ _ Hcert).
  - exact (derive_combine_preterms false C p1 p2 (wpt C T_C p1)
      (wpt C T_C p2) y IHp1 IHp2).
  - exact (derive_combine_preterms true C p1 p2 (wpt C T_C p1)
      (wpt C T_C p2) y IHp1 IHp2).
Qed.
