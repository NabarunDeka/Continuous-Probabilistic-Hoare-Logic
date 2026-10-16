(** Relative completeness for any command equipped with an exact expectation
    certificate. Construction of certificates for commands is a later layer. *)
From Stdlib Require Import List Reals.
Require Import CPHL Soundness.AssertionLogic Soundness.ProbabilisticSubstitution
  Completeness.Interface Completeness.Freshness Completeness.StructuralRules
  Completeness.WeakestPreterm Completeness.FormulaAbstraction.
Import ListNotations.

Fixpoint wp (C : Cmd) (T_C : PConstruct -> Pterm) (eta : PFormula) : PFormula :=
  match eta with
  | PFLe a b => PFLe (wpt C T_C a) (wpt C T_C b)
  | PFFalse => PFFalse
  | PFImpl a b => PFImpl (wp C T_C a) (wp C T_C b)
  end.

Theorem wp_correct C T_C : expectation_transformer_correct C T_C ->
  forall eta ps, pstate_admissible ps ->
  (psatisfies ps (wp C T_C eta) <-> psatisfies (CommandSemantics.run C ps) eta).
Proof.
  intros H eta ps Hps; induction eta; cbn [wp psatisfies].
  - rewrite !wpt_correct by assumption; reflexivity.
  - tauto.
  - rewrite IHeta1, IHeta2; reflexivity.
Qed.

Lemma wp_occurs C T_C : expectation_transformer_no_prob_vars T_C ->
  forall eta y, prob_logic_var_occurs_pformula y (wp C T_C eta) <->
    prob_logic_var_occurs_pformula y eta.
Proof.
  intros H eta y; induction eta; cbn [wp prob_logic_var_occurs_pformula].
  - rewrite !wpt_occurs by assumption; reflexivity.
  - reflexivity.
  - rewrite IHeta1, IHeta2; reflexivity.
Qed.

Lemma bindings_precondition_spec bs frame ps :
  psatisfies ps (bindings_precondition bs frame) <->
  psatisfies ps frame /\ bindings_hold ps bs.
Proof.
  induction bs as [|[y p] rest IH]; cbn [bindings_precondition].
  - unfold bindings_hold; cbn; tauto.
  - rewrite psatisfies_and, psatisfies_eq, IH; cbn [pterm_eval].
    unfold bindings_hold; cbn; split.
    + intros H; destruct H as [Hrest Hy]; destruct Hrest as [Hframe Hr].
      split; [exact Hframe |].
      intros z r Hin; destruct Hin as [Hin | Hin]; [inversion Hin; subst; exact Hy | auto].
    + intros H; destruct H as [Hframe H]; split; [split; [exact Hframe |] |].
      * intros z r Hin; apply H; auto.
      * apply H; auto.
Qed.

(** The semantic assignment order mirrors syntactic substitution: the tail
    is interpreted first, then the head replacement is evaluated once. *)
Fixpoint instantiate_bindings (bs : ProbBindings) (ps : Pstate) : Pstate :=
  match bs with
  | [] => ps
  | (y,p) :: rest => let qs := instantiate_bindings rest ps in
      update_prob_state qs y (pterm_eval p qs)
  end.

Lemma substitute_bindings_correct bs frame ps :
  psatisfies ps (substitute_bindings bs frame) <->
  psatisfies (instantiate_bindings bs ps) frame.
Proof.
  revert frame; induction bs as [|[y p] rest IH]; intro frame; cbn.
  - reflexivity.
  - rewrite IH, subst_prob_pformula_correct; reflexivity.
Qed.

Lemma instantiate_bindings_admissible bs ps : pstate_admissible ps ->
  pstate_admissible (instantiate_bindings bs ps).
Proof.
  induction bs as [|[y p] rest IH]; cbn; [auto |].
  rewrite update_prob_state_admissible; exact IH.
Qed.

Lemma instantiate_bindings_term_fresh bs p ps :
  (forall y r, In (y,r) bs -> ~ prob_logic_var_occurs_pterm y p) ->
  pterm_eval p (instantiate_bindings bs ps) = pterm_eval p ps.
Proof.
  induction bs as [|[y r] rest IH]; intro H; cbn; [reflexivity |].
  rewrite pterm_eval_update_prob_fresh.
  - apply IH; intros z t Hin; apply (H z t); cbn; auto.
  - apply (H y r); cbn; auto.
Qed.

Lemma instantiate_bindings_formula_fresh bs eta ps :
  (forall y r, In (y,r) bs -> ~ prob_logic_var_occurs_pformula y eta) ->
  (psatisfies (instantiate_bindings bs ps) eta <-> psatisfies ps eta).
Proof.
  induction bs as [|[y r] rest IH]; intro H; cbn; [reflexivity |].
  rewrite psatisfies_update_prob_fresh.
  - apply IH; intros z t Hin; apply (H z t); cbn; auto.
  - apply (H y r); cbn; auto.
Qed.

Lemma independent_bindings_tail y p bs :
  independent_bindings ((y,p)::bs) -> independent_bindings bs.
Proof.
  intros H; destruct H as [Hd Hf]; split.
  - inversion Hd; assumption.
  - intros z r w t Hz Hw; apply (Hf z r w t); cbn; auto.
Qed.

Lemma instantiate_bindings_value bs ps : independent_bindings bs ->
  forall y p, In (y,p) bs ->
  pstate_prob_logic_values (instantiate_bindings bs ps) y = pterm_eval p ps.
Proof.
  induction bs as [|[z r] rest IH]; intros Hind y p Hin; cbn in Hin; [contradiction |].
  pose proof (independent_bindings_tail z r rest Hind) as Htail.
  destruct Hind as [Hd Hf].
  destruct Hin as [Hin | Hin].
  - inversion Hin; subst y p; cbn [instantiate_bindings pstate_prob_logic_values update_prob_state].
    rewrite update_prob_assignment_here.
    apply instantiate_bindings_term_fresh; intros w t Hw.
    apply (Hf w t z r); cbn; auto.
  - cbn [instantiate_bindings pstate_prob_logic_values update_prob_state].
    rewrite update_prob_assignment_other.
    + apply IH; assumption.
    + intro Heq; subst y; inversion Hd; subst.
      match goal with Hnot : ~ In z _ |- _ => apply Hnot end.
      apply in_map_iff; exists (z,p); auto.
Qed.

Lemma instantiate_bindings_hold bs ps : independent_bindings bs ->
  bindings_hold (instantiate_bindings bs ps) bs.
Proof.
  intros H y p Hin; rewrite (instantiate_bindings_value bs ps H y p Hin).
  symmetry; apply instantiate_bindings_term_fresh; intros z r Hz.
  exact (proj2 H z r y p Hz Hin).
Qed.

Definition preterm_bindings C T_C (bs : ProbBindings) : ProbBindings :=
  map (fun yp => (fst yp, wpt C T_C (snd yp))) bs.

Lemma abstraction_name_fresh eta frame bs :
  formula_abstraction eta (pformula_prob_vars eta) frame bs ->
  forall y p, In (y,p) bs -> ~ prob_logic_var_occurs_pformula y eta.
Proof.
  intros H y p Hin; rewrite <- pformula_prob_vars_spec.
  exact (abstraction_avoids _ _ _ _ H y p Hin).
Qed.

Lemma abstraction_preterms_independent C T_C eta frame bs :
  expectation_transformer_no_prob_vars T_C ->
  formula_abstraction eta (pformula_prob_vars eta) frame bs ->
  independent_bindings (preterm_bindings C T_C bs).
Proof.
  intros Hfresh Habs; split.
  - unfold preterm_bindings; rewrite map_map.
    change (NoDup (map (@fst ProbLogicVar Pterm) bs)).
    exact (abstraction_distinct _ _ _ _ Habs).
  - intros y p z r Hy Hz; apply in_map_iff in Hy, Hz.
    destruct Hy as [yp Hy]; destruct yp as [y' p']; destruct Hy as [Hy HinY]; inversion Hy; subst y p.
    destruct Hz as [zr Hz]; destruct zr as [z' r']; destruct Hz as [Hz HinZ]; inversion Hz; subst z r.
    rewrite wpt_occurs by exact Hfresh; intro Hocc.
    apply (abstraction_name_fresh _ _ _ Habs y' p' HinY).
    eapply comparison_term_vars; [exact (abstraction_terms _ _ _ _ Habs z' r' HinZ) | exact Hocc].
Qed.

Lemma abstraction_preterms_correct C T_C eta frame bs :
  expectation_transformer_correct C T_C ->
  formula_abstraction eta (pformula_prob_vars eta) frame bs ->
  forall ps, pstate_admissible ps -> bindings_hold ps (preterm_bindings C T_C bs) ->
  (psatisfies ps frame <-> psatisfies ps (wp C T_C eta)).
Proof.
  intros Hcorrect Habs ps Hps Hbindings.
  rewrite (wp_correct C T_C Hcorrect eta ps Hps).
  rewrite (psatisfies_analytical_measure_independent frame ps (CommandSemantics.run C ps)
    (abstraction_analytical _ _ _ _ Habs) (fun _ => eq_refl)).
  apply (abstraction_correct _ _ _ _ Habs).
  intros y p Hin.
  change (pstate_prob_logic_values ps y = pterm_eval p (CommandSemantics.run C ps)).
  rewrite <- (wpt_correct C T_C Hcorrect p ps Hps).
  apply Hbindings; unfold preterm_bindings; apply in_map_iff; exists (y,p); auto.
Qed.

Theorem wp_derivable C T_C : exact_expectation_certificate C T_C ->
  forall eta, hoare_derivable (wp C T_C eta) C eta.
Proof.
  intros Hcert eta.
  destruct (formula_abstraction_exists eta (pformula_prob_vars eta)) as [frame Hframe].
  destruct Hframe as [bs Habs].
  pose proof (certificate_no_prob_vars _ _ Hcert) as Hfresh.
  pose proof (certificate_correct _ _ Hcert) as Hcorrect.
  set (inputs := preterm_bindings C T_C bs).
  assert (Hind : independent_bindings inputs).
  { apply abstraction_preterms_independent with (eta := eta) (frame := frame); assumption. }
  assert (Hpost : forall y p, In (y,p) inputs -> ~ prob_logic_var_occurs_pformula y eta).
  { intros y p Hin; apply in_map_iff in Hin.
    destruct Hin as [zr Hin]; destruct zr as [z r]; destruct Hin as [Heq Hr]; inversion Heq; subst y p.
    exact (abstraction_name_fresh _ _ _ Habs z r Hr). }
  assert (D : hoare_derivable (bindings_precondition inputs frame) C eta).
  { eapply derive_post with (post := p_and frame
      (pformula_conjunction (map (fun yp => p_eq (PVar (fst yp)) (snd yp)) bs))).
    - apply HAnd.
      + eapply derive_pre with (pre' := frame).
        * intros ps Hps H; apply (proj1 (bindings_precondition_spec _ _ _)) in H; tauto.
        * apply HFree; exact (abstraction_analytical _ _ _ _ Habs).
      + apply derive_conjunction; intros post Hin; apply in_map_iff in Hin.
        destruct Hin as [yp Hin]; destruct yp as [y p]; destruct Hin as [Heq Hr]; subst post; cbn.
        eapply derive_pre with (pre' := p_eq (PVar y) (wpt C T_C p)).
        * intros ps Hps H; apply (proj1 (bindings_precondition_spec _ _ _)) in H.
          apply (proj2 (psatisfies_eq _ _ _)); cbn [pterm_eval]; apply (proj2 H).
          unfold inputs, preterm_bindings; apply in_map_iff; exists (y,p); auto.
        * apply wpt_transfer; [exact Hcert |].
          intro Hocc; apply (abstraction_name_fresh _ _ _ Habs y p Hr).
          eapply comparison_term_vars; [exact (abstraction_terms _ _ _ _ Habs y p Hr) | exact Hocc].
    - intros ps Hps H; apply (proj1 (psatisfies_and _ _ _)) in H.
      destruct H as [Hframe Hb].
      assert (Hholds : bindings_hold ps bs).
      { intros y p Hin; apply (proj1 (psatisfies_eq ps (PVar y) p)).
        apply (proj1 (psatisfies_conjunction _ _) Hb).
        apply in_map_iff; exists (y,p); auto. }
      exact (proj1 (abstraction_correct _ _ _ _ Habs ps Hholds) Hframe). }
  pose proof (derive_eliminate_bindings inputs frame C eta Hind Hpost D) as Delim.
  eapply derive_pre; [| exact Delim].
  intros ps Hps Hwp; apply (proj2 (substitute_bindings_correct _ _ _)).
  apply (proj2 (abstraction_preterms_correct C T_C eta frame bs Hcorrect Habs
    (instantiate_bindings inputs ps) (instantiate_bindings_admissible inputs ps Hps)
    (instantiate_bindings_hold inputs ps Hind))).
  assert (HwpFresh : forall y p, In (y,p) inputs ->
    ~ prob_logic_var_occurs_pformula y (wp C T_C eta)).
  { intros y p Hin; rewrite wp_occurs by exact Hfresh; apply (Hpost y p Hin). }
  exact (proj2 (instantiate_bindings_formula_fresh inputs (wp C T_C eta) ps HwpFresh) Hwp).
Qed.

Theorem certified_relative_complete C T_C : exact_expectation_certificate C T_C ->
  forall pre post, hoare_valid pre C post -> hoare_derivable pre C post.
Proof.
  intros Hcert pre post Hvalid.
  eapply derive_pre; [| exact (wp_derivable C T_C Hcert post)].
  intros ps Hps Hpre.
  apply (proj2 (wp_correct C T_C (certificate_correct _ _ Hcert) post ps Hps)).
  exact (Hvalid ps Hps Hpre).
Qed.

Theorem wp_characterizes_validity C T_C : expectation_transformer_correct C T_C ->
  forall pre post, hoare_valid pre C post <-> pformula_valid (PFImpl pre (wp C T_C post)).
Proof.
  intros Hcorrect pre post; split; intros H ps Hps Hpre.
  - apply (proj2 (wp_correct C T_C Hcorrect post ps Hps)); apply H; assumption.
  - apply (proj1 (wp_correct C T_C Hcorrect post ps Hps)); apply H; assumption.
Qed.
