(** Exact expectation certificates for deterministic atomic commands and
    all Boolean tosses. Real sampling is a later subtask. *)
From Stdlib Require Import Reals Lra.
From mathcomp Require Import ssreflect ssrbool Rstruct.
Require Import CPHL Soundness.AssertionLogic Soundness.StructuralRules
  Soundness.AtomicCommandFacts Soundness.RealSubstitutionAssertions
  Soundness.BoolSubstitutionAssertions Soundness.AssertionFacts
  Soundness.ConstructFacts Completeness.Interface Completeness.StructuralRules.

Definition skip_expectation_transformer (q : PConstruct) : Pterm := PExpect q.
Definition real_assign_expectation_transformer x t (q : PConstruct) : Pterm :=
  subst_real_pterm x t (PExpect q).
Definition bool_assign_expectation_transformer b beta (q : PConstruct) : Pterm :=
  subst_bool_pterm b beta (PExpect q).
Definition valid_toss_expectation_transformer b r (q : PConstruct) : Pterm :=
  toss_pterm b r (PExpect q).

Theorem skip_certificate :
  exact_expectation_certificate CSkip skip_expectation_transformer.
Proof.
  constructor.
  - intros q y; cbn [skip_expectation_transformer prob_logic_var_occurs_pterm]; tauto.
  - intros ps q Hps.
    change (pterm_eval (PExpect q) ps = pterm_eval (PExpect q) (CommandSemantics.run CSkip ps)).
    symmetry; apply pterm_eval_equiv; apply run_skip_equiv.
  - intros q y; apply HSkip.
Qed.

Theorem real_assign_certificate x t :
  exact_expectation_certificate (CRealAssign x t) (real_assign_expectation_transformer x t).
Proof.
  constructor.
  - intros q y; cbn [real_assign_expectation_transformer subst_real_pterm
      prob_logic_var_occurs_pterm]; tauto.
  - intros ps q Hps.
    change (pterm_eval (subst_real_pterm x t (PExpect q)) ps =
      pterm_eval (PExpect q) (CommandSemantics.run (CRealAssign x t) ps)).
    rewrite subst_real_pterm_correct.
    symmetry; apply pterm_eval_equiv; apply run_real_assign_equiv.
  - intros q y.
    change (hoare_derivable (subst_real_pformula x t (p_eq (PVar y) (PExpect q)))
      (CRealAssign x t) (p_eq (PVar y) (PExpect q))).
    apply HRealAssign.
Qed.

Theorem bool_assign_certificate b beta :
  exact_expectation_certificate (CBoolAssign b beta) (bool_assign_expectation_transformer b beta).
Proof.
  constructor.
  - intros q y; cbn [bool_assign_expectation_transformer subst_bool_pterm
      prob_logic_var_occurs_pterm]; tauto.
  - intros ps q Hps.
    change (pterm_eval (subst_bool_pterm b beta (PExpect q)) ps =
      pterm_eval (PExpect q) (CommandSemantics.run (CBoolAssign b beta) ps)).
    rewrite subst_bool_pterm_correct.
    symmetry; apply pterm_eval_equiv; apply run_bool_assign_equiv.
  - intros q y.
    change (hoare_derivable (subst_bool_pformula b beta (p_eq (PVar y) (PExpect q)))
      (CBoolAssign b beta) (p_eq (PVar y) (PExpect q))).
    apply HBoolAssign.
Qed.

(** The definition is syntactically meaningful for every r, but this exact
    certificate requires 0 <= r <= 1, including both endpoints. *)
Theorem valid_toss_certificate b r : coin_probability_valid r ->
  exact_expectation_certificate (CBoolToss b r) (valid_toss_expectation_transformer b r).
Proof.
  intro Hr; constructor.
  - intros q y; cbn [valid_toss_expectation_transformer toss_pterm
      prob_logic_var_occurs_pterm]; tauto.
  - intros ps q Hps.
    change (pterm_eval (toss_pterm b r (PExpect q)) ps =
      pterm_eval (PExpect q) (CommandSemantics.run (CBoolToss b r) ps)).
    apply toss_pterm_correct; assumption.
  - intros q y.
    change (hoare_derivable (toss_pformula b r (p_eq (PVar y) (PExpect q)))
      (CBoolToss b r) (p_eq (PVar y) (PExpect q))).
    apply HBoolToss; exact Hr.
Qed.

(** Zero total mass forces every construct expectation to vanish. This is
    an assertion implication on admissible states, independent of commands. *)
Lemma zero_mass_expectation q ps : pstate_admissible ps ->
  psatisfies ps (p_eq (PExpect (QIndicator c_true)) (PConst 0%R)) ->
  pterm_eval (PExpect q) ps = 0%R.
Proof.
  intros Hps Hmass; apply psatisfies_eq in Hmass.
  pose proof (pexpect_bounds q ps Hps) as [Hnonneg _].
  pose proof (elimT RleP (q_expectation_mass_bound q Hps)) as Hbound.
  assert (Htrue : measure_of (pstate_measure ps) (fun _ => True) =
    pterm_eval (PExpect (QIndicator c_true)) ps).
  { cbn [pterm_eval]; rewrite expectation_indicator.
    apply measure_extensional; intro v.
    unfold formula_assertion, c_true; cbn [satisfies]; tauto. }
  rewrite Htrue in Hbound; cbn [pterm_eval] in *; lra.
Qed.

Definition invalid_toss_expectation_transformer (_ : PConstruct) : Pterm := PConst 0%R.

Theorem invalid_toss_certificate b r : ~ coin_probability_valid r ->
  exact_expectation_certificate (CBoolToss b r) invalid_toss_expectation_transformer.
Proof.
  intro Hr; constructor.
  - intros q y; cbn [invalid_toss_expectation_transformer prob_logic_var_occurs_pterm]; tauto.
  - intros ps q Hps; symmetry; apply run_toss_invalid_expectation; assumption.
  - intros q y.
    eapply derive_pre with (pre' := p_and p_true (p_eq (PVar y) (PConst 0%R))).
    + intros ps Hps H; apply psatisfies_and; split; [apply psatisfies_true | exact H].
    + eapply derive_post.
      * apply derive_analytical_frame.
        -- cbn [p_eq p_and p_not pformula_analytical pterm_analytical]; tauto.
        -- apply HBoolTossInvalid; exact Hr.
      * intros ps Hps H; apply psatisfies_and in H.
        destruct H as [Hmass Hy]; apply psatisfies_eq in Hy.
        apply psatisfies_eq; rewrite (zero_mass_expectation q ps Hps Hmass); exact Hy.
Qed.

(** Classical selection agrees with the semantics, including invalid constants.
    This definition is not a computational decision procedure for real validity. *)
Definition toss_expectation_transformer b r : PConstruct -> Pterm :=
  if boolp.pselect (coin_probability_valid r)
  then valid_toss_expectation_transformer b r
  else invalid_toss_expectation_transformer.

Lemma toss_transformer_valid b r : coin_probability_valid r ->
  toss_expectation_transformer b r = valid_toss_expectation_transformer b r.
Proof. intro Hr; unfold toss_expectation_transformer; destruct (boolp.pselect _); [reflexivity | contradiction]. Qed.

Lemma toss_transformer_invalid b r : ~ coin_probability_valid r ->
  toss_expectation_transformer b r = invalid_toss_expectation_transformer.
Proof. intro Hr; unfold toss_expectation_transformer; destruct (boolp.pselect _); [contradiction | reflexivity]. Qed.

Theorem toss_certificate b r :
  exact_expectation_certificate (CBoolToss b r) (toss_expectation_transformer b r).
Proof.
  unfold toss_expectation_transformer; destruct (boolp.pselect _) as [Hr | Hr].
  - apply valid_toss_certificate; exact Hr.
  - apply invalid_toss_certificate; exact Hr.
Qed.
