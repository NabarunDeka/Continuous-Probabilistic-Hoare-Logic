(** Real substitution evaluates its replacement in the incoming valuation.
    Integral parameters have that same scope; only the body is bound.
    This file proves pointwise identities, without assuming any Hoare rule. *)
From Stdlib Require Import Reals Lists.List Lia.
Require Import MeasureIntegration CPHL Soundness.StateFacts Soundness.BindingFacts.
Import ListNotations.

(** Substitution is a single update, including when t itself mentions x.
    Classical logic coordinates and Boolean coordinates remain unchanged. *)
Lemma subst_real_term_correct x t u v :
  term_eval (subst_real_term x t u) v =
  term_eval u (update_real v x (term_eval t v)).
Proof.
  induction u as [y | y | c | u1 IH1 u2 IH2 | u1 IH1 u2 IH2];
    cbn [subst_real_term term_eval].
  - destruct (real_program_var_eq_dec y x) as [-> | Hne]; cbn [term_eval].
    + symmetry; apply update_real_here.
    + symmetry; apply update_real_other; exact Hne.
  - reflexivity.
  - reflexivity.
  - now rewrite IH1, IH2.
  - now rewrite IH1, IH2.
Qed.

Lemma subst_real_cformula_correct x t gamma v :
  satisfies v (subst_real_cformula x t gamma) <->
  satisfies (update_real v x (term_eval t v)) gamma.
Proof.
  induction gamma as [b | b | u1 u2 | | g1 IH1 g2 IH2];
    cbn [subst_real_cformula satisfies]; try reflexivity.
  - now rewrite !subst_real_term_correct.
  - tauto.
Qed.

(** The whole sampling law agrees, including the zero law at invalid
    parameters. No state-independence or parameter-validity premise is needed. *)
Lemma subst_real_distribution_correct x t d v :
  distribution_measure (subst_real_distribution x t d) v =
  distribution_measure d (update_real v x (term_eval t v)).
Proof.
  destruct d as [a b | a b | a b];
    unfold distribution_measure, DistributionSemantics.real_law;
    cbn [subst_real_distribution]; rewrite !subst_real_term_correct; reflexivity.
Qed.

(** In a capture branch, the old binder occurs in t. Avoiding every name
    in t therefore also makes the new binder distinct from the old one. *)
Lemma real_substitution_fresh_spec x t d q :
  let z := fresh_real_program_var
    (pconstruct_real_program_vars q ++ distribution_real_program_vars d ++
      term_real_program_vars t ++ [x]) in
  z <> x /\ ~ In z (pconstruct_real_program_vars q) /\
  ~ In z (distribution_real_program_vars d) /\
  ~ In z (term_real_program_vars t).
Proof.
  cbn zeta.
  pose proof (fresh_real_program_var_not_in
    (pconstruct_real_program_vars q ++ distribution_real_program_vars d ++
      term_real_program_vars t ++ [x])) as H.
  repeat rewrite in_app_iff in H; cbn [In] in H; intuition congruence.
Qed.

(** Renaming preserves size, so the recursive call still fits the supplied
    fuel. The public wrapper never reaches the zero-fuel fallback. *)
Lemma subst_real_pconstruct_fuel_size fuel x t q :
  pconstruct_size (subst_real_pconstruct_fuel fuel x t q) = pconstruct_size q.
Proof.
  revert q; induction fuel as [|fuel IH]; intro q; [reflexivity|].
  destruct q as [gamma | a d q]; cbn [subst_real_pconstruct_fuel pconstruct_size].
  - reflexivity.
  - destruct (real_program_var_eq_dec a x); [reflexivity|].
    destruct (in_dec real_program_var_eq_dec a (term_real_program_vars t));
      cbn [pconstruct_size]; rewrite IH; try rewrite rename_bound_pconstruct_size;
      reflexivity.
Qed.

Lemma subst_real_pconstruct_sufficient fuel x t q :
  (pconstruct_size q <= fuel)%nat ->
  subst_real_pconstruct_fuel fuel x t q = subst_real_pconstruct x t q.
Proof.
  intro H; unfold subst_real_pconstruct.
  apply subst_real_pconstruct_fuel_stable; lia.
Qed.

(** The shadowing case substitutes the parameters but leaves the body alone.
    The capture case renames before substitution; the other case commutes
    distinct updates. All cases compare integrands under the same law. *)
Lemma subst_real_pconstruct_fuel_correct fuel x t q v :
  (pconstruct_size q <= fuel)%nat ->
  q_eval (subst_real_pconstruct_fuel fuel x t q) v =
  q_eval q (update_real v x (term_eval t v)).
Proof.
  (** The indicator bridge lets substitution reuse formula satisfaction. *)
  revert q v; induction fuel as [|fuel IH]; intros q v Hfuel;
    destruct q as [gamma | a d q]; cbn [pconstruct_size] in Hfuel; try lia.
  - cbn [subst_real_pconstruct_fuel q_eval]; rewrite !formula_indicatorE; apply real_indicator_extensional.
    apply subst_real_cformula_correct.
  - cbn [subst_real_pconstruct_fuel].
    destruct (real_program_var_eq_dec a x) as [-> | Hax].
    + cbn [q_eval]; rewrite subst_real_distribution_correct.
      apply ConcreteMeasure.expectation_ext; intro z; now rewrite update_real_shadow.
    + destruct (in_dec real_program_var_eq_dec a (term_real_program_vars t))
        as [Hcapture | Hsafe].
      * pose proof (real_substitution_fresh_spec x t d q) as Hfresh.
        cbn zeta in Hfresh.
        cbn [q_eval]; rewrite subst_real_distribution_correct.
        apply ConcreteMeasure.expectation_ext; intro z.
        rewrite IH by (rewrite rename_bound_pconstruct_size; lia).
        rewrite term_eval_update_real_fresh by tauto.
        rewrite update_real_commute by tauto.
        apply rename_bound_pconstruct_eval; intuition congruence.
      * cbn [q_eval]; rewrite subst_real_distribution_correct.
        apply ConcreteMeasure.expectation_ext; intro z.
        rewrite IH by lia.
        rewrite term_eval_update_real_fresh by exact Hsafe.
        now rewrite update_real_commute by exact Hax.
Qed.

Theorem subst_real_pconstruct_correct x t q v :
  q_eval (subst_real_pconstruct x t q) v =
  q_eval q (update_real v x (term_eval t v)).
Proof.
  unfold subst_real_pconstruct; apply subst_real_pconstruct_fuel_correct; lia.
Qed.
