(** Conditioning masks a construct by the guard in the incoming state.
    Integral binders may be renamed, but their incoming laws are unchanged. *)
From Stdlib Require Import Reals Lists.List Lia.
Require Import MeasureIntegration CPHL Soundness.StateFacts Soundness.BindingFacts
  Soundness.ConstructFacts.
Import ListNotations.

(** In the capture branch, the old binder occurs in the guard. Avoiding
    guard names therefore also makes the fresh binder distinct from it. *)
Lemma conditioning_fresh_spec d q gamma :
  let z := fresh_real_program_var
    (pconstruct_real_program_vars q ++ distribution_real_program_vars d ++
      cformula_real_program_vars gamma) in
  ~ In z (pconstruct_real_program_vars q) /\
  ~ In z (distribution_real_program_vars d) /\
  ~ In z (cformula_real_program_vars gamma).
Proof.
  cbn zeta; pose proof (fresh_real_program_var_not_in
    (pconstruct_real_program_vars q ++ distribution_real_program_vars d ++
      cformula_real_program_vars gamma)) as H.
  repeat rewrite in_app_iff in H; tauto.
Qed.

(** Size preservation justifies recursion after renaming. The public
    wrapper supplies enough fuel to avoid the zero-fuel fallback. *)
Lemma condition_pconstruct_fuel_size fuel q gamma :
  pconstruct_size (condition_pconstruct_fuel fuel q gamma) = pconstruct_size q.
Proof.
  revert q; induction fuel as [|fuel IH]; intro q; [reflexivity|].
  destruct q as [beta | x d q]; cbn [condition_pconstruct_fuel pconstruct_size].
  - reflexivity.
  - destruct (in_dec real_program_var_eq_dec x (cformula_real_program_vars gamma));
      cbn [pconstruct_size]; rewrite IH; try rewrite rename_bound_pconstruct_size;
      reflexivity.
Qed.

Lemma condition_pconstruct_sufficient fuel q gamma :
  (pconstruct_size q <= fuel)%nat ->
  condition_pconstruct_fuel fuel q gamma = condition_pconstruct q gamma.
Proof.
  intro H; unfold condition_pconstruct.
  apply condition_pconstruct_fuel_stable; lia.
Qed.

Lemma guard_indicator_update_real_fresh gamma v x z :
  ~ In x (cformula_real_program_vars gamma) ->
  real_indicator (satisfies (update_real v x z) gamma) =
  real_indicator (satisfies v gamma).
Proof.
  intro H; apply real_indicator_extensional.
  apply satisfies_update_real_fresh; exact H.
Qed.

(** Renaming protects the guard while preserving the sampled body's value.
    The resulting constant factor leaves the integral by bounded integrability,
    including when the incoming distribution has invalid parameters. *)
Lemma condition_pconstruct_fuel_correct fuel q gamma v :
  (pconstruct_size q <= fuel)%nat ->
  q_eval (condition_pconstruct_fuel fuel q gamma) v =
  (real_indicator (satisfies v gamma) * q_eval q v)%R.
Proof.
  revert q v; induction fuel as [|fuel IH]; intros q v Hfuel;
    destruct q as [beta | x d q]; cbn [pconstruct_size] in Hfuel; try lia.
  - cbn [condition_pconstruct_fuel q_eval].
    (** Transfer the syntax indicator to the existing analytical interface. *)
    rewrite !formula_indicatorE.
    destruct (cformula_satisfies_dec gamma v) as [Hg | Hg].
    + rewrite (real_indicator_true _ Hg), Rmult_1_l.
      apply real_indicator_extensional; cbn [c_and c_not satisfies].
      (** Deciding the leaf removes the double negation in c_and. *)
      destruct (cformula_satisfies_dec beta v); tauto.
    + rewrite (real_indicator_false _ Hg), Rmult_0_l.
      apply real_indicator_false; cbn [c_and c_not satisfies]; tauto.
  - cbn [condition_pconstruct_fuel].
    destruct (in_dec real_program_var_eq_dec x (cformula_real_program_vars gamma))
      as [Hcapture | Hsafe].
    + pose proof (conditioning_fresh_spec d q gamma) as Hfresh; cbn zeta in Hfresh.
      cbn [q_eval].
      transitivity (@ConcreteMeasure.expectation _ RealIntegration.Space (distribution_measure d v)
        (fun z => (real_indicator (satisfies v gamma) *
          q_eval q (update_real v x z))%R)).
      * apply ConcreteMeasure.expectation_ext; intro z.
        rewrite IH by (rewrite rename_bound_pconstruct_size; lia).
        rewrite guard_indicator_update_real_fresh by tauto.
        rewrite rename_bound_pconstruct_eval by intuition congruence.
        reflexivity.
      * apply ConcreteMeasure.expectation_scale; apply q_integral_integrable.
    + cbn [q_eval].
      transitivity (@ConcreteMeasure.expectation _ RealIntegration.Space (distribution_measure d v)
        (fun z => (real_indicator (satisfies v gamma) *
          q_eval q (update_real v x z))%R)).
      * apply ConcreteMeasure.expectation_ext; intro z.
        rewrite IH by lia.
        rewrite guard_indicator_update_real_fresh by exact Hsafe.
        reflexivity.
      * apply ConcreteMeasure.expectation_scale; apply q_integral_integrable.
Qed.

Theorem condition_pconstruct_correct q gamma v :
  q_eval (condition_pconstruct q gamma) v =
  (real_indicator (satisfies v gamma) * q_eval q v)%R.
Proof.
  unfold condition_pconstruct; apply condition_pconstruct_fuel_correct; lia.
Qed.

(** Complementary guards split a reward pointwise. This statement is about
    constructs; arbitrary assertions need not distribute over a partition. *)
Lemma condition_pconstruct_partition q gamma v :
  q_eval q v = (q_eval (condition_pconstruct q gamma) v +
    q_eval (condition_pconstruct q (c_not gamma)) v)%R.
Proof.
  rewrite !condition_pconstruct_correct; cbn [c_not satisfies].
  destruct (cformula_satisfies_dec gamma v) as [Hg | Hg].
  - rewrite (real_indicator_true _ Hg), real_indicator_false by tauto.
    ring.
  - rewrite (real_indicator_false _ Hg), real_indicator_true by tauto.
    ring.
Qed.
