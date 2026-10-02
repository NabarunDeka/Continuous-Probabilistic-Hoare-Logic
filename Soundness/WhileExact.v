(** Exact while soundness follows from the two one-sided rules. The bridges
    below keep all three rules' assertion and certificate contracts explicit. *)
From Stdlib Require Import Reals Lra.
Require Import MeasureIntegration CPHL Soundness.ConstructFacts
  Soundness.AssertionLogic Soundness.FiniteExpectationBounds
  Soundness.WhileUpper Soundness.WhileLower.

Import CommandSemantics.
Local Open Scope R_scope.

(** Exact regional masses and exit reward are precisely the conjunction
    of their upper and lower bounds, including a vacuous finite region list. *)
Lemma while_body_post_bounds m regions transitions g q exit ps :
  psatisfies ps (while_body_post m regions transitions g q exit) <->
  psatisfies ps (while_body_post_upper m regions transitions g q exit) /\
  psatisfies ps (while_body_post_lower m regions transitions g q exit).
Proof.
  unfold while_body_post, while_body_post_upper, while_body_post_lower.
  rewrite !psatisfies_and, !psatisfies_finite_p_and.
  split.
  - intros [ht he]; apply psatisfies_eq in he.
    split; split.
    + intros j hj; specialize (ht j hj); apply psatisfies_eq in ht.
      cbn [psatisfies]; lra.
    + cbn [psatisfies]; lra.
    + intros j hj; specialize (ht j hj); apply psatisfies_eq in ht.
      cbn [psatisfies]; lra.
    + cbn [psatisfies]; lra.
  - intros [ [htu heu] [htl hel] ]; split.
    + intros j hj; apply psatisfies_eq.
      specialize (htu j hj); specialize (htl j hj).
      cbn [psatisfies] in htu, htl; lra.
    + apply psatisfies_eq; cbn [psatisfies] in heu, hel; lra.
Qed.

(** An exact bounded fixed point supplies both inequality certificates.
    This is finite algebra only, without any assumption on empty rows. *)
Lemma while_solution_bounds m solution transitions exits :
  while_solution m solution transitions exits <->
  while_upper_solution m solution transitions exits /\
  while_lower_solution m solution transitions exits.
Proof.
  unfold while_solution, while_upper_solution, while_lower_solution.
  split.
  - intro hs; split; intros i hi; specialize (hs i hi); split; tauto || lra.
  - intros [hu hl] i hi; specialize (hu i hi); specialize (hl i hi).
    split; tauto || lra.
Qed.

(** The two mass bounds together give the exact mass precondition. No
    positivity is assumed: the shared concentration assertion admits zero. *)
Lemma concentrated_mass_bounds gamma mass ps :
  psatisfies ps (p_concentrated_mass gamma mass) <->
  psatisfies ps (p_concentrated_mass_upper gamma mass) /\
  psatisfies ps (p_concentrated_mass_lower gamma mass).
Proof.
  unfold p_concentrated_mass, p_concentrated_mass_upper, p_concentrated_mass_lower.
  fold (p_almost_sure gamma).
  rewrite !psatisfies_and, psatisfies_eq.
  cbn [psatisfies]; split; intros; intuition lra.
Qed.

(** The upper rule requires initial guard support. Guard containment makes
    gamma and (g and gamma) equivalent pointwise, hence on any input measure. *)
Lemma concentrated_mass_guard_upper gamma g mass ps :
  cformula_valid (FImpl gamma g) ->
  psatisfies ps (p_concentrated_mass gamma mass) ->
  psatisfies ps (p_concentrated_mass_upper (c_and g gamma) mass).
Proof.
  intros hg hpre.
  destruct (proj1 (concentrated_mass_bounds gamma mass ps) hpre) as [hu _].
  unfold p_concentrated_mass_upper in *; rewrite psatisfies_and in *.
  destruct hu as [hreg hm]; split; [|exact hm].
  apply psatisfies_almost_sure; apply psatisfies_almost_sure in hreg.
  transitivity (expectation (pstate_measure ps) (q_eval (QIndicator gamma))); [|exact hreg].
  apply ConcreteMeasure.expectation_ext; intro v.
  rewrite !q_eval_indicatorE; apply real_indicator_extensional.
  specialize (hg v); cbn [c_and c_not satisfies] in *.
  (** Guard containment plus formula decidability justifies the double negation. *)
  destruct (cformula_satisfies_dec gamma v); tauto.
Qed.

(** This is HWhile with semantic validity for its recursive body premises.
    Upper and lower bounds refer to the same output measure and unchanged
    external assignment; antisymmetry recovers the declared equality. *)
Theorem hoare_valid_while m k g body q regions solution transitions exits y :
  Nat.lt k m -> while_regions_cover m g regions ->
  while_regions_in_guard m g regions -> while_regions_disjoint m regions ->
  while_progress m transitions exits ->
  (forall i, Nat.lt i m -> hoare_valid
    (p_concentrated_mass (regions i) (PConst R1)) body
    (while_body_post m regions (transitions i) g q (exits i))) ->
  while_solution m solution transitions exits ->
  hoare_valid (p_concentrated_mass (regions k) (PVar y)) (CWhile g body)
    (p_eq (PExpect (condition_pconstruct q (c_not g)))
      (PMul (PConst (solution k)) (PVar y))).
Proof.
  intros hk hc hg hd hp hb hs ps hps hpre.
  destruct (proj1 (while_solution_bounds m solution transitions exits) hs) as [hsu hsl].
  assert (hbu : forall i, Nat.lt i m -> hoare_valid
    (p_concentrated_mass (regions i) (PConst R1)) body
    (while_body_post_upper m regions (transitions i) g q (exits i))).
  { intros i hi qs hqs hqpre.
    exact (proj1 (proj1 (while_body_post_bounds _ _ _ _ _ _ _) (hb i hi qs hqs hqpre))). }
  assert (hbl : forall i, Nat.lt i m -> hoare_valid
    (p_concentrated_mass (regions i) (PConst R1)) body
    (while_body_post_lower m regions (transitions i) g q (exits i))).
  { intros i hi qs hqs hqpre.
    exact (proj2 (proj1 (while_body_post_bounds _ _ _ _ _ _ _) (hb i hi qs hqs hqpre))). }
  pose proof (hoare_valid_while_upper m k g body q regions solution transitions exits y
    hk hc hbu hsu ps hps
    (concentrated_mass_guard_upper _ _ _ _ (hg k hk) hpre)) as hu.
  pose proof (hoare_valid_while_lower m k g body q regions solution transitions exits y
    hk hg hd hp hbl hsl ps hps
    (proj2 (proj1 (concentrated_mass_bounds _ _ _) hpre))) as hl.
  apply psatisfies_eq; cbn [psatisfies] in hu, hl; lra.
Qed.
