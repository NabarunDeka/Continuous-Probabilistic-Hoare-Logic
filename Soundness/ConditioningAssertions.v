(** Assertion conditioning denotes unnormalized restriction of the joint
    measure. External probabilistic assignments are retained, even at mass zero. *)
From Stdlib Require Import Reals Lra.
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals topology ereal measure.
From mathcomp Require Import numfun measurable_realfun lebesgue_integral.
From mathcomp Require Import lebesgue_stieltjes_measure Rstruct Rstruct_topology.
Require Import MeasureIntegration CPHL Soundness.ConstructFacts Soundness.Conditioning.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports MeasurableR ValuationSpace.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Prove restriction in nonnegative extended integrals before projecting
    to reals. This identity itself needs no finite-mass assumption. *)
Lemma q_expectation_restrict (mu : Measure) gamma q :
  expectation (ConcreteMeasure.restrict mu (measurable_formula_event gamma)) (q_eval q) =
  expectation mu (fun v => (real_indicator (satisfies v gamma) * q_eval q v)%R).
Proof.
  unfold expectation, ConcreteMeasure.expectation, Rintegral.
  f_equal.
  transitivity (ConcreteMeasure.integral mu
    ((fun v => (q_eval q v)%:E) \_ (formula_event gamma))).
  - apply ConcreteMeasure.integral_restrict.
    + apply/measurable_EFinP; exact: q_eval_measurable.
    + intro v; rewrite lee_fin; exact: q_eval_nonnegative.
  - apply eq_integral => v _; rewrite /patch.
    case: ifP => hv.
    + have Hg : satisfies v gamma by exact/set_mem.
      by rewrite (real_indicator_true _ Hg) mul1r.
    + have Hg : ~ satisfies v gamma.
      { move=> Hg; have Hin : v \in formula_event gamma by exact/mem_set.
        by rewrite Hin in hv. }
      by rewrite (real_indicator_false _ Hg) mul0r.
Qed.

Lemma condition_expectation_correct q gamma mu :
  expectation mu (q_eval (condition_pconstruct q gamma)) =
  expectation (ConcreteMeasure.restrict mu (measurable_formula_event gamma)) (q_eval q).
Proof.
  rewrite q_expectation_restrict.
  apply ConcreteMeasure.expectation_ext; intro v; apply condition_pconstruct_correct.
Qed.

Definition condition_state gamma (ps : Pstate) : Pstate :=
  {| pstate_measure := ConcreteMeasure.restrict (pstate_measure ps)
       (measurable_formula_event gamma);
     pstate_prob_logic_values := pstate_prob_logic_values ps |}.

Lemma condition_state_admissible gamma ps : pstate_admissible ps ->
  pstate_admissible (condition_state gamma ps).
Proof. exact: ConcreteMeasure.restrict_subprob. Qed.

Lemma condition_state_external gamma ps :
  pstate_prob_logic_values (condition_state gamma ps) = pstate_prob_logic_values ps.
Proof. reflexivity. Qed.

(** Restriction filters valuations; it never updates program or logic
    coordinates. These equations expose the event and total-mass interfaces. *)
Lemma condition_state_event gamma ps A :
  pstate_measure (condition_state gamma ps) A =
  pstate_measure ps (A `&` formula_event gamma).
Proof. reflexivity. Qed.

Lemma restriction_formula_mass (mu : Measure) gamma :
  measure_of (ConcreteMeasure.restrict mu (measurable_formula_event gamma))
    (fun _ => True) = measure_of mu (formula_event gamma).
Proof.
  by rewrite /measure_of /ConcreteMeasure.event_mass /ConcreteMeasure.restrict /= /mrestr setTI.
Qed.

(** Equality of whole term values handles multiplication. Formula lifting
    includes implication and false; it imposes no linearity on assertions. *)
Lemma condition_pterm_correct p gamma ps :
  pterm_eval (condition_pterm p gamma) ps = pterm_eval p (condition_state gamma ps).
Proof.
  induction p; cbn [condition_pterm pterm_eval condition_state
    pstate_measure pstate_prob_logic_values].
  - reflexivity.
  - reflexivity.
  - apply condition_expectation_correct.
  - now rewrite IHp1 IHp2.
  - now rewrite IHp1 IHp2.
Qed.

Theorem condition_pformula_correct eta gamma ps :
  psatisfies ps (condition_pformula eta gamma) <->
  psatisfies (condition_state gamma ps) eta.
Proof.
  induction eta; cbn [condition_pformula psatisfies].
  - now rewrite !condition_pterm_correct.
  - tauto.
  - tauto.
Qed.

(** The complementary-guard identity can be integrated on admissible
    inputs because both conditioned constructs are bounded and integrable. *)
Lemma condition_expectation_partition q gamma mu : Subprob mu ->
  expectation mu (q_eval q) =
  (expectation mu (q_eval (condition_pconstruct q gamma)) +
   expectation mu (q_eval (condition_pconstruct q (c_not gamma))))%R.
Proof.
  intro Hmu.
  transitivity (expectation mu (fun v =>
    (q_eval (condition_pconstruct q gamma) v +
     q_eval (condition_pconstruct q (c_not gamma)) v)%R)).
  - apply ConcreteMeasure.expectation_ext; intro v; apply condition_pconstruct_partition.
  - apply ConcreteMeasure.expectation_add; apply q_expectation_integrable; exact Hmu.
Qed.

(** A null guard annihilates every conditioned construct. The input bound
    makes the restricted expectation finite, so its real mass bound applies. *)
Lemma condition_expectation_null q gamma mu : Subprob mu ->
  measure_of mu (formula_event gamma) = 0%R ->
  expectation mu (q_eval (condition_pconstruct q gamma)) = 0%R.
Proof.
  intros Hmu Hnull; rewrite condition_expectation_correct.
  have Hr : Subprob (ConcreteMeasure.restrict mu (measurable_formula_event gamma)).
  { exact: ConcreteMeasure.restrict_subprob Hmu. }
  have /andP [/RleP H0 _] := q_expectation_bounds q Hr.
  have /RleP H1 := q_expectation_mass_bound q Hr.
  rewrite restriction_formula_mass Hnull in H1.
  apply Rle_antisym; assumption.
Qed.
