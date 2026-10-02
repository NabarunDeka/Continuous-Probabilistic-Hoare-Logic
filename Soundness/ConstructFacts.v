(** Probability constructs are measurable bounded rewards. Their real-valued
    expectations below are justified by finiteness, not by a default at infinity. *)
From Stdlib Require Import Reals Lra.
From mathcomp Require Import boot order ssralg ssrnum interval_inference.
From mathcomp Require Import boolp classical_sets functions reals topology.
From mathcomp Require Import ereal normedtype measure numfun measurable_realfun.
From mathcomp Require Import lebesgue_integral lebesgue_stieltjes_measure kernel.
From mathcomp Require Import Rstruct Rstruct_topology.
Require Import MeasureIntegration CPHL Soundness.StateSpace Soundness.DistributionFacts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports MeasurableR ValuationSpace DistributionSemantics.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** This conversion lemma applies both to each sampling law and to an input
    subprobability measure. The extended integral is proved finite first. *)
Lemma bounded_real_expectation d (T : measurableType d)
    (mu : {measure set T -> \bar real}) (f : T -> real) :
  ConcreteMeasure.Subprob mu -> measurable_fun setT f ->
  (forall v, (0 <= f v)%R) -> (forall v, (f v <= 1)%R) ->
  (0 <= ConcreteMeasure.expectation mu f <= 1)%R.
Proof.
move=> hm mf f0 f1.
have hi := ConcreteMeasure.bounded_integrable hm mf f0 f1.
have me : measurable_fun setT (EFin \o f) by exact/measurable_EFinP.
have e0 v : 0 <= (f v)%:E by rewrite lee_fin.
have e1 v : (f v)%:E <= 1 by rewrite lee_fin.
have [h0 h1] := ConcreteMeasure.bounded_integral hm me e0 e1.
apply/andP; split; rewrite -lee_fin ConcreteMeasure.expectationE//.
Qed.

(** Joint update measurability handles nested binders, including shadowing.
    Parameters are outside the binder and remain evaluated in the old state. *)
Lemma measurable_construct_update x (f : Valuation -> real) :
  measurable_fun setT f ->
  measurable_fun [set: Valuation * real]
    (fun p => f (update_real p.1 x p.2)).
Proof. move=> mf; exact: measurableT_comp mf (measurable_real_update x). Qed.

(** Induction proves measurability and both bounds together. The integral
    case uses joint kernel integration followed by the measurable real projection. *)
Lemma q_eval_spec q :
  @measurable_fun _ _ [the measurableType _ of Valuation]
    [the measurableType _ of (real : Type)] setT (q_eval q) /\
  forall v, (0 <= q_eval q v <= 1)%R.
Proof.
elim: q => [gamma|x d q IH].
- have qe : q_eval (QIndicator gamma) = (\1_(formula_event gamma) : Valuation -> real).
    by apply/funext => v; exact: IndicatorExpectation.q_indicatorE.
  rewrite qe; split; first exact: measurable_indic (measurable_formula_event gamma).
  by move=> v; rewrite indicE; case: (v \in formula_event gamma);
    rewrite /= ?lexx ?ler01.
- have [mq bounds] := IH.
  have mj := measurable_construct_update x mq.
  have ms v : @measurable_fun _ _ RealIntegration.Space RealIntegration.Space
      setT (fun z => q_eval q (update_real v x z)).
    exact: measurable_fun_pair2 mj.
  have q0 v : (0 <= q_eval q v)%R by have /andP [] := bounds v.
  have q1 v : (q_eval q v <= 1)%R by have /andP [] := bounds v.
  split.
  + change (measurable_fun [set: Valuation]
      (fun v => fine (\int[distribution_measure d v]_z
        (q_eval q (update_real v x z))%:E))).
    apply: measurableT_comp; first exact: fine_measurable.
    apply: (measurable_fun_integral_finite_kernel
      (fun p : Valuation * real => (q_eval q (update_real p.1 x p.2))%:E)
      (real_law d)).
    * by move=> p; rewrite lee_fin q0.
    * exact/measurable_EFinP.
  + move=> v; apply: bounded_real_expectation => //.
    exact: distribution_mass_subprob.
Qed.

Lemma q_eval_measurable q :
  @measurable_fun _ _ [the measurableType _ of Valuation]
    [the measurableType _ of (real : Type)] setT (q_eval q).
Proof. exact: (proj1 (q_eval_spec q)). Qed.

Lemma q_eval_bounds q v : (0 <= q_eval q v <= 1)%R.
Proof. exact: (proj2 (q_eval_spec q)). Qed.

Lemma q_eval_nonnegative q v : (0 <= q_eval q v)%R.
Proof. by have /andP [] := q_eval_bounds q v. Qed.

Lemma q_eval_le_one q v : (q_eval q v <= 1)%R.
Proof. by have /andP [] := q_eval_bounds q v. Qed.

(** Stdlib-facing bounds can be used without importing MathComp notation. *)
Lemma q_eval_bounds_real q v :
  Rle 0 (q_eval q v) /\ Rle (q_eval q v) 1.
Proof. by have /andP [/RleP h0 /RleP h1] := q_eval_bounds q v; split. Qed.

(** Every assertion expectation is integrable on admissible inputs. No bound
    is claimed for arbitrary arithmetic combinations of expectations or rho. *)
Lemma q_expectation_integrable (mu : Measure) q : Subprob mu ->
  expectation_integrable mu (q_eval q).
Proof.
move=> hm; exact: ConcreteMeasure.bounded_integrable hm
  (q_eval_measurable q) (q_eval_nonnegative q) (q_eval_le_one q).
Qed.

Lemma q_expectation_bounds (mu : Measure) q : Subprob mu ->
  (0 <= expectation mu (q_eval q) <= 1)%R.
Proof.
move=> hm; exact: bounded_real_expectation hm
  (q_eval_measurable q) (q_eval_nonnegative q) (q_eval_le_one q).
Qed.

Lemma q_expectation_extended (mu : Measure) q : Subprob mu ->
  (expectation mu (q_eval q))%:E = \int[mu]_v (q_eval q v)%:E.
Proof. move=> hm; exact: ConcreteMeasure.expectationE (q_expectation_integrable q hm). Qed.

(** The unnormalized bound is sharper than one: lost input mass is not
    restored when a construct is evaluated. This includes the zero measure. *)
Lemma q_expectation_mass_bound (mu : Measure) q : Subprob mu ->
  (expectation mu (q_eval q) <= measure_of mu (fun _ => True))%R.
Proof.
move=> hm; rewrite -lee_fin q_expectation_extended//.
rewrite /measure_of
  (ConcreteMeasure.event_massE (ConcreteMeasure.subprob_finite hm) measurableT).
rewrite -[leRHS]mul1e -integral_cst//.
apply: ge0_le_integral => //.
- by move=> v _; rewrite lee_fin q_eval_nonnegative.
- apply/measurable_EFinP; exact: q_eval_measurable q.
- by move=> v _; rewrite lee_fin q_eval_le_one.
Qed.

Lemma q_integral_integrable x d q v :
  ConcreteMeasure.Integrable (distribution_measure d v)
    (fun z => q_eval q (update_real v x z)).
Proof.
apply: ConcreteMeasure.bounded_integrable.
- exact: distribution_mass_subprob.
- exact: measurable_fun_pair2 (measurable_construct_update x (q_eval_measurable q)).
- by move=> z; exact: q_eval_nonnegative.
- by move=> z; exact: q_eval_le_one.
Qed.

Lemma q_integral_extended x d q v :
  (q_eval (QIntegral x d q) v)%:E =
  \int[distribution_measure d v]_z (q_eval q (update_real v x z))%:E.
Proof. exact: ConcreteMeasure.expectationE (q_integral_integrable x d q v). Qed.

(** Kernel identity with a constant true body records the actual mass of
    the sampling law, including its zero-mass invalid branch. *)
Lemma q_integral_true x d v :
  q_eval (QIntegral x d (QIndicator c_true)) v =
  if distribution_validb d v then 1%R else 0%R.
Proof.
change (ConcreteMeasure.expectation (distribution_measure d v)
  (fun z => formula_indicator c_true (update_real v x z)) =
  if distribution_validb d v then 1%R else 0%R).
transitivity (ConcreteMeasure.expectation (distribution_measure d v) (fun _ => 1%R)).
- apply: ConcreteMeasure.expectation_ext => z.
  apply formula_indicator_true; by [].
- rewrite ConcreteMeasure.expectation_constant /ConcreteMeasure.event_mass.
  rewrite /distribution_measure real_law_mass /distribution_validb.
  by case: (validb d v); rewrite mul1r.
Qed.

Lemma q_expectation_zero q : expectation ConcreteMeasure.zero (q_eval q) = 0%R.
Proof.
change (fine (\int[(mzero : Measure)]_v (q_eval q v)%:E) = 0%R).
by rewrite integral_measure_zero.
Qed.

Lemma q_expectation_point q (v : Valuation) :
  expectation (ConcreteMeasure.point v) (q_eval q) = q_eval q v.
Proof.
change (fine (\int[dirac v]_w (q_eval q w)%:E) = q_eval q v).
rewrite integral_dirac ?diracT ?mul1e//.
apply/measurable_EFinP; exact: q_eval_measurable q.
Qed.

(** Weighted points may correlate program and classical coordinates. This
    finite-mixture identity holds even before imposing a total mass budget. *)
Lemma q_expectation_mixture q (v w : Valuation) (c e : {nonneg real}) :
  expectation (ConcreteMeasure.add
    (ConcreteMeasure.scale c (ConcreteMeasure.point v))
    (ConcreteMeasure.scale e (ConcreteMeasure.point w))) (q_eval q) =
  (c%:num * q_eval q v + e%:num * q_eval q w)%R.
Proof.
have mf : measurable_fun [set: Valuation] (fun v => (q_eval q v)%:E).
  apply/measurable_EFinP; exact: q_eval_measurable q.
have f0 u : 0 <= (q_eval q u)%:E by rewrite lee_fin q_eval_nonnegative.
change (fine (\int[measure_add (mscale c (dirac v)) (mscale e (dirac w))]_u
  (q_eval q u)%:E) = (c%:num * q_eval q v + e%:num * q_eval q w)%R).
by rewrite ge0_integral_measure_add// !ge0_integral_mscale//
  !integral_dirac// !diracT !mul1e -!EFinM -EFinD.
Qed.

(** A parameter mentioning the bound name still reads the old value. *)
Example integral_incoming_parameter x v :
  (real_program_values v x < 1)%R ->
  q_eval (QIntegral x (CPHL.Uniform (TProgVar x) (TConst 1%R))
    (QIndicator c_true)) v = 1%R.
Proof. move=> h; by rewrite q_integral_true /distribution_validb /validb /= h. Qed.

(** Nested shadowing does not bypass invalid-parameter handling: the inner
    equal-endpoint law is zero for every value installed by the outer binder. *)
Example nested_invalid_integral x d q v :
  q_eval (QIntegral x d (QIntegral x
    (CPHL.Uniform (TProgVar x) (TProgVar x)) q)) v = 0%R.
Proof.
change (ConcreteMeasure.expectation (distribution_measure d v)
  (fun z => q_eval (QIntegral x
    (CPHL.Uniform (TProgVar x) (TProgVar x)) q) (update_real v x z)) = 0%R).
transitivity (ConcreteMeasure.expectation (distribution_measure d v) (fun _ => 0%R)).
- apply: ConcreteMeasure.expectation_ext => z; apply: q_integral_invalid.
  by move=> /RltP; rewrite ltxx.
- exact: ConcreteMeasure.expectation_zero.
Qed.
