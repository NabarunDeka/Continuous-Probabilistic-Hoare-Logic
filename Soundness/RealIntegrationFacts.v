(** Library-backed interval and singleton calculations. Distribution-specific
    exponential and disk calculations do not belong to this foundation. *)
From Stdlib Require Import Reals FunctionalExtensionality.
From mathcomp Require Import boot order ssralg ssrnum interval interval_inference.
From mathcomp Require Import boolp classical_sets functions reals topology.
From mathcomp Require Import ereal numfun measure measurable_realfun.
From mathcomp Require Import lebesgue_measure lebesgue_integral.
From mathcomp Require Import lebesgue_stieltjes_measure Rstruct Rstruct_topology.
Require Import MeasureIntegration CPHL.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports MeasurableR.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Masking is an exact identity of total integrals; it does not need the
    false claim that every signed function is Lebesgue integrable. *)
Lemma real_integral_mask (A : set real) (f : real -> real) :
  real_integral (fun x => Rmult (real_indicator (A x)) (f x)) =
    Rintegral RealIntegration.lebesgue A f.
Proof.
rewrite /real_integral /ConcreteMeasure.expectation [RHS]Rintegral_mkcond.
apply: eq_Rintegral => x _; rewrite IndicatorExpectation.indicatorE indicE /patch.
by case: (x \in A); rewrite (Rmult_1_l, Rmult_0_l).
Qed.

Lemma real_integral_singleton_zero (a : R) (f : R -> R) :
  real_integral (fun x => Rmult (real_indicator (x = a)) (f x)) = 0%R.
Proof.
rewrite real_integral_mask /Rintegral.
by rewrite /RealIntegration.lebesgue integral_set1.
Qed.

(** Closed or open endpoints have the same Lebesgue mass. This statement
    keeps the library's interval representation for a small reusable bridge. *)
Lemma real_integral_interval (a b : real) (left right : bool) : (a <= b)%R ->
  real_integral (fun x => real_indicator (x \in Interval (BSide left a) (BSide right b))) =
    (b - a)%R.
Proof.
move=> hab.
transitivity (Rintegral RealIntegration.lebesgue
  [set` Interval (BSide left a) (BSide right b)] (fun _ => 1%R)).
- rewrite -real_integral_mask; apply: real_integral_extensional => x.
  by rewrite Rmult_1_r.
- rewrite Rintegral_cst ?measurable_itv// mul1r.
  change (fine (@lebesgue_measure real
    [set` Interval (BSide left a) (BSide right b)]) = (b - a)%R).
  rewrite lebesgue_measure_itv /= lte_fin.
  case: ltP => [hlt|hba]; first by rewrite -EFinB.
  have -> : b = a by apply/eqP; rewrite eq_le hba hab.
  by rewrite subrr.
Qed.

(** The public half-open notation uses Stdlib's propositional comparisons;
    reflection connects it to the Borel interval used by the library. *)
Lemma real_integral_between_one (a b : R) : Rle a b ->
  real_integral_between a b (fun _ => 1%R) = Rminus b a.
Proof.
move=> /RleP hab; rewrite /real_integral_between.
transitivity (real_integral (fun x => real_indicator (x \in `[a, b[))).
- apply: real_integral_extensional => x; rewrite Rmult_1_r.
  apply: real_indicator_extensional; rewrite in_itv /=.
  split => [ [/RleP ha /RltP hb] | /andP [/RleP ha /RltP hb] ].
  + by apply/andP.
  + by split.
- exact: real_integral_interval.
Qed.

Lemma real_integral_closed_between_one (a b : R) : Rle a b ->
  real_integral (fun x => real_indicator (Rle a x /\ Rle x b)) = Rminus b a.
Proof.
move=> /RleP hab.
transitivity (real_integral (fun x => real_indicator (x \in `[a, b]))).
- apply: real_integral_extensional => x.
  apply: real_indicator_extensional; rewrite in_itv /=.
  split => [ [/RleP ha /RleP hb] | /andP [/RleP ha /RleP hb] ].
  + by apply/andP.
  + by split.
- exact: real_integral_interval.
Qed.
