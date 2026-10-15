(**
  CdfLibraryFacts.v -- the few MathComp-level facts behind CdfAssertions.v.

  Kept separate so that CdfAssertions.v (and the examples importing it) do
  not activate SSReflect's [rewrite], which the Stdlib-style proofs avoid.
*)

From Stdlib Require Import Reals Lra.
From mathcomp Require Import boot order ssralg ssrnum interval interval_inference.
From mathcomp Require Import boolp classical_sets functions reals topology.
From mathcomp Require Import ereal normedtype measure numfun measurable_realfun.
From mathcomp Require Import lebesgue_measure lebesgue_integral.
From mathcomp Require Import Rstruct Rstruct_topology.
Require Import MeasureIntegration CPHL.
Require Import CPHLFacts.ConstructFacts CPHLFacts.CalculationFacts.

(** * Library-level facts (MathComp proofs) *)

Section LibraryFacts.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports MeasurableR.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma real_integral_nonneg (f : R -> R) :
  (forall x, Rle 0 (f x)) -> Rle 0 (real_integral f).
Proof.
move=> h; rewrite /real_integral /ConcreteMeasure.expectation /Rintegral.
apply/RleP; apply: fine_ge0; apply: integral_ge0 => x _.
by rewrite lee_fin; apply/RleP.
Qed.

Lemma real_measurable_atmost (a : R) :
  real_event_measurable (fun x => Rle x a).
Proof.
have -> : (fun x => Rle x a) = `]-oo, a]%classic.
  by rewrite predeqE => x; rewrite /= in_itv/=; split=> /RleP.
exact: measurable_itv.
Qed.

Lemma real_measurable_point (a : R) :
  real_event_measurable (fun x => x = a).
Proof. exact: measurable_set1. Qed.

(** The mass of any formula is at most the total mass. *)
Lemma pr_le_mass (mu : Measure) (gamma : CFormula) :
  Subprob mu ->
  Rle (expectation mu (q_eval (QIndicator gamma)))
      (expectation mu (q_eval (QIndicator c_true))).
Proof.
move=> h; rewrite !expectation_indicator; apply/RleP.
apply: ConcreteMeasure.event_monotone.
- exact: ConcreteMeasure.subprob_finite.
- exact: (ValuationSpace.measurable_formula_event gamma).
- exact: (ValuationSpace.measurable_formula_event c_true).
- by move=> v _; rewrite /formula_assertion /= => -[].
Qed.

(** At a point mass, the expectation of a construct is its value there. *)
Lemma expect_point_q (v : state) (q : PConstruct) :
  expectation (ConcreteMeasure.point (v : ValuationSpace.Valuation)) (q_eval q) =
  q_eval q v.
Proof.
rewrite /expectation /ConcreteMeasure.expectation /Rintegral /ConcreteMeasure.point.
rewrite integral_dirac //=.
- apply/measurable_EFinP; exact: q_eval_measurable.
- by rewrite indicT mul1r.
Qed.

(** The unit point mass at [v], as a probabilistic state. *)
Definition point_pstate (v : state) : Pstate :=
  {| pstate_measure := ConcreteMeasure.point (v : ValuationSpace.Valuation);
     pstate_prob_logic_values := fun _ => 0%R |}.

Lemma point_admissible (v : state) : pstate_admissible (point_pstate v).
Proof. exact: ConcreteMeasure.point_subprob. Qed.

Lemma point_pstate_expect (v : state) (q : PConstruct) :
  expectation (pstate_measure (point_pstate v)) (q_eval q) = q_eval q v.
Proof. exact: expect_point_q. Qed.

End LibraryFacts.
