(** Increasing limits of input measures. Order and convergence concern
    measurable events; arbitrary nonnegative measures, including infinite
    ones, are permitted in these analytical lemmas. *)
From Stdlib Require Import Reals.
From mathcomp Require Import boot order ssralg ssrnum interval_inference finmap.
From mathcomp Require Import boolp classical_sets functions reals topology fsbigop.
From mathcomp Require Import ereal normedtype sequences esum measure numfun.
From mathcomp Require Import measurable_realfun simple_functions lebesgue_integral.
From mathcomp Require Import lebesgue_stieltjes_measure Rstruct Rstruct_topology.
Require Import MeasureIntegration.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports MeasurableR HBNNSimple.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Module MeasureContinuity.
Section Space.
Context {d} {T : measurableType d}.
Local Notation measure := (@ConcreteMeasure.measure d T).

(** These predicates identify the exact topology used below: setwise
    convergence on measurable events, rather than weak convergence. *)
Definition below (mu nu : measure) := forall A, measurable A -> mu A <= nu A.
Definition increasing (mus : nat -> measure) :=
  forall m n, (m <= n)%N -> below (mus m) (mus n).
Definition converges (mus : nat -> measure) (mu : measure) :=
  forall A, measurable A -> (fun n => mus n A) @ \oo --> mu A.

Lemma integral_monotone mu nu f : below mu nu ->
  (forall v, 0 <= f v) -> measurable_fun [set: T] f ->
  \int[mu]_v f v <= \int[nu]_v f v.
Proof. move=> h f0 mf; exact: ge0_le_measure_integral. Qed.

(** A simple function has a finite range. Setwise convergence passes through
    its finite sum of weighted event masses, even when some masses are infinite. *)
Lemma simple_integral_cvg mus mu (h : {nnsfun T >-> real}) : converges mus mu ->
  (fun n => sintegral (mus n) h) @ \oo --> sintegral mu h.
Proof.
move=> hc; rewrite sintegralE fsbig_finite//=.
under eq_fun do rewrite sintegralE fsbig_finite//=.
apply: cvg_nnesum => [r _|r _].
- apply: nearW => n; exact: nnsfun_mulemu_ge0.
- apply: cvgeZl => //; by apply: hc.
Qed.

Lemma below_limit mus mu : increasing mus -> converges mus mu ->
  forall n, below (mus n) mu.
Proof.
move=> hi hc n A mA.
apply: cvge_ge (hc A mA).
near=> m; apply: hi mA.
by near: m; exists n => // m; exact.
Unshelve. all: by end_near. Qed.

(** Nonnegative integration is the supremum of simple integrals. Each simple
    lower bound converges; monotonicity bounds the other direction. This proves
    continuity without assuming densities or integrability of the reward. *)
Lemma integral_increasing_cvg mus mu f : increasing mus -> converges mus mu ->
  (forall v, 0 <= f v) -> measurable_fun [set: T] f ->
  (fun n => \int[mus n]_v f v) @ \oo --> \int[mu]_v f v.
Proof.
move=> hi hc f0 mf.
have hiI : nondecreasing_seq (fun n => \int[mus n]_v f v).
  move=> m n hmn; apply: integral_monotone => //; exact: hi hmn.
have hI := ereal_nondecreasing_cvgn hiI.
have he : ereal_sup (range (fun n => \int[mus n]_v f v)) = \int[mu]_v f v.
  apply/eqP; rewrite eq_le; apply/andP; split.
  - apply: ge_ereal_sup => _ [n _ <-].
    apply: integral_monotone => //; exact: (@below_limit mus mu hi hc n).
  - rewrite ge0_integralTE//; apply: ge_ereal_sup => _ [h hf <-].
    apply (lee_cvg_to (@simple_integral_cvg mus mu h hc) hI).
    apply: nearW => n.
    have hs : \int[mus n]_v (h v)%:E = sintegral (mus n) h.
      by rewrite integral_nnsfun// patch_setT.
    rewrite -hs.
    apply: ge0_le_integral => //.
    + by move=> v _; rewrite lee_fin; exact: fun_ge0.
    + exact/measurable_EFinP.
by rewrite -he.
Qed.

(** Admissibility is closed under these limits; the proof is separate from
    the measure carrier and uses convergence only at the whole space. *)
Lemma subprob_limit mus mu : converges mus mu ->
  (forall n, ConcreteMeasure.Subprob (mus n)) -> ConcreteMeasure.Subprob mu.
Proof.
move=> hc hm; apply (cvge_to_le (hc setT measurableT)).
by apply: nearW => n; exact: hm.
Qed.
End Space.
End MeasureContinuity.
