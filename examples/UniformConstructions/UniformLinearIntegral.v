(** The first moment of Lebesgue measure on a bounded half-open interval,
    proved from the library's fundamental theorem of calculus. *)
From Stdlib Require Import Reals.
From mathcomp Require Import boot order ssralg ssrnum interval interval_inference.
From mathcomp Require Import boolp classical_sets functions reals topology.
From mathcomp Require Import ereal normedtype sequences derive realfun numfun.
From mathcomp Require Import measure measurable_realfun lebesgue_measure lebesgue_integral ftc.
From mathcomp Require Import Rstruct Rstruct_topology.
Require Import CPHL CPHLFacts.RealIntegrationFacts CPHLFacts.CalculationFacts.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports MeasurableR.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Module UniformLinear.
Local Notation mu := (@lebesgue_measure real).

Definition primitive (x : real) : real := (x * x / 2)%R.

Lemma continuous_primitive : continuous primitive.
Proof.
move=> x; rewrite /primitive.
apply: cvgM; last exact: cst_continuous.
by apply: cvgM; exact: id_continuous.
Qed.

Local Instance is_derive_primitive (x : real) : is_derive x 1%R primitive x.
Proof.
rewrite /primitive.
apply: is_derive_eq.
have sc (u v : real) : u *: v = (u * v)%R by [].
rewrite !sc mulr0 mulr0 add0r !mulr1 -mulr2n -(mulr_natl x 2) mulrA mulVf ?mul1r// pnatr_eq0.
Qed.

Lemma derive_primitive x : primitive^`() x = x.
Proof. by rewrite derive1E; apply: derive_val. Qed.

Lemma integral_between a b : (a <= b)%R ->
  \int[mu]_(x in `[a, b[) (x : real)%:E = ((b * b - a * a) / 2)%:E.
Proof.
move=> ab.
have [->|anb] := eqVneq a b.
  by rewrite set_itvco0 integral_set0 subrr mul0r.
have ablt : (a < b)%R by rewrite lt_neqAle anb ab.
rewrite integral_itvbo_itvbc.
  by apply/measurable_EFinP/measurable_funTS; exact: measurable_id.
rewrite (@continuous_FTC2 _ _ primitive a b ablt).
- exact: continuous_subspaceT id_continuous.
- split.
  + by move=> x _; rewrite /primitive; exact: ex_derive.
  + apply/cvg_at_right_filter; exact: continuous_primitive.
  + apply/cvg_at_left_filter; exact: continuous_primitive.
- by move=> x _; exact: derive_primitive.
- by rewrite /primitive -EFinB -mulrBl.
Qed.
End UniformLinear.

(** The Stdlib-real statement in CPHL's region vocabulary. *)
Lemma real_integral_between_linear_proved (a b : R) : Rle a b ->
  real_integral_between a b (fun x => x) =
    Rdiv (Rminus (Rmult b b) (Rmult a a)) 2.
Proof.
move=> hab.
rewrite /real_integral_between real_integral_mask /Rintegral.
have region : [set x : real | Rle a x /\ Rlt x b] = `[a, b[%classic.
  rewrite predeqE => x.
  change ((Rle a x /\ Rlt x b) <-> (x \in `[a, b[)).
  rewrite in_itv /=.
  split; first by move=> [/RleP ha /RltP hb]; apply/andP.
  by move=> /andP[/RleP ha /RltP hb]; split.
change ((fun x : real => Rle a x /\ Rlt x b) = `[a, b[%classic) in region.
rewrite region /RealIntegration.lebesgue.
rewrite UniformLinear.integral_between; first exact/RleP.
by rewrite /= RdivE RminusE !RmultE.
Qed.

(** Regularity facts used by the Stdlib-style uniform calculations. *)
Lemma real_measurable_atmost (b : R) :
  real_event_measurable (fun x => Rle x b).
Proof.
have -> : (fun x => Rle x b) = `]-oo, b]%classic.
  by rewrite predeqE => x; rewrite /= in_itv/=; split=> /RleP.
exact: measurable_itv.
Qed.

Lemma real_integrable_between_id (a b : R) :
  real_integrable (fun x => Rmult (real_indicator (Rle a x /\ Rlt x b)) x).
Proof. apply: real_integrable_between_continuous; exact: id_continuous. Qed.
