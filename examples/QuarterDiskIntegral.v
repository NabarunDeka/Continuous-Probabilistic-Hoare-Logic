(** The unit-square quarter-disk area, proved from the library's fundamental
    theorem of calculus and integration by substitution (x = sin t).
    No example-specific analytical axioms are used. *)
From Stdlib Require Import Reals.
From mathcomp Require Import boot order ssralg ssrnum interval interval_inference.
From mathcomp Require Import boolp classical_sets functions reals topology.
From mathcomp Require Import ereal normedtype sequences derive realfun numfun.
From mathcomp Require Import measure measurable_realfun lebesgue_measure lebesgue_integral ftc.
From mathcomp Require Import trigonometry_functions.
From mathcomp Require Import Rstruct Rstruct_topology.
Require Import AnalysisPrelude CPHL CPHLFacts.RealIntegrationFacts.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports MeasurableR.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Module QuarterDisk.
Section Generic.
Context {R : realType}.
Local Open Scope ring_scope.
Local Notation mu := (@lebesgue_measure R).
Implicit Types x t : R.

(** A primitive of [cos^2]. *)
Definition primitive x : R := (x + sin x * cos x) / 2.

Local Instance is_derive_primitive x : is_derive x 1 primitive (cos x ^+ 2).
Proof.
rewrite /primitive.
apply: is_derive_eq.
rewrite !scaler0 add0r.
have sc (u v : R) : u *: v = u * v by [].
rewrite !sc mulrN -!expr2 sin2cos2 opprB addrA [(1 + _)]addrC subrK.
by rewrite -mulr2n -(mulr_natl (cos x ^+ 2) 2) mulrA mulVf ?mul1r// pnatr_eq0.
Qed.

Lemma derive_primitive x : primitive^`() x = cos x ^+ 2.
Proof. by rewrite derive1E; apply: derive_val. Qed.

Lemma continuous_primitive : continuous primitive.
Proof.
move=> x; apply: differentiable_continuous.
apply/derivable1_diffP; exact: ex_derive.
Qed.

Lemma derive_sin_cos : (@sin R)^`() = cos.
Proof. by apply/funext => x; rewrite derive1E; apply: derive_val. Qed.

Lemma continuous_cos2 : continuous (fun x : R => cos x ^+ 2).
Proof.
have -> : (fun x : R => cos x ^+ 2) = (fun x => cos x * cos x).
  by apply/funext => y; rewrite expr2.
move=> x; apply: cvgM; exact: continuous_cos.
Qed.

Lemma pihalf_gt0 : 0 < pi / 2 :> R.
Proof. by rewrite divr_gt0// pi_gt0. Qed.

(** [int_0^(pi/2) cos^2 = pi/4]. *)
Lemma integral_cos2 :
  (\int[mu]_(x in `[0%R, (pi / 2)%R]) (cos x ^+ 2)%:E = ((pi / 4)%R)%:E)%E.
Proof.
rewrite (@continuous_FTC2 _ _ primitive 0 (pi / 2)).
- exact: pihalf_gt0.
- exact: continuous_subspaceT continuous_cos2.
- split.
  + by move=> x _; exact: ex_derive.
  + apply/cvg_at_right_filter; exact: continuous_primitive.
  + apply/cvg_at_left_filter; exact: continuous_primitive.
- by move=> x _; exact: derive_primitive.
- rewrite -EFinB; congr EFin.
  rewrite /primitive sin_pihalf cos_pihalf sin0 cos0 mulr0 mul0r !addr0 mul0r subr0.
  by rewrite -mulrA -invfM -natrM.
Qed.

(** Substituting [x = sin t] on [[0, pi/2]]. *)
Lemma integral_sqrt_one_minus_sq :
  (\int[mu]_(x in `[0%R, 1%R]) (Num.sqrt (1 - x ^+ 2))%:E = ((pi / 4)%R)%:E)%E.
Proof.
have mem t : t \in `[0, pi / 2] -> t \in `[- (pi / 2), pi / 2].
  rewrite !in_itv/= => /andP[t0 ->]; rewrite andbT.
  by rewrite (le_trans _ t0)// oppr_le0 ltW// pihalf_gt0.
have H := @integration_by_substitution_increasing R (@sin R)
  (fun x => Num.sqrt (1 - x ^+ 2)) 0 (pi / 2).
rewrite sin0 sin_pihalf in H.
rewrite H.
- exact: ltW pihalf_gt0.
- move=> x y /mem xI /mem yI xy; by rewrite ltr_sin.
- by move=> x _; rewrite derive_sin_cos; exact: continuous_cos.
- rewrite derive_sin_cos; apply/cvg_ex; exists (cos 0).
  apply/cvg_at_right_filter; exact: continuous_cos.
- rewrite derive_sin_cos; apply/cvg_ex; exists (cos (pi / 2)).
  apply/cvg_at_left_filter; exact: continuous_cos.
- split.
  + by move=> x _; exact: ex_derive.
  + apply/cvg_at_right_filter; exact: continuous_sin.
  + apply/cvg_at_left_filter; exact: continuous_sin.
- apply: continuous_subspaceT => x.
  apply: continuous_comp; last exact: sqrt_continuous.
  apply: continuousB; first exact: cst_continuous.
  exact: exprn_continuous.
- rewrite -integral_cos2; apply: eq_integral => t.
  rewrite inE /= in_itv /= => /andP[t0 tpi].
  rewrite derive_sin_cos; congr EFin.
  change (Num.sqrt (1 - sin t ^+ 2) * cos t = cos t ^+ 2).
  have c0 : 0 <= cos t.
    apply: cos_ge0_pihalf.
    by rewrite tpi andbT (le_trans _ t0)// oppr_le0 ltW// pihalf_gt0.
  by rewrite -cos2sin2 sqrtr_sqr ger0_norm// expr2.
Qed.

End Generic.
End QuarterDisk.

(** The Stdlib-real statement used by the examples. *)
Lemma real_integral_sqrt_quarter :
  real_integral (fun x => Rmult (real_indicator (Rle 0 x /\ Rle x 1))
    (R_sqrt.sqrt (Rminus 1 (Rmult x x)))) = Rdiv PI 4.
Proof.
rewrite real_integral_mask /Rintegral.
have region : [set x : real | Rle 0 x /\ Rle x 1] = `[0%R, 1%R]%classic.
  rewrite predeqE => x.
  change ((Rle 0 x /\ Rle x 1) <-> (x \in `[0%R, 1%R])).
  rewrite in_itv /=.
  split; first by move=> [/RleP h0 /RleP h1]; apply/andP.
  by move=> /andP[/RleP h0 /RleP h1]; split.
change ((fun x : real => Rle 0 x /\ Rle x 1) = `[0%R, 1%R]%classic) in region.
rewrite region /RealIntegration.lebesgue.
under eq_integral do rewrite RsqrtE RminusE RmultE -expr2.
rewrite QuarterDisk.integral_sqrt_one_minus_sq /=.
by rewrite StandardReal.pi RdivE IZRposE INRE.
Qed.
