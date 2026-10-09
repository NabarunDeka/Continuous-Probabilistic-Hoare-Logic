(** Exponential region integrals, proved from the library's fundamental
    theorem of calculus. No example-specific analytical axioms are used. *)
From Stdlib Require Import Reals.
From mathcomp Require Import boot order ssralg ssrnum interval interval_inference.
From mathcomp Require Import boolp classical_sets functions reals topology.
From mathcomp Require Import ereal normedtype sequences exp derive realfun numfun.
From mathcomp Require Import measure measurable_realfun lebesgue_measure lebesgue_integral ftc.
From mathcomp Require Import Rstruct Rstruct_topology.
Require Import CPHL Soundness.RealIntegrationFacts.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports MeasurableR.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Module ExponentialRegions.
Local Notation mu := (@lebesgue_measure real).
Definition primitive (k x : real) := (expR (k * x) / k)%R.

Lemma continuous_exp_linear (k : real) : continuous (fun x : real => expR (k * x)).
Proof.
move=> x; apply: continuous_comp; last exact: continuous_expR.
by apply: continuousM; [exact: cst_continuous | exact: id_continuous].
Qed.

Lemma continuous_primitive k : continuous (primitive k : real^o -> real^o).
Proof.
rewrite /primitive. move=> x.
apply: cvgM.
- exact: continuous_exp_linear.
- exact: cst_continuous.
Qed.

Lemma derive_primitive k x : k != 0%R -> (primitive k)^`() x = expR (k * x).
Proof.
move=> k0; rewrite /primitive derive1Mr// derive1_comp// derive1E.
have /funeqP -> := @derive_expR real.
by rewrite derive1Ml// derive1_id mulr1 -mulrA divff// mulr1.
Qed.

Lemma integral_above a k : (k < 0)%R ->
  \int[mu]_(x in `[a, +oo[) (expR (k * x))%:E = (- expR (k * a) / k)%:E.
Proof.
move=> k0.
have kn0 : k != 0%R by exact: ltr0_neq0 k0.
have limexp : (fun x : real => expR (k * x)) x @[x --> +oo%R] --> 0%R.
  rewrite (_ : (fun x : real => expR (k * x)) =
    (fun z : real => expR (- z)) \o (fun z => - k * z)%R).
    by apply: eq_fun => x; rewrite /= mulNr opprK.
  apply: (@cvg_comp _ _ _ _ _ _ (pinfty_nbhs real)); last exact: cvgr_expR.
  have nk0 : (0 < - k)%R by rewrite oppr_gt0.
  apply: gt0_cvgMry => //; exact: cvg_id.
rewrite (@ge0_continuous_FTC2y _ _ (primitive k) a 0%R).
- by move=> x _; exact: expR_ge0.
- exact: continuous_subspaceT (continuous_exp_linear k).
- rewrite /primitive -[0%R](mul0r (k^-1)%R); exact: cvgM limexp (cvg_cst _).
- by move=> x _; rewrite /primitive; exact: ex_derive.
- apply/cvg_at_right_filter; exact: continuous_primitive.
- by move=> x _; exact: derive_primitive.
- by rewrite /primitive sub0e -EFinN mulNr.
Qed.

Lemma integral_below a k : (0 < k)%R ->
  \int[mu]_(x in `]-oo, a[) (expR (k * x))%:E = (expR (k * a) / k)%:E.
Proof.
move=> k0.
rewrite integral_itvbo_itvbc; first
  (apply/measurable_EFinP/measurable_funTS;
   apply: measurableT_comp; [exact: measurable_expR | exact: measurable_funM]).
rewrite -{1}(opprK a) ge0_integration_by_substitutionNy.
- exact: continuous_subspaceT (continuous_exp_linear k).
- by move=> x _; exact: expR_ge0.
- rewrite (eq_integral (fun x : real => (expR (- k * x))%:E)).
  + by move=> x _; rewrite /= mulrN mulNr.
  + rewrite integral_above ?oppr_lt0//.
    by rewrite !mulrNN invrN mulrNN.
Qed.

Lemma integral_between a b k : (a <= b)%R -> k != 0%R ->
  \int[mu]_(x in `[a, b[) (expR (k * x))%:E =
    ((expR (k * b) - expR (k * a)) / k)%:E.
Proof.
move=> ab k0.
have mf : measurable_fun setT (fun x : real => (expR (k * x))%:E).
  apply/measurable_EFinP; apply: measurableT_comp;
    [exact: measurable_expR | exact: measurable_funM].
have [->|anb] := eqVneq a b.
  by rewrite set_itvco0 integral_set0 subrr mul0r.
have ablt : (a < b)%R by rewrite lt_neqAle anb ab.
rewrite integral_itvbo_itvbc; first exact: measurable_funTS mf.
rewrite (@continuous_FTC2 _ _ (primitive k) a b ablt).
- exact: continuous_subspaceT (continuous_exp_linear k).
- split.
  + by move=> x _; rewrite /primitive; exact: ex_derive.
  + apply/cvg_at_right_filter; exact: continuous_primitive.
  + apply/cvg_at_left_filter; exact: continuous_primitive.
- by move=> x _; exact: derive_primitive.
- by rewrite /primitive -EFinB -mulrBl.
Qed.
End ExponentialRegions.

(** Bridges preserve the original Stdlib-real statements used by examples. *)
Lemma real_integral_exp_above_proved (a k : R) : Rlt k 0 ->
  real_integral_above a (fun x => exp (Rmult k x)) = Rdiv (Ropp (exp (Rmult k a))) k.
Proof.
move=> hk.
rewrite /real_integral_above real_integral_mask /Rintegral.
have region : [set x : real | Rle a x] = `[a, +oo[%classic.
  rewrite predeqE => x.
  change (Rle a x <-> (x \in `[a, +oo[)).
  rewrite in_itv /= andbT; by split => /RleP.
change (Rle a = `[a, +oo[%classic) in region.
rewrite region /RealIntegration.lebesgue.
under eq_integral do rewrite RexpE !RealsE.
rewrite ExponentialRegions.integral_above; first exact/RltP.
by rewrite RexpE !RealsE.
Qed.

Lemma real_integral_exp_below_proved (a k : R) : Rlt 0 k ->
  real_integral_below a (fun x => exp (Rmult k x)) = Rdiv (exp (Rmult k a)) k.
Proof.
move=> hk.
rewrite /real_integral_below real_integral_mask /Rintegral.
have region : [set x : real | Rlt x a] = `]-oo, a[%classic.
  rewrite predeqE => x.
  change (Rlt x a <-> (x \in `]-oo, a[)).
  rewrite in_itv /=; by split => /RltP.
change ((fun x : real => Rlt x a) = `]-oo, a[%classic) in region.
rewrite region /RealIntegration.lebesgue.
under eq_integral do rewrite RexpE !RealsE.
rewrite ExponentialRegions.integral_below; first exact/RltP.
by rewrite RexpE !RealsE.
Qed.

Lemma real_integral_exp_between_proved (a b k : R) : Rle a b -> k <> 0%R ->
  real_integral_between a b (fun x => exp (Rmult k x)) =
    Rdiv (Rminus (exp (Rmult k b)) (exp (Rmult k a))) k.
Proof.
move=> hab hk.
rewrite /real_integral_between real_integral_mask /Rintegral.
have region : [set x : real | Rle a x /\ Rlt x b] = `[a, b[%classic.
  rewrite predeqE => x.
  change ((Rle a x /\ Rlt x b) <-> (x \in `[a, b[)).
  rewrite in_itv /=.
  split; first by move=> [/RleP ha /RltP hb]; apply/andP.
  by move=> /andP[/RleP ha /RltP hb]; split.
change ((fun x : real => Rle a x /\ Rlt x b) = `[a, b[%classic) in region.
rewrite region /RealIntegration.lebesgue.
under eq_integral do rewrite RexpE !RealsE.
rewrite ExponentialRegions.integral_between.
- exact/RleP.
- apply/eqP; exact hk.
- by rewrite RexpE !RealsE.
Qed.
