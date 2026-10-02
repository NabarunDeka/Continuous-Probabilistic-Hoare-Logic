(** A density specified on measurable events also changes nonnegative
    integrals. This bridges the concrete sampling measures to raw densities. *)
From Stdlib Require Import Reals.
From mathcomp Require Import boot order ssralg ssrnum interval_inference finmap.
From mathcomp Require Import boolp classical_sets functions fsbigop reals topology.
From mathcomp Require Import ereal normedtype sequences esum measure numfun.
From mathcomp Require Import measurable_realfun simple_functions lebesgue_integral.
From mathcomp Require Import lebesgue_stieltjes_measure Rstruct Rstruct_topology.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports MeasurableR HBNNSimple.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section Density.
Context {d} {T : measurableType d} {R : realType}.
Variables (mu nu : {measure set T -> \bar R}) (density : T -> R).
Hypotheses (md : measurable_fun setT density)
  (d0 : forall x, (0 <= density x)%R)
  (events : forall A, measurable A ->
    nu A = \int[mu]_(x in A) (density x)%:E).

(** Approximate the reward from below by simple functions. Finite sums use
    the event hypothesis; monotone convergence passes the identity to the limit.
    The density is real-valued, so multiplication respects pointwise limits. *)
Lemma integral_density_from_events f :
  (forall x, 0 <= f x) -> measurable_fun setT f ->
  \int[mu]_x (f x * (density x)%:E) = \int[nu]_x f x.
Proof.
move=> f0 mf; pose h := nnsfun_approx measurableT mf.
have -> : \int[nu]_x f x =
    lim (\int[nu]_x (EFin \o h n) x @[n --> \oo]).
  have fE x : f x = lim ((EFin \o h n) x @[n --> \oo]).
    by apply/esym/cvg_lim => //; apply: cvg_nnsfun_approx.
  under eq_integral => x _ do rewrite fE.
  apply: monotone_convergence => //.
  - move=> n; exact/measurable_EFinP.
  - by move=> n x _ /=; rewrite lee_fin.
  - by move=> x _ a b ab; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
have -> : \int[mu]_x (f x * (density x)%:E) =
    lim (\int[mu]_x ((EFin \o h n) x * (density x)%:E) @[n --> \oo]).
  have fg x : f x * (density x)%:E =
      lim ((EFin \o h n) x * (density x)%:E @[n --> \oo]).
    apply/esym/cvg_lim => //; apply: cvgeZr => //.
    by apply: cvg_nnsfun_approx.
  under eq_integral => x _ do rewrite fg.
  apply: monotone_convergence => //.
  - move=> n; apply: emeasurable_funM; exact/measurable_EFinP.
  - by move=> n x _ /=; rewrite mule_ge0 ?lee_fin.
  - move=> x _ a b ab /=; rewrite lee_wpmul2r ?lee_fin//.
    exact/lefP/nd_nnsfun_approx.
suff eqI n : \int[mu]_x ((EFin \o h n) x * (density x)%:E) =
    \int[nu]_x (EFin \o h n) x.
  by under eq_fun do rewrite eqI.
transitivity (\int[mu]_x
  ((\sum_(y \in range (h n)) (y * \1_(h n @^-1` [set y]) x)%:E) * (density x)%:E)).
- by apply: eq_integral => x _; rewrite /= fsumEFin// -(fimfunE (h n) x).
- under eq_integral => x _.
    rewrite ge0_mule_fsuml => [y _|]; first exact: nnfun_muleindic_ge0.
    over.
  rewrite ge0_integral_fsum//.
  + move=> y; apply: emeasurable_funM; apply/measurable_EFinP => //.
    exact: measurable_funM.
  + move=> n' y _; apply: mule_ge0; last by rewrite lee_fin.
    by rewrite EFinM; exact: nnfun_muleindic_ge0.
  + transitivity (sintegral nu (h n)); last by rewrite integral_nnsfun// patch_setT.
    rewrite sintegralE; apply: eq_fsbigr => r hr.
    under eq_integral do rewrite EFinM -muleA.
    rewrite ge0_integralZl//.
    * apply: emeasurable_funM; exact/measurable_EFinP.
    * by move=> x _; rewrite mule_ge0 ?lee_fin.
    * by move: hr; rewrite inE => -[x _ <-]; rewrite lee_fin.
    * congr (_ * _); rewrite events//.
      rewrite [RHS]integral_mkcond.
      by apply: eq_integral => x _; rewrite epatch_indic /= muleC.
Qed.
End Density.
