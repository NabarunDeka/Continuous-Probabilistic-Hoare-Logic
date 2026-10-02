(** Density correspondence and boundary checks for the production sampling
    laws. No historical example-calculation assumption is imported here. *)
From Stdlib Require Import Reals.
From mathcomp Require Import boot order ssralg ssrnum interval interval_inference.
From mathcomp Require Import boolp classical_sets functions reals topology.
From mathcomp Require Import ereal normedtype sequences exp numfun measure measurable_realfun.
From mathcomp Require Import lebesgue_measure lebesgue_integral lebesgue_stieltjes_measure kernel.
From mathcomp Require Import uniform_distribution normal_distribution bernoulli_distribution.
From mathcomp Require Import Rstruct Rstruct_topology.
Require Import AnalysisPrelude MeasureIntegration DistributionKernels CPHL.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports MeasurableR NormalPdf0.
Import ValuationSpace DistributionSemantics DistributionLaws.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** The public density uses propositional comparisons and Stdlib functions;
    these equalities connect it to the library's real carrier and formulas. *)
Lemma uniform_density_bridge a b v z :
  distribution_density (Uniform a b) v z =
  uniform_pdf (term_eval a v) (term_eval b v) z.
Proof.
rewrite /distribution_density /uniform_pdf.
case: ifP => [/andP [/RleP ha /RleP hb]|h].
- by rewrite real_indicator_true// RdivE mul1r.
- rewrite real_indicator_false ?RdivE ?mul0r//.
  move=> [/RleP ha /RleP hb]; by move/negP: h; apply; apply/andP.
Qed.

Lemma laplace_density_bridge a b v z :
  distribution_density (Laplace a b) v z =
  laplace_pdf (term_eval a v) (term_eval b v) z.
Proof.
by rewrite /distribution_density /laplace_pdf RexpE !RealsE mul1r.
Qed.

Lemma gaussian_density_bridge a b v z :
  distribution_valid (Gaussian a b) v ->
  distribution_density (Gaussian a b) v z =
  normal_pdf0 (term_eval a v) (term_eval b v) z.
Proof.
move=> /RltP s0.
rewrite /distribution_density /normal_pdf0 normal_peak_positive//.
rewrite RexpE RsqrtE Rtrigo_PIE !RealsE mul1r /normal_fun expr2.
congr (_ * (expR _))%R.
congr (_ / _)%R.
rewrite -(mulr_natr (term_eval b v ^+ 2)%R 2) expr2.
by rewrite -mulrA mulrC.
Qed.

(** Valid laws have unit mass; invalid parameters give the zero measure
    on every event, including degenerate Uniform intervals and zero scale. *)
Lemma distribution_mass_valid d v : distribution_valid d v ->
  distribution_measure d v setT = 1.
Proof. move=> /validbP h; by rewrite /distribution_measure real_law_mass h. Qed.

Lemma distribution_mass_subprob d v : distribution_measure d v setT <= 1.
Proof. rewrite /distribution_measure; exact: sprob_kernel_le1. Qed.

Lemma distribution_invalid d v A : ~ distribution_valid d v ->
  distribution_measure d v A = 0.
Proof.
move=> h; have hv : ~~ validb d v by apply/negP => /validbP.
clear h; case: d hv => a b hv.
- exact: (@parameter_measure_invalid _ _ uniform_valid_measurable
    uniform_density_measurable (@uniform_pdf_ge0 real)
    uniform_density_mass (term_eval a v, term_eval b v) A hv).
- exact: (@parameter_measure_invalid _ _ scale_valid_measurable
    laplace_density_measurable laplace_pdf_ge0
    integral_laplace_pdf (term_eval a v, term_eval b v) A hv).
- exact: (@parameter_measure_invalid _ _ scale_valid_measurable
    gaussian_density_measurable (fun a b x _ => normal_pdf0_ge0 a b x)
    gaussian_density_mass (term_eval a v, term_eval b v) A hv).
Qed.

Lemma distribution_density_event d v A : distribution_valid d v ->
  distribution_measure d v A =
  \int[lebesgue_measure]_(z in A) (distribution_density d v z)%:E.
Proof.
case: d => a b /[dup] h /RltP hb; rewrite /distribution_measure /real_law.
- rewrite uniform_valid_event//; apply: eq_integral => z _.
  by rewrite uniform_density_bridge.
- rewrite laplace_valid_event//; apply: eq_integral => z _.
  by rewrite laplace_density_bridge.
- rewrite gaussian_valid_event//; apply: eq_integral => z _.
  by rewrite gaussian_density_bridge.
Qed.

Lemma distribution_density_nonnegative d v z : distribution_valid d v ->
  (0 <= distribution_density d v z)%R.
Proof.
case: d => a b h.
- rewrite uniform_density_bridge; apply: uniform_pdf_ge0; exact/RltP.
- rewrite laplace_density_bridge; apply: laplace_pdf_ge0; exact/RltP.
- rewrite gaussian_density_bridge//; exact: normal_pdf0_ge0.
Qed.

Lemma distribution_density_normalized d v : distribution_valid d v ->
  \int[lebesgue_measure]_z (distribution_density d v z)%:E = 1.
Proof.
move=> h; rewrite -(distribution_density_event setT h).
exact: distribution_mass_valid.
Qed.

(** Normalized nonnegative densities are integrable, so their real-valued
    integral agrees with the finite extended integral rather than a fallback. *)
Lemma distribution_density_measurable d v : distribution_valid d v ->
  @measurable_fun _ _ RealIntegration.Space RealIntegration.Space
    setT (distribution_density d v).
Proof.
case: d => a b h.
- apply: (eq_measurable_fun (uniform_pdf (term_eval a v) (term_eval b v))).
  + by move=> z _; rewrite uniform_density_bridge.
  + exact: measurable_uniform_pdf.
- apply: (eq_measurable_fun (laplace_pdf (term_eval a v) (term_eval b v))).
  + by move=> z _; rewrite laplace_density_bridge.
  + exact: measurable_laplace_pdf.
- apply: (eq_measurable_fun (normal_pdf0 (term_eval a v) (term_eval b v))).
  + by move=> z _; rewrite gaussian_density_bridge.
  + exact: measurable_normal_pdf0.
Qed.

Lemma distribution_density_integrable d v : distribution_valid d v ->
  real_integrable (distribution_density d v).
Proof.
move=> h; apply/integrableP; split.
- apply/measurable_EFinP; exact: distribution_density_measurable.
- under eq_integral do rewrite /= ger0_norm ?lee_fin
    ?distribution_density_nonnegative//.
  by rewrite distribution_density_normalized// ltry.
Qed.

Lemma real_integral_distribution_density d v : distribution_valid d v ->
  real_integral (distribution_density d v) = 1%R.
Proof.
move=> h.
change (fine (\int[lebesgue_measure]_z (distribution_density d v z)%:E) = 1%R).
by rewrite distribution_density_normalized.
Qed.

(** The kernel evaluator loses all mass on invalid parameters, independently
    of the body. This uses the zero measure, rather than raw invalid densities. *)
Lemma q_integral_invalid x d q v : ~ distribution_valid d v ->
  q_eval (QIntegral x d q) v = 0%R.
Proof.
move=> h.
change (fine (\int[distribution_measure d v]_z
  (q_eval q (update_real v x z))%:E) = 0%R).
have -> : (\int[distribution_measure d v]_z
    (q_eval q (update_real v x z))%:E) =
    \int[(mzero : {measure set real -> \bar real})]_z
      (q_eval q (update_real v x z))%:E.
  apply: eq_measure_integral => A _ _; exact: distribution_invalid.
by rewrite integral_measure_zero.
Qed.

(** Boundary cases exercise the total policy, including parameter expressions
    that read the old value of the variable being sampled. *)
Example uniform_equal_endpoints t v A :
  distribution_measure (Uniform t t) v A = 0.
Proof. apply: distribution_invalid => /RltP; by rewrite ltxx. Qed.

Example laplace_zero_scale t v A :
  distribution_measure (Laplace t (TConst 0%R)) v A = 0.
Proof. apply: distribution_invalid => /RltP; by rewrite ltxx. Qed.

Example gaussian_negative_scale t v A :
  distribution_measure (Gaussian t (TConst (-1)%R)) v A = 0.
Proof. apply: distribution_invalid => /RltP; by rewrite ltr0N1. Qed.

Example gaussian_incoming_value x v A :
  distribution_measure (Gaussian (TProgVar x) (TProgVar x)) v A =
  gaussian (real_program_values v x, real_program_values v x) A.
Proof. reflexivity. Qed.

Example gaussian_varying_deviation x v : (0 < real_program_values v x)%R ->
  distribution_measure (Gaussian (TProgVar x) (TProgVar x)) v setT = 1.
Proof. move=> h; apply: distribution_mass_valid; exact/RltP. Qed.

Example toss_zero_endpoint v : toss_measure (TConst 0%R) v [set false] = 1.
Proof.
change (DistributionLaws.toss 0 [set false] = 1).
by rewrite toss_point /bernoulli_pmf ?subr0// /toss_valid lexx ler01.
Qed.

Example toss_one_endpoint v : toss_measure (TConst 1%R) v [set true] = 1.
Proof.
change (DistributionLaws.toss 1 [set true] = 1).
by rewrite toss_point /bernoulli_pmf// /toss_valid ler01 lexx.
Qed.

Example toss_invalid_probability v A : toss_measure (TConst 2%R) v A = 0.
Proof.
change (DistributionLaws.toss 2 A = 0).
apply: toss_invalid; by rewrite /toss_valid ler0n andTb -ltNge ltr1n.
Qed.

(** These checks integrate sampling laws over zero, Dirac, and mixed inputs;
    they do not introduce a Cmd interpreter or update any valuation. *)
Lemma sampling_zero_input d A :
  \int[(mzero : Measure)]_v distribution_measure d v A = 0.
Proof. exact: integral_measure_zero. Qed.

Lemma sampling_dirac_input d (v : Valuation) A : measurable A ->
  \int[dirac v]_w distribution_measure d w A = distribution_measure d v A.
Proof.
move=> mA; rewrite integral_dirac ?diracT ?mul1e//.
exact: real_law_measurable.
Qed.


Lemma sampling_mixed_input d (v w : Valuation) (c e : {nonneg real}) :
  distribution_valid d v -> ~ distribution_valid d w ->
  \int[measure_add (mscale c (dirac v)) (mscale e (dirac w))]_u
    distribution_measure d u setT = c%:num%:E.
Proof.
move=> hv hw.
have mf : measurable_fun [set: Valuation]
    (fun u => distribution_measure d u setT).
  exact: real_law_measurable.
have f0 u : 0 <= distribution_measure d u setT by exact: measure_ge0.
rewrite ge0_integral_measure_add// !ge0_integral_mscale//
  !sampling_dirac_input// distribution_mass_valid// distribution_invalid//.
by rewrite mule1 mule0 adde0.
Qed.
