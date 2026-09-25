(** Library-only distribution foundation. Parameters are ordinary reals;
    invalid parameters produce zero mass, never a fallback distribution. *)
From Stdlib Require Import Reals Lra.
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum interval interval_inference.
From mathcomp Require Import boolp classical_sets functions fsbigop reals topology.
From mathcomp Require Import ereal normedtype sequences exp realfun numfun measure.
From mathcomp Require Import measurable_realfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import lebesgue_stieltjes_measure radon_nikodym kernel ftc.
From mathcomp Require Import uniform_distribution normal_distribution exponential_distribution bernoulli_distribution.
From mathcomp Require Import Rstruct Rstruct_topology.
Require Import AnalysisPrelude MeasureIntegration.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports MeasurableR NormalPdf0.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Module DistributionLaws.
Local Notation mu := (@lebesgue_measure real).

(** The total reciprocal is Borel measurable, including its value at zero.
    Splitting off that singleton avoids asserting continuity there. *)
Lemma measurable_inverse : measurable_fun [set: real] (fun x => x^-1)%R.
Proof.
rewrite -(setUv [set (0%R : real)]); apply/measurable_funU => //.
- exact: measurableC.
- split; first exact: measurable_fun_set1.
  apply: open_continuous_measurable_fun.
  + apply: closed_openC; exact/accessible_closed_set1/hausdorff_accessible/Rhausdorff.
  + move=> x; rewrite inE => x0; apply: continuousV => //.
    by apply/eqP => h; apply: x0; exact: h.
Qed.

Lemma measurable_sqrt : measurable_fun [set: real] Num.sqrt.
Proof. apply: continuous_measurable_fun; exact: sqrt_continuous. Qed.

(** Laplace is normalized below using the two exponential tails. *)
Definition laplace_pdf (m s x : real) : real :=
  ((2 * s)^-1 * expR (- `|x - m| / s))%R.

Lemma laplace_pdf_ge0 m s x : (0 < s)%R -> (0 <= laplace_pdf m s x)%R.
Proof.
move=> s0; rewrite /laplace_pdf mulr_ge0 ?expR_ge0//.
by rewrite invr_ge0 mulr_ge0// ltW.
Qed.

Lemma measurable_laplace_pdf m s : measurable_fun setT (laplace_pdf m s).
Proof.
apply: measurable_funM => //; apply: measurableT_comp; first exact: measurable_expR.
apply: measurable_funM => //; apply: measurable_funN.
apply: measurableT_comp; first exact: normr_measurable.
exact: measurable_funB.
Qed.


(** Translation invariance on all Borel events, obtained from the library's
    uniqueness theorem for Lebesgue measure. *)
Lemma lebesgue_translate (m : real) (A : set real) : measurable A ->
  pushforward mu (fun x : real => (x - m)%R) A = mu A.
Proof.
move=> mA.
have mt : measurable_fun setT (fun x : real => (x - m)%R).
  exact: measurable_funB.
apply/esym/lebesgue_measure_unique => //= _ [[a b]] _ <-.
rewrite /pushforward.
have -> : (fun x : real => (x - m)%R) @^-1` `]a, b] =
    `](a + m)%R, (b + m)%R]%classic.
  by rewrite predeqE => x; rewrite /preimage /= !in_itv/= ltrBrDl lerBlDr (addrC m a).
rewrite !lebesgue_measure_itv/= !lte_fin ltrD2r.
case: ifP => _ //; rewrite -!EFinB.
by congr EFin; rewrite opprD addrACA subrr addr0.
Qed.

Lemma integral_translate (m : real) (f : real -> \bar real) :
  measurable_fun setT f -> (forall x, 0 <= f x) ->
  \int[mu]_x f (x - m)%R = \int[mu]_x f x.
Proof.
move=> mf f0.
have mt : measurable_fun setT (fun x : real => (x - m)%R).
  exact: measurable_funB.
rewrite -(@ge0_integral_pushforward _ _ _ _ _
  (fun x : real => (x - m)%R) mt mu setT f)//.
apply: eq_measure_integral => A mA _; exact: lebesgue_translate.
Qed.

Lemma exponential_positive_mass (r : real) : (0 < r)%R ->
  \int[mu]_(x in `[0%R, +oo[) (exponential_pdf r x)%:E = 1.
Proof.
move=> r0; rewrite -(@integral_exponential_pdf real r r0).
rewrite [LHS]integral_mkcond.
apply: eq_integral => x _; rewrite /exponential_pdf !patchE.
by case: (x \in `[0%R, +oo[%classic).
Qed.

Lemma laplace_positive_mass (s : real) : (0 < s)%R ->
  \int[mu]_(x in `[0%R, +oo[) (laplace_pdf 0 s x)%:E = (2^-1)%:E.
Proof.
move=> s0.
rewrite (eq_integral (fun x => (2^-1)%:E * (exponential_pdf s^-1 x)%:E)).
- move=> x; rewrite inE/= in_itv/= andbT => x0.
  rewrite /laplace_pdf subr0 ger0_norm// exponential_pdfE//.
  by rewrite invfM !EFinM muleA !mulNr (mulrC x (s^-1)%R).
- rewrite ge0_integralZl//=.
  + apply/measurable_EFinP/measurable_funTS; exact: measurable_exponential_pdf.
  + by move=> x _; rewrite lee_fin exponential_pdf_ge0// invr_ge0 ltW.
  + by rewrite exponential_positive_mass ?invr_gt0// mule1.
Qed.

Lemma integral_laplace_pdf (m s : real) : (0 < s)%R ->
  \int[mu]_x (laplace_pdf m s x)%:E = 1.
Proof.
move=> s0.
have mf : measurable_fun setT (fun x => (laplace_pdf 0 s x)%:E).
  apply/measurable_EFinP; exact: measurable_laplace_pdf.
have f0 x : 0 <= (laplace_pdf 0 s x)%:E.
  by rewrite lee_fin laplace_pdf_ge0.
have shiftE x : laplace_pdf m s x = laplace_pdf 0 s (x - m)%R.
  by rewrite /laplace_pdf subr0.
under eq_integral do rewrite shiftE.
rewrite (integral_translate m mf f0).
have reflected :
    \int[mu]_(x in `]-oo, 0%R]) (laplace_pdf 0 s x)%:E =
    \int[mu]_(x in `[0%R, +oo[) (laplace_pdf 0 s x)%:E.
  rewrite (eq_integral (fun x : real => (laplace_pdf 0 s (- x)%R)%:E)).
  - by move=> x _; rewrite /laplace_pdf !subr0 normrN.
  - exact/esym/ge0_integration_by_substitution0.
rewrite -(setUv `[0%R, +oo[%classic) ge0_integral_setU//=.
- exact: measurableC.
- by rewrite setUv.
- exact/disj_setPCl.
- rewrite setCitvr integral_itvbo_itvbc; first exact: measurable_funTS mf.
  rewrite reflected !laplace_positive_mass// -EFinD.
  have half : ((2^-1 + 2^-1)%R : real) = 1%R.
    by rewrite -[X in (X + _)%R](mul1r (2^-1)%R)
      -[X in (_ + X)%R](mul1r (2^-1)%R) -splitr.
  by rewrite half.
Qed.


(** Joint density measurability allows every parameter to depend on state.
    In particular Gaussian deviation is not restricted to a constant. *)
Section JointDensity.
Context {d} {T : measurableType d}.
Variables a b z : T -> real.
Hypotheses (ma : measurable_fun setT a) (mb : measurable_fun setT b)
  (mz : measurable_fun setT z).

Lemma measurable_uniform_joint :
  measurable_fun setT (fun t => uniform_pdf (a t) (b t) (z t)).
Proof.
rewrite /uniform_pdf; apply: measurable_fun_ifT => //.
- apply: measurable_and; exact: measurable_fun_ler.
- apply: measurableT_comp; first exact: measurable_inverse.
  exact: measurable_funB.
Qed.

Lemma measurable_laplace_joint :
  measurable_fun setT (fun t => laplace_pdf (a t) (b t) (z t)).
Proof.
rewrite /laplace_pdf; apply: measurable_funM.
- apply: measurableT_comp; first exact: measurable_inverse.
  exact: measurable_funM.
- apply: measurableT_comp; first exact: measurable_expR.
  apply: measurable_funM.
  + apply: measurable_funN; apply: measurableT_comp; first exact: normr_measurable.
    exact: measurable_funB.
  + exact: measurableT_comp measurable_inverse mb.
Qed.

Lemma measurable_gaussian_joint :
  measurable_fun setT (fun t => normal_pdf0 (a t) (b t) (z t)).
Proof.
rewrite /normal_pdf0 /normal_peak /normal_fun; apply: measurable_funM.
- apply: measurableT_comp; first exact: measurable_inverse.
  apply: measurableT_comp; first exact: measurable_sqrt.
  apply: (eq_measurable_fun (fun x => ((b x ^+ 2 * trigonometry_functions.pi) * 2)%R)).
    by move=> x _; rewrite mulr_natr.
  apply: measurable_funM => //.
  apply: measurable_funM => //; exact: measurable_funX.
- apply: measurableT_comp; first exact: measurable_expR.
  apply: measurable_funM.
  + apply: measurable_funN; apply: measurable_funX; exact: measurable_funB.
  + apply: measurableT_comp; first exact: measurable_inverse.
    apply: (eq_measurable_fun (fun x => (b x ^+ 2 * 2)%R)).
      by move=> x _; rewrite mulr_natr.
    apply: measurable_funM => //; exact: measurable_funX.
Qed.
End JointDensity.


(** Positive deviation removes the absolute value hidden in the library's
    Gaussian normalizer and recovers the paper's standard density formula. *)
Lemma normal_peak_positive (s : real) : (0 < s)%R ->
  normal_peak s = ((s * Num.sqrt (2 * trigonometry_functions.pi))^-1)%R.
Proof.
move=> s0; rewrite /normal_peak -mulr_natr -mulrA.
rewrite (mulrC trigonometry_functions.pi (2%R : real)).
by rewrite sqrtrM ?sqr_ge0// sqrtr_sqr ger0_norm// ltW.
Qed.

(** A nonnegative jointly measurable density defines a countably additive
    measure for each parameter and a measurable kernel for the whole family. *)
Section DensityKernel.
Context {d} {T : measurableType d}.
Variable density : T * real -> real.
Hypothesis md : measurable_fun setT density.
Hypothesis d0 : forall p, (0 <= density p)%R.

Definition density_measure (t : T) (A : set real) : \bar real :=
  let _ := md in let _ := d0 in
  \int[mu]_(x in A) (density (t, x))%:E.

Lemma density_measure0 t : density_measure t set0 = 0.
Proof. exact: integral_set0. Qed.

Lemma density_measure_ge0 t A : 0 <= density_measure t A.
Proof. apply: integral_ge0 => x _; by rewrite lee_fin d0. Qed.

Lemma density_measure_sigma_additive t : semi_sigma_additive (density_measure t).
Proof.
apply: semi_sigma_additive_nng_induced.
- apply/measurable_EFinP; exact: measurable_fun_pair2.
- by move=> x; rewrite lee_fin d0.
Qed.

HB.instance Definition _ t := isMeasure.Build _ _ _ (density_measure t)
  (density_measure0 t) (density_measure_ge0 t) (@density_measure_sigma_additive t).

Lemma density_measure_measurable A : measurable A ->
  measurable_fun setT (density_measure ^~ A).
Proof.
move=> mA.
have -> : (density_measure ^~ A) =
  fubini_F mu (fun p : T * real => (density p)%:E * (\1_A p.2)%:E).
  apply/funext => t; rewrite /density_measure /fubini_F [LHS]integral_mkcond.
  apply: eq_integral => x _; rewrite patchE indicE.
  by case: (x \in A); rewrite ?mule1 ?mule0.
apply: measurable_fun_fubini_tonelli_F.
- apply: emeasurable_funM => //; first exact/measurable_EFinP.
  apply/measurable_EFinP/measurableT_comp; last exact: measurable_snd.
  exact: measurable_indic.
- by move=> [t x]; rewrite mule_ge0// lee_fin d0.
Qed.

(** Give the bundled family a name so HB can register its kernel structure. *)
Definition density_kernel (t : T) : {measure set real -> \bar real} :=
  density_measure t.

HB.instance Definition _ := isKernel.Build _ _ _ _ _
  density_kernel density_measure_measurable.
End DensityKernel.


Section GuardedFamily.
Variable valid : real -> real -> bool.
Variable pdf : real -> real -> real -> real.
Hypothesis mv : measurable_fun setT (fun p : real * real => valid p.1 p.2).
Hypothesis mp : measurable_fun setT
  (fun p : (real * real) * real => pdf p.1.1 p.1.2 p.2).
Hypothesis p0 : forall a b x, valid a b -> (0 <= pdf a b x)%R.
Hypothesis p1 : forall a b, valid a b -> \int[mu]_x (pdf a b x)%:E = 1.

Definition guarded_density (p : (real * real) * real) : real :=
  if valid p.1.1 p.1.2 then pdf p.1.1 p.1.2 p.2 else 0%R.

Lemma guarded_density_measurable : measurable_fun setT guarded_density.
Proof.
apply: measurable_fun_ifT => //.
exact: measurableT_comp mv measurable_fst.
Qed.

Lemma guarded_density_ge0 p : (0 <= guarded_density p)%R.
Proof. rewrite /guarded_density; case: ifP => //; exact: p0. Qed.

Definition parameter_measure (p : real * real) : {measure set real -> \bar real} :=
  let _ := p1 in
  @density_kernel _ _ guarded_density guarded_density_measurable
    guarded_density_ge0 p.

Lemma parameter_measure_measurable A : measurable A ->
  measurable_fun setT (parameter_measure ^~ A).
Proof. exact: density_measure_measurable. Qed.

HB.instance Definition _ := isKernel.Build _ _ _ _ _
  parameter_measure parameter_measure_measurable.

Lemma parameter_measure_mass p :
  parameter_measure p setT = if valid p.1 p.2 then 1 else 0.
Proof.
change (\int[mu]_x (guarded_density (p,x))%:E =
  if valid p.1 p.2 then 1 else 0).
rewrite /guarded_density /=; case: ifP => h.
- exact (@p1 p.1 p.2 h).
- exact: integral0.
Qed.

Lemma parameter_measure_subprob :
  ereal_sup [set parameter_measure p setT | p in [set: real * real]] <= 1.
Proof.
apply: ge_ereal_sup => _ [p _ <-]; rewrite parameter_measure_mass.
by case: (valid p.1 p.2); [exact: lexx | exact: lee01].
Qed.

HB.instance Definition _ := Kernel_isSubProbability.Build _ _ _ _ _
  parameter_measure parameter_measure_subprob.

Lemma parameter_measure_valid p A : valid p.1 p.2 ->
  parameter_measure p A = \int[mu]_(x in A) (pdf p.1 p.2 x)%:E.
Proof.
move=> h.
change (\int[mu]_(x in A) (guarded_density (p,x))%:E =
  \int[mu]_(x in A) (pdf p.1 p.2 x)%:E).
by rewrite /guarded_density /= h.
Qed.

Lemma parameter_measure_invalid p A : ~~ valid p.1 p.2 ->
  parameter_measure p A = 0.
Proof.
move=> /negbTE h.
change (\int[mu]_(x in A) (guarded_density (p,x))%:E = 0).
rewrite /guarded_density /= h; exact: integral0.
Qed.

End GuardedFamily.



Definition uniform_valid (a b : real) := (a < b)%R.
Definition scale_valid (_ s : real) := (0 < s)%R.

Lemma uniform_valid_measurable :
  measurable_fun setT (fun p : real * real => uniform_valid p.1 p.2).
Proof. exact: measurable_fun_ltr. Qed.

Lemma scale_valid_measurable :
  measurable_fun setT (fun p : real * real => scale_valid p.1 p.2).
Proof. exact: measurable_fun_ltr. Qed.

Lemma uniform_density_measurable : measurable_fun setT
  (fun p : (real * real) * real => uniform_pdf p.1.1 p.1.2 p.2).
Proof.
apply: measurable_uniform_joint => //; apply: measurableT_comp;
  [exact: measurable_fst | exact: measurable_fst |
   exact: measurable_snd | exact: measurable_fst].
Qed.

Lemma laplace_density_measurable : measurable_fun setT
  (fun p : (real * real) * real => laplace_pdf p.1.1 p.1.2 p.2).
Proof.
apply: measurable_laplace_joint => //; apply: measurableT_comp;
  [exact: measurable_fst | exact: measurable_fst |
   exact: measurable_snd | exact: measurable_fst].
Qed.

Lemma gaussian_density_measurable : measurable_fun setT
  (fun p : (real * real) * real => normal_pdf0 p.1.1 p.1.2 p.2).
Proof.
apply: measurable_gaussian_joint => //; apply: measurableT_comp;
  [exact: measurable_fst | exact: measurable_fst |
   exact: measurable_snd | exact: measurable_fst].
Qed.

Lemma uniform_density_mass a b : uniform_valid a b ->
  \int[mu]_x (uniform_pdf a b x)%:E = 1.
Proof. move=> h; exact: integral_uniform_pdf1 h (subsetT _). Qed.

Lemma gaussian_density_mass a b : scale_valid a b ->
  \int[mu]_x (normal_pdf0 a b x)%:E = 1.
Proof.
move=> b0; have bn0 : b != 0%R by rewrite gt_eqF//.
rewrite (eq_integral (fun x => (normal_pdf a b x)%:E)).
- by move=> x _; rewrite normal_pdfE//.
- exact: integral_normal_pdf.
Qed.

(** These are the complete subprobability kernels on the parameter pair. *)
Definition uniform : real.-spker (real * real) ~> real :=
  @parameter_measure uniform_valid (@uniform_pdf real)
    uniform_valid_measurable uniform_density_measurable
    (@uniform_pdf_ge0 real) uniform_density_mass.

Definition laplace : real.-spker (real * real) ~> real :=
  @parameter_measure scale_valid laplace_pdf
    scale_valid_measurable laplace_density_measurable
    laplace_pdf_ge0 integral_laplace_pdf.

Definition gaussian : real.-spker (real * real) ~> real :=
  @parameter_measure scale_valid (@normal_pdf0 real)
    scale_valid_measurable gaussian_density_measurable
    (fun a b x _ => normal_pdf0_ge0 a b x) gaussian_density_mass.


Lemma uniform_mass p : uniform p setT = if uniform_valid p.1 p.2 then 1 else 0.
Proof. exact: parameter_measure_mass. Qed.
Lemma laplace_mass p : laplace p setT = if scale_valid p.1 p.2 then 1 else 0.
Proof. exact: parameter_measure_mass. Qed.
Lemma gaussian_mass p : gaussian p setT = if scale_valid p.1 p.2 then 1 else 0.
Proof. exact: parameter_measure_mass. Qed.

Lemma uniform_valid_event a b A : uniform_valid a b ->
  uniform (a,b) A = \int[mu]_(x in A) (uniform_pdf a b x)%:E.
Proof. exact: parameter_measure_valid. Qed.
Lemma laplace_valid_event a b A : scale_valid a b ->
  laplace (a,b) A = \int[mu]_(x in A) (laplace_pdf a b x)%:E.
Proof. exact: parameter_measure_valid. Qed.
Lemma gaussian_valid_event a b A : scale_valid a b ->
  gaussian (a,b) A = \int[mu]_(x in A) (normal_pdf0 a b x)%:E.
Proof. exact: parameter_measure_valid. Qed.

(** The Boolean family uses the same zero policy as the continuous laws;
    MathComp's invalid-parameter Dirac fallback is deliberately gated out. *)
Definition toss_valid (p : real) := (0 <= p <= 1)%R.

Definition valid_toss (p : real) : {measure set bool -> \bar real} := bernoulli_prob p.

HB.instance Definition _ p := Measure.on (valid_toss p).
HB.instance Definition _ p := Measure_isProbability.Build _ _ _
  (valid_toss p) (@probability_setT _ _ _ (bernoulli_prob p)).

Definition toss (p : real) : {measure set bool -> \bar real} :=
  if toss_valid p then valid_toss p else mzero.

Lemma toss_valid_measurable : measurable_fun setT toss_valid.
Proof. apply: measurable_and; exact: measurable_fun_ler. Qed.

Lemma toss_measurable A : measurable A -> measurable_fun setT (toss ^~ A).
Proof.
move=> mA.
have -> : (toss ^~ A) =
    (fun p => if toss_valid p then bernoulli_prob p A else 0).
  by apply/funext => p; rewrite /toss; case: (toss_valid p).
apply: measurable_fun_ifT => //; first exact: toss_valid_measurable.
exact: measurable_bernoulli_prob2.
Qed.

HB.instance Definition _ := isKernel.Build _ _ _ _ _ toss toss_measurable.

Lemma toss_mass p : toss p setT = if toss_valid p then 1 else 0.
Proof. by rewrite /toss; case: ifP => _ //; rewrite probability_setT. Qed.

Lemma toss_subprob : ereal_sup [set toss p setT | p in [set: real]] <= 1.
Proof.
apply: ge_ereal_sup => _ [p _ <-]; rewrite toss_mass.
by case: (toss_valid p); [exact: lexx | exact: lee01].
Qed.

HB.instance Definition _ := Kernel_isSubProbability.Build _ _ _ _ _
  toss toss_subprob.

Lemma toss_invalid p A : ~~ toss_valid p -> toss p A = 0.
Proof. by move=> /negbTE h; rewrite /toss h. Qed.

Lemma toss_point p b : toss_valid p -> toss p [set b] = (bernoulli_pmf p b)%:E.
Proof.
move=> h; rewrite /toss h.
change (bernoulli_prob p [set b] = (bernoulli_pmf p b)%:E).
move: h; rewrite /toss_valid => h.
by rewrite /bernoulli_prob h fsbig_set1.
Qed.

End DistributionLaws.
