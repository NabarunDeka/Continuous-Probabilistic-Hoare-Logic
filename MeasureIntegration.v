(** Concrete analytical interfaces shared by CPHL and its supporting proofs.
    Extended-real integrals retain infinite nonnegative limits; real-valued
    operations are used only with the finiteness hypotheses stated below. *)
From Stdlib Require Import Reals FunctionalExtensionality.
From mathcomp Require Import boot order ssralg ssrnum interval_inference.
From mathcomp Require Import boolp classical_sets functions reals topology.
From mathcomp Require Import ereal normedtype sequences esum measure.
From mathcomp Require Import numfun measurable_realfun lebesgue_measure.
From mathcomp Require Import fsbigop simple_functions measurable_fun_approximation.
From mathcomp Require Import lebesgue_integral lebesgue_stieltjes_measure.
From mathcomp Require Import Rstruct Rstruct_topology.
Require Import AnalysisPrelude.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports MeasurableR.
Import HBNNSimple.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Module ConcreteMeasure.
Section Space.
Context {d} {T : measurableType d}.

(** This carrier includes infinite measures. Admissibility is a predicate,
    not a proof field stored inside the measure or probabilistic state. *)
Definition measure := {measure set T -> \bar real}.
Definition Subprob (mu : measure) : Prop := mu setT <= 1.
Definition Finite (mu : measure) : Prop := mu setT < +oo.
Definition event_mass (mu : measure) (A : set T) : R := fine (mu A).
Definition integral (mu : measure) (f : T -> \bar real) :=
  \int[mu]_v f v.
Definition Integrable (mu : measure) (f : T -> R) : Prop :=
  integrable mu setT (EFin \o f).
Definition expectation (mu : measure) (f : T -> R) : R :=
  Rintegral mu setT f.

(** These are the library's countably additive measures. Measurability is
    required at the operation boundary where the library needs it. *)
Definition zero : measure := mzero.
Definition point (v : T) : measure := dirac v.
Definition restrict (mu : measure) A (mA : measurable A) : measure :=
  mrestr mu mA.
Definition push (mu : measure) (f : T -> T)
    (mf : measurable_fun setT f) : measure :=
  @measure_function_pushforward__canonical__measure_function_Measure
    _ _ _ _ _ mu f mf.
Definition add (mu nu : measure) : measure := measure_add mu nu.
Definition scale (c : {nonneg real}) (mu : measure) : measure := mscale c mu.
Definition partial_sum (mus : nat -> measure) n : measure := msum mus n.
Definition series (mus : nat -> measure) : measure := mseries mus 0.

Lemma subprob_finite mu : Subprob mu -> Finite mu.
Proof. move=> h; exact: le_lt_trans h (ltry 1%R). Qed.

Lemma event_finite mu A : Finite mu -> measurable A -> mu A \is a fin_num.
Proof.
move=> h mA; rewrite ge0_fin_numE//.
apply: le_lt_trans h; apply: le_measure; by rewrite ?inE.
Qed.

Lemma event_massE mu A : Finite mu -> measurable A ->
  (event_mass mu A)%:E = mu A.
Proof. move=> h mA; exact/fineK/event_finite. Qed.

Lemma event_empty mu : event_mass mu set0 = 0%R.
Proof. by rewrite /event_mass measure0. Qed.

Lemma event_nonnegative mu A : (0 <= event_mass mu A)%R.
Proof. exact/fine_ge0/measure_ge0. Qed.

Lemma event_monotone mu A B : Finite mu -> measurable A -> measurable B ->
  A `<=` B -> (event_mass mu A <= event_mass mu B)%R.
Proof.
move=> h mA mB AB; apply: fine_le; try exact: event_finite.
apply: le_measure; by rewrite ?inE.
Qed.

Lemma event_additive mu A B : Finite mu -> measurable A -> measurable B ->
  A `&` B = set0 ->
  event_mass mu (A `|` B) = (event_mass mu A + event_mass mu B)%R.
Proof.
move=> h mA mB AB.
have e : mu (A `|` B) = mu A + mu B by apply: measureU.
rewrite /event_mass e; apply: fineD; exact: event_finite.
Qed.

Lemma mass_bound mu : Subprob mu -> (event_mass mu setT <= 1)%R.
Proof.
move=> h; rewrite -lee_fin (event_massE (subprob_finite h) measurableT).
exact: h.
Qed.

Lemma zero_subprob : Subprob zero.
Proof. by rewrite /Subprob /zero /mzero lee_fin ler01. Qed.

Lemma point_subprob v : Subprob (point v).
Proof.
change (dirac v setT <= (1 : \bar real)).
by rewrite diracT lexx.
Qed.

Lemma restrict_subprob mu A mA : Subprob mu -> Subprob (@restrict mu A mA).
Proof.
move=> h; change (mu (setT `&` A) <= 1); rewrite setTI.
apply: le_trans h; apply: le_measure; by rewrite ?inE.
Qed.

Lemma push_subprob mu f mf : Subprob mu -> Subprob (@push mu f mf).
Proof. by rewrite /Subprob /push /= /pushforward preimage_setT. Qed.

(** Addition and countable sums need a mass budget; two subprobability
    measures can have a sum of mass two. No closure claim omits this bound. *)
Lemma add_subprob (mu nu : measure) :
  mu setT + nu setT <= 1 -> Subprob (add mu nu).
Proof.
change (mu setT + nu setT <= 1 -> measure_add mu nu setT <= 1).
by rewrite measure_addE.
Qed.

Lemma series_subprob mus :
  (forall n, Subprob (partial_sum mus n)) -> Subprob (series mus).
Proof.
move=> h; rewrite /Subprob /series /mseries.
apply: (cvge_to_le (is_cvg_ereal_nneg_natsum
  (fun i _ => measure_ge0 (mus i) setT))).
apply: nearW => n; move: (h n).
by rewrite /Subprob /partial_sum /msum big_mkord.
Qed.

Lemma expectation_ext mu f g : (forall v, f v = g v) ->
  expectation mu f = expectation mu g.
Proof. move=> h; apply: eq_Rintegral => v _; exact: h. Qed.

Lemma expectation_zero mu : expectation mu (fun _ => 0%R) = 0%R.
Proof. by rewrite /expectation Rintegral_cst// mul0r. Qed.

Lemma expectation_constant mu c :
  expectation mu (fun _ => c) = (c * event_mass mu setT)%R.
Proof. exact: Rintegral_cst. Qed.

Lemma expectation_add mu f g : Integrable mu f -> Integrable mu g ->
  expectation mu (fun v => (f v + g v)%R) =
    (expectation mu f + expectation mu g)%R.
Proof. move=> hf hg; exact: RintegralD. Qed.

Lemma expectation_scale mu c f : Integrable mu f ->
  expectation mu (fun v => (c * f v)%R) = (c * expectation mu f)%R.
Proof. move=> hf; exact: RintegralZl. Qed.

Lemma integrable_add mu f g : Integrable mu f -> Integrable mu g ->
  Integrable mu (fun v => (f v + g v)%R).
Proof.
move=> hf hg.
change (integrable mu setT (fun v => (f v)%:E + (g v)%:E)).
exact: integrableD.
Qed.

Lemma integrable_scale mu c f : Integrable mu f ->
  Integrable mu (fun v => (c * f v)%R).
Proof.
move=> hf; change (integrable mu setT (fun v => c%:E * (f v)%:E)).
exact: integrableZl.
Qed.

(** Partitioning an event is valid in extended reals without a finite-mass
    assumption. Real-valued subtraction would require finiteness. *)
Lemma event_partition (mu : measure) A B : measurable A -> measurable B ->
  mu A = mu (A `&` B) + mu (A `\` B).
Proof. by move=> mA mB; rewrite addeC; exact: measureDI. Qed.

Lemma expectation_indicator mu A : measurable A ->
  expectation mu (\1_A) = event_mass mu A.
Proof. by move=> mA; rewrite /expectation /Rintegral integral_indic// setIT. Qed.

(** Recovering the extended integral from a real expectation needs this
    finiteness proof; [fine] alone also returns zero at either infinity. *)
Lemma expectationE mu f : Integrable mu f ->
  (expectation mu f)%:E = integral mu (EFin \o f).
Proof. move=> hf; exact/fineK/integrable_fin_num. Qed.

Lemma bounded_integral mu f : Subprob mu -> measurable_fun setT f ->
  (forall v, 0 <= f v) -> (forall v, f v <= 1) ->
  0 <= integral mu f /\ integral mu f <= 1.
Proof.
move=> hm mf f0 f1; split; first exact: integral_ge0.
apply: (le_trans _ hm); rewrite -[leRHS]mul1e -integral_cst//.
by apply: ge0_le_integral => // v _; exact: f1.
Qed.

Lemma bounded_integral_finite mu f : Subprob mu -> measurable_fun setT f ->
  (forall v, 0 <= f v) -> (forall v, f v <= 1) ->
  integral mu f \is a fin_num.
Proof.
move=> hm mf f0 f1; have [h0 h1] := bounded_integral hm mf f0 f1.
rewrite ge0_fin_numE//; exact: le_lt_trans h1 (ltry 1%R).
Qed.

(** Nonnegative identities stay in extended reals and therefore remain
    valid for infinite sums, before any subprobability bound is available. *)
Lemma integral_zero f : integral zero f = 0.
Proof. exact: integral_measure_zero. Qed.

Lemma integral_point v f : measurable_fun setT f -> integral (point v) f = f v.
Proof. by move=> mf; rewrite /integral /point integral_dirac// diracT mul1e. Qed.

Lemma integral_add mu nu f : measurable_fun setT f ->
  (forall v, 0 <= f v) ->
  integral (add mu nu) f = integral mu f + integral nu f.
Proof. move=> mf f0; exact: ge0_integral_measure_add. Qed.

Lemma integral_scale c mu f : measurable_fun setT f ->
  (forall v, 0 <= f v) ->
  integral (scale c mu) f = c%:num%:E * integral mu f.
Proof. move=> mf f0; exact: ge0_integral_mscale. Qed.

Lemma integral_series mus f : measurable_fun setT f ->
  (forall v, 0 <= f v) ->
  integral (series mus) f = \sum_(n <oo) integral (mus n) f.
Proof. move=> mf f0; exact: ge0_integral_measure_series. Qed.

Lemma integral_push mu phi mphi f : measurable_fun setT f ->
  (forall v, 0 <= f v) ->
  integral (@push mu phi mphi) f = integral mu (f \o phi).
Proof.
move=> mf f0; rewrite /integral /push /= ge0_integral_pushforward//.
Qed.

(** Restricting a measure agrees with restricting its integrand. First
    check simple functions, then pass to their increasing approximations. *)
Lemma simple_integral_restrict mu A mA (h : {nnsfun T >-> real}) :
  sintegral (@restrict mu A mA) h = sintegral mu (h \_ A).
Proof.
rewrite /sintegral; apply: eq_fsbigr => r _.
case: (eqVneq r 0%R) => [->|r0]; first by rewrite !mul0e.
rewrite /restrict /= /mrestr preimage_restrict.
change (r%:E * mu (h @^-1` [set r] `&` A) =
  r%:E * mu ((if 0%R \in [set r] then ~` A else set0)
    `|` A `&` h @^-1` [set r])).
by rewrite in_set1 eq_sym (negbTE r0) set0U setIC.
Qed.

Lemma integral_restrict mu A mA f : measurable_fun setT f ->
  (forall v, 0 <= f v) ->
  integral (@restrict mu A mA) f = integral mu (f \_ A).
Proof.
move=> mf f0.
pose g := nnsfun_approx measurableT mf.
have ndg x : nondecreasing_seq (g^~x).
  by move=> m n mn; exact/lefP/nd_nnsfun_approx.
have cg x : EFin \o g^~x @ \oo --> f x.
  exact: cvg_nnsfun_approx.
have Af0 x : 0 <= (f \_ A) x by apply: erestrict_ge0.
pose gA n := proj_nnsfun (g n) mA.
have gAE n : gA n = (g n \_ A) :> (T -> real) by rewrite mrestrict.
have ndgA x : nondecreasing_seq (gA^~x).
  move=> m n mn; rewrite !gAE /patch.
  by case: ifP => // _; exact: ndg.
have cgA x : EFin \o gA^~x @ \oo --> (f \_ A) x.
  rewrite /patch; case: ifPn => hx.
  - under eq_fun do rewrite gAE /patch hx; exact: cg.
  - under eq_fun do rewrite gAE /patch (negbTE hx); exact: cvg_cst.
rewrite /integral (nd_ge0_integral_lim _ f0 ndg cg).
rewrite (nd_ge0_integral_lim _ Af0 ndgA cgA).
congr (limn _); apply/funext => n /=.
by rewrite gAE simple_integral_restrict.
Qed.

Lemma bounded_integrable mu (f : T -> real) : Subprob mu ->
  measurable_fun setT f -> (forall v, (0 <= f v)%R) ->
  (forall v, (f v <= 1)%R) -> Integrable mu f.
Proof.
move=> hm mf f0 f1.
have me : measurable_fun setT (EFin \o f) by exact/measurable_EFinP.
have e0 v : 0 <= (f v)%:E by rewrite lee_fin.
have e1 v : (f v)%:E <= 1 by rewrite lee_fin.
have [h0 h1] := bounded_integral hm me e0 e1.
apply/integrableP; split => //.
under eq_integral do rewrite /= ger0_norm//.
exact: le_lt_trans h1 (ltry 1%R).
Qed.

(** The coefficient bound is essential: scaling by two need not preserve
    admissibility. The measure operation itself accepts every nonnegative c. *)
Lemma scale_subprob c mu : (c%:num <= 1)%R -> Subprob mu ->
  Subprob (scale c mu).
Proof.
move=> hc hm; change (c%:num%:E * mu setT <= 1).
apply: (le_trans (_ : c%:num%:E * mu setT <= c%:num%:E * 1)).
- by apply: lee_wpmul2l; [rewrite lee_fin|exact: hm].
- by rewrite mule1 lee_fin.
Qed.

Lemma partial_sum_cvg mus A :
  (fun n => partial_sum mus n A) @ \oo --> series mus A.
Proof.
rewrite /partial_sum /series /= /msum /mseries.
have -> : (fun n => \sum_(k < n) mus k A) =
    (fun n => \sum_(0 <= k < n) mus k A).
  by apply/funext => n; rewrite big_mkord.
by apply: is_cvg_ereal_nneg_natsum => i _; exact: measure_ge0.
Qed.

Lemma partial_sum_increasing mus A :
  nondecreasing_seq (fun n => partial_sum mus n A).
Proof.
apply/nondecreasing_seqP => n.
rewrite /partial_sum /= /msum big_ord_recr /=.
by apply: leeDl; exact: measure_ge0.
Qed.

Lemma integral_nonnegative_add mu f g :
  measurable_fun setT f -> measurable_fun setT g ->
  (forall v, 0 <= f v) -> (forall v, 0 <= g v) ->
  integral mu (fun v => f v + g v) = integral mu f + integral mu g.
Proof. move=> mf mg f0 g0; exact: ge0_integralD. Qed.

(** This is the analytical limit law; it makes no assertion that arbitrary
    program exit approximations satisfy a mass bound or increase. *)
Lemma integral_increasing_limit mu fs :
  (forall n, measurable_fun setT (fs n)) ->
  (forall n v, 0 <= fs n v) ->
  (forall v, nondecreasing_seq (fs^~v)) ->
  integral mu (fun v => limn (fs^~v)) = limn (fun n => integral mu (fs n)).
Proof. move=> mf f0 nd; exact: monotone_convergence. Qed.

End Space.
End ConcreteMeasure.
