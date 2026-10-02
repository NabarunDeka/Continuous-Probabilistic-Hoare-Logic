(** Finite certificate folds and bounds for real expectations. These facts
    use finite measures and integrable functions before projecting to R. *)
From Stdlib Require Import Reals Lra Lia.
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals topology ereal measure.
From mathcomp Require Import numfun measurable_realfun lebesgue_integral.
From mathcomp Require Import lebesgue_stieltjes_measure Rstruct Rstruct_topology.
Require Import MeasureIntegration CPHL Soundness.ConstructFacts Soundness.AssertionLogic.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports MeasurableR ValuationSpace.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Lemma satisfies_finite_c_or m regions v :
  satisfies v (finite_c_or m regions) <->
  exists i, Nat.lt i m /\ satisfies v (regions i).
Proof.
  induction m as [|m ih]; cbn [finite_c_or].
  - cbn [satisfies]; split; [tauto|intros [i [hi _] ]; lia].
  - change (((satisfies v (finite_c_or m regions) -> False) ->
      satisfies v (regions m)) <-> exists i, Nat.lt i (S m) /\ satisfies v (regions i)).
    have hor : ((satisfies v (finite_c_or m regions) -> False) -> satisfies v (regions m)) <->
      (satisfies v (finite_c_or m regions) \/ satisfies v (regions m)).
    { (** The encoded disjunction needs only its syntactic left decision. *)
      destruct (cformula_satisfies_dec (finite_c_or m regions) v); tauto. }
    rewrite hor ih.
    split.
    + intros [ [i [hi hv] ] |hv]; [exists i|exists m]; split; try lia; assumption.
    + intros [i [hi hv] ]; destruct (Nat.eq_dec i m) as [->|hne];
        [right; exact hv|left; exists i; split; [lia|exact hv] ].
Qed.

Lemma psatisfies_finite_p_and m formulas ps :
  psatisfies ps (finite_p_and m formulas) <->
  forall i, Nat.lt i m -> psatisfies ps (formulas i).
Proof.
  induction m as [|m ih]; cbn [finite_p_and].
  - split; [intros _ i hi; lia|intros _; apply psatisfies_true].
  - rewrite psatisfies_and ih; split.
    + intros [h hm] i hi; destruct (Nat.eq_dec i m) as [->|hne]; [exact hm|apply h; lia].
    + intro h; split; [intros i hi; apply h; lia|apply h; lia].
Qed.

Lemma finite_r_sum_le m f h :
  (forall i, Nat.lt i m -> Rle (f i) (h i)) ->
  Rle (finite_r_sum m f) (finite_r_sum m h).
Proof.
  induction m as [|m ih]; intro hfh; cbn [finite_r_sum]; first lra.
  apply Rplus_le_compat; [apply ih; intros; apply hfh; lia|apply hfh; lia].
Qed.

Lemma finite_r_sum_nonnegative m f :
  (forall i, Nat.lt i m -> Rle 0 (f i)) -> Rle 0 (finite_r_sum m f).
Proof.
  induction m as [|m ih]; intro hf; cbn [finite_r_sum]; first lra.
  have h0 : Rle 0 (finite_r_sum m f) by apply ih; intros; apply hf; lia.
  have hm : Rle 0 (f m) by apply hf; lia.
  lra.
Qed.

(** Overlap is harmless for an upper bound: a nonnegative finite sum is
    at least any selected summand. No disjointness is used. *)
Lemma finite_r_sum_member_le m f i :
  Nat.lt i m -> (forall j, Nat.lt j m -> Rle 0 (f j)) ->
  Rle (f i) (finite_r_sum m f).
Proof.
  induction m as [|m ih]; intros hi hf; first lia.
  cbn [finite_r_sum].
  have hs : Rle 0 (finite_r_sum m f) by apply finite_r_sum_nonnegative; intros; apply hf; lia.
  have hm : Rle 0 (f m) by apply hf; lia.
  destruct (Nat.eq_dec i m) as [->|hne]; first lra.
  have h : Rle (f i) (finite_r_sum m f) by apply ih; [lia|intros; apply hf; lia].
  lra.
Qed.

Lemma expectation_le_integrable (mu : Measure) f h :
  ConcreteMeasure.Integrable mu f -> ConcreteMeasure.Integrable mu h ->
  (forall v, Rle (f v) (h v)) ->
  Rle (expectation mu f) (expectation mu h).
Proof.
  move=> hf hh hle; apply/RleP; apply: le_Rintegral => // v _.
  exact/RleP/hle.
Qed.

Lemma integrable_finite_r_sum (mu : Measure) m (f : nat -> Valuation -> R) :
  (forall i, Nat.lt i m -> ConcreteMeasure.Integrable mu (f i)) ->
  ConcreteMeasure.Integrable mu (fun v => finite_r_sum m (fun i => f i v)).
Proof.
  induction m as [|m ih]; intro hf; cbn [finite_r_sum].
  - exact: integrable0.
  - apply ConcreteMeasure.integrable_add; [apply ih; intros; apply hf; lia|apply hf; lia].
Qed.

Lemma expectation_finite_r_sum (mu : Measure) m (f : nat -> Valuation -> R) :
  (forall i, Nat.lt i m -> ConcreteMeasure.Integrable mu (f i)) ->
  expectation mu (fun v => finite_r_sum m (fun i => f i v)) =
  finite_r_sum m (fun i => expectation mu (f i)).
Proof.
  induction m as [|m ih]; intro hf; cbn [finite_r_sum].
  - exact: ConcreteMeasure.expectation_zero.
  - have hprev : forall i, Nat.lt i m -> ConcreteMeasure.Integrable mu (f i)
      by intros; apply hf; lia.
    have hlast : ConcreteMeasure.Integrable mu (f m) by apply hf; lia.
    rewrite /expectation (ConcreteMeasure.expectation_add
      (integrable_finite_r_sum mu m f hprev) hlast).
    exact (f_equal2 Rplus (ih hprev) (Logic.eq_refl _)).
Qed.

(** This bound is local to the restricted region, including empty and null
    regions. It avoids normalization and remains valid at zero input mass. *)
Lemma expectation_restrict_bound (mu : Measure) gamma (f : Valuation -> real) a :
  Subprob mu -> measurable_fun setT f ->
  (forall v, (0 <= f v)%R) -> (forall v, (f v <= 1)%R) ->
  (0 <= a)%R -> (forall v, satisfies v gamma -> (f v <= a)%R) ->
  (expectation (ConcreteMeasure.restrict mu (measurable_formula_event gamma)) f <=
    a * measure_of mu (formula_event gamma))%R.
Proof.
  move=> hm mf f0 f1 a0 hfa.
  have hr : Subprob (ConcreteMeasure.restrict mu (measurable_formula_event gamma))
    by exact: ConcreteMeasure.restrict_subprob.
  have hI := ConcreteMeasure.bounded_integrable hr mf f0 f1.
  have mfE : measurable_fun setT (fun v => (f v)%:E) by exact/measurable_EFinP.
  have fE0 v : 0 <= (f v)%:E by rewrite lee_fin.
  rewrite -lee_fin (ConcreteMeasure.expectationE hI) EFinM /measure_of
    (ConcreteMeasure.event_massE (ConcreteMeasure.subprob_finite hm) (measurable_formula_event gamma)).
  rewrite -/(ConcreteMeasure.integral _ _)
    (ConcreteMeasure.integral_restrict mu (measurable_formula_event gamma) mfE fE0).
  rewrite /ConcreteMeasure.integral -integral_mkcond -integral_cst //;
    first exact: measurable_formula_event.
  apply: ge0_le_integral => //.
  - exact: measurable_formula_event.
  - exact: measurable_funS mfE.
Qed.
