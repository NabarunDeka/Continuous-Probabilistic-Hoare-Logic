(**
  CdfAssertions.v -- cumulative distribution functions as assertion terms.

  In the assertion logic the CDF of a distribution [d] at a cutoff [c] is

      F(c) = integral of indicator[z <= c] against the density of d,

  written as the probabilistic term [p_cdf z d c]:

      E[ integral z ~ d, indicator[z <= c] ].

  An expectation integrates over the current state measure, so in a state of
  total mass [M] this term evaluates to [M * F(c)].  Examples therefore state
  their postconditions cross-multiplied against [Pr[true]] rather than
  dividing by it (Pterms have no division).

  The analytic facts below are axiom-free: they use only the library's
  density normalization, integral linearity and interval/point masses.  In
  particular nothing here relies on the exponential-integral axioms of
  [AnalyticalCalculations.v].
*)

From Stdlib Require Import Reals Lra.
Require Import MeasureIntegration CPHL.
Require Import CPHLFacts.ConstructFacts CPHLFacts.CalculationFacts.
Require Import CdfLibraryFacts.
Require Import CPHLFacts.ExponentialIntegrals.

Open Scope R_scope.

(** * Assertion syntax *)

(** Subtraction of probabilistic terms, as an abbreviation. *)
Definition p_sub (p1 p2 : Pterm) : Pterm :=
  PAdd p1 (PMul (PConst (-1)) p2).

(** The CDF of [d] at [c], with [z] as the integration variable. *)
Definition p_cdf (z : RealProgramVar) (d : Distribution) (c : Term) : Pterm :=
  PExpect (QIntegral z d (QIndicator (FLe (TProgVar z) c))).

(** * Generic real-integral facts *)

Lemma real_integral_le :
  forall f g : R -> R,
    real_integrable f -> real_integrable g ->
    (forall x, f x <= g x) ->
    real_integral f <= real_integral g.
Proof.
  intros f g Hf Hg Hle.
  assert (Hsum : real_integral (fun x => g x + (-1) * f x) =
                 real_integral g + -1 * real_integral f).
  { rewrite real_integral_add;
      [| exact Hg | apply real_integrable_scale; exact Hf].
    rewrite real_integral_scale; [reflexivity | exact Hf]. }
  assert (Hnn : 0 <= real_integral (fun x => g x + (-1) * f x)).
  { apply real_integral_nonneg; intro x; specialize (Hle x); lra. }
  lra.
Qed.

Lemma exp_le_mono : forall x y : R, x <= y -> exp x <= exp y.
Proof.
  intros x y Hxy.
  destruct (Rle_lt_or_eq_dec x y Hxy) as [Hlt | Heq].
  - left; apply exp_increasing; exact Hlt.
  - right; rewrite Heq; reflexivity.
Qed.

(** * The Laplace density and its regions *)

Section Laplace.

Variables (loc b : R).
Hypothesis Hb : 0 < b.

Definition lap_density (z : R) : R := (1 / (2 * b)) * exp (- Rabs (z - loc) / b).

Definition lap_below (c : R) : R :=
  real_integral (fun z => lap_density z * real_indicator (z < c)).
Definition lap_atmost (c : R) : R :=
  real_integral (fun z => lap_density z * real_indicator (z <= c)).
Definition lap_above (c : R) : R :=
  real_integral (fun z => lap_density z * real_indicator (c <= z)).

Lemma lap_density_pos : forall z, 0 < lap_density z.
Proof.
  intro z; unfold lap_density.
  apply Rmult_lt_0_compat; [| apply exp_pos].
  apply Rdiv_lt_0_compat; lra.
Qed.

Lemma lap_density_integrable : real_integrable lap_density.
Proof. exact (real_integrable_laplace loc b Hb). Qed.

Lemma lap_masked_integrable :
  forall A : R -> Prop, real_event_measurable A ->
    real_integrable (fun z => lap_density z * real_indicator (A z)).
Proof.
  intros A HA; apply real_integrable_mask_right; [exact HA |].
  exact lap_density_integrable.
Qed.

Lemma lap_density_total : real_integral lap_density = 1.
Proof.
  pose (v := demo_valuation).
  assert (Hv : distribution_valid (Laplace (TConst loc) (TConst b)) v)
    by (cbn [distribution_valid term_eval]; exact Hb).
  transitivity (real_integral
                  (distribution_density (Laplace (TConst loc) (TConst b)) v)).
  - apply real_integral_extensional; intro z; reflexivity.
  - exact (real_integral_distribution_density Hv).
Qed.

(** Every cutoff splits the line into two disjoint regions. *)
Lemma lap_below_above : forall c, lap_below c + lap_above c = 1.
Proof.
  intro c; unfold lap_below, lap_above.
  rewrite <- real_integral_add
    by (apply lap_masked_integrable;
        first [apply real_measurable_below | apply real_measurable_above]).
  rewrite <- lap_density_total.
  apply real_integral_extensional; intro z.
  destruct (Rlt_dec z c) as [Hz | Hz].
  - rewrite (real_indicator_true _ Hz).
    rewrite (real_indicator_false (c <= z)) by lra; ring.
  - rewrite (real_indicator_false _ Hz).
    rewrite (real_indicator_true (c <= z)) by lra; ring.
Qed.

(** A single point carries no mass, so [<=] and [<] give the same CDF. *)
Lemma lap_atmost_below : forall c, lap_atmost c = lap_below c.
Proof.
  intro c; unfold lap_atmost, lap_below.
  transitivity
    (real_integral (fun z => lap_density z * real_indicator (z < c)) +
     real_integral (fun z => real_indicator (z = c) * lap_density z)).
  - rewrite <- real_integral_add.
    + apply real_integral_extensional; intro z.
      destruct (Rlt_dec z c) as [Hlt | Hnlt].
      * rewrite (real_indicator_true (z <= c)) by lra.
        rewrite (real_indicator_true (z < c)) by lra.
        rewrite (real_indicator_false (z = c)) by lra; ring.
      * destruct (Req_dec z c) as [Heq | Hne].
        -- rewrite (real_indicator_true (z <= c)) by lra.
           rewrite (real_indicator_false (z < c)) by lra.
           rewrite (real_indicator_true (z = c)) by exact Heq; ring.
        -- rewrite (real_indicator_false (z <= c)) by lra.
           rewrite (real_indicator_false (z < c)) by lra.
           rewrite (real_indicator_false (z = c)) by exact Hne; ring.
    + apply lap_masked_integrable, real_measurable_below.
    + apply real_integrable_mask;
        [apply real_measurable_point | exact lap_density_integrable].
  - assert (H0 : real_integral (fun z => real_indicator (z = c) * lap_density z)
                 = 0) by exact (real_integral_singleton_zero c lap_density).
    rewrite H0; ring.
Qed.

Lemma lap_atmost_above : forall c, lap_atmost c + lap_above c = 1.
Proof. intro c; rewrite lap_atmost_below; apply lap_below_above. Qed.

Lemma lap_above_nonneg : forall c, 0 <= lap_above c.
Proof.
  intro c; apply real_integral_nonneg; intro z.
  apply Rmult_le_pos; [left; apply lap_density_pos |].
  unfold real_indicator; destruct (boolp.pselect (c <= z)); lra.
Qed.

Lemma lap_below_nonneg : forall c, 0 <= lap_below c.
Proof.
  intro c; apply real_integral_nonneg; intro z.
  apply Rmult_le_pos; [left; apply lap_density_pos |].
  unfold real_indicator; destruct (boolp.pselect (z < c)); lra.
Qed.

(** Upper tails shrink as the cutoff grows. *)
Lemma lap_above_antitone : forall c1 c2, c1 <= c2 -> lap_above c2 <= lap_above c1.
Proof.
  intros c1 c2 Hc; unfold lap_above.
  apply real_integral_le;
    [apply lap_masked_integrable, real_measurable_above.. |].
  intro z; pose proof (lap_density_pos z).
  unfold real_indicator.
  destruct (boolp.pselect (c2 <= z)); destruct (boolp.pselect (c1 <= z)); nra.
Qed.

(** Every upper tail has positive mass: on [c, c+1) the density is bounded
    below by a positive constant. *)
Lemma lap_above_pos : forall c, 0 < lap_above c.
Proof.
  intro c.
  set (K := (1 / (2 * b)) * exp (- (Rabs (c - loc) + 1) / b)).
  assert (HK : 0 < K).
  { unfold K; apply Rmult_lt_0_compat; [apply Rdiv_lt_0_compat; lra | apply exp_pos]. }
  apply Rlt_le_trans with (K * real_integral_between c (c + 1) (fun _ => 1)).
  { rewrite real_integral_between_one by lra.
    replace (c + 1 - c) with 1 by ring; lra. }
  unfold real_integral_between.
  rewrite <- real_integral_scale by apply real_integrable_between_one.
  unfold lap_above; apply real_integral_le.
  - apply real_integrable_scale, real_integrable_between_one.
  - apply lap_masked_integrable, real_measurable_above.
  - intro z; unfold real_indicator.
    destruct (boolp.pselect (c <= z < c + 1)) as [Hin | Hout];
      destruct (boolp.pselect (c <= z)) as [Hz | Hz].
    + rewrite !Rmult_1_r; unfold K, lap_density.
      apply Rmult_le_compat_l; [left; apply Rdiv_lt_0_compat; lra |].
      apply exp_le_mono.
      unfold Rdiv; apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra |].
      apply Ropp_le_contravar.
      replace (z - loc) with ((c - loc) + (z - c)) by ring.
      eapply Rle_trans; [apply Rabs_triang |].
      rewrite (Rabs_right (z - c)) by lra; lra.
    + lra.
    + pose proof (lap_density_pos z); lra.
    + lra.
Qed.

End Laplace.

(** * From sampled indicators to density integrals *)

Lemma update_real_same :
  forall (v : state) (x : RealProgramVar) (r : R),
    term_eval (TProgVar x) (update_real v x r) = r.
Proof.
  intros v x r; cbn [term_eval update_real real_program_values].
  unfold update_real_values.
  destruct (real_program_var_eq_dec x x); [reflexivity | contradiction].
Qed.

(** An integral binder over a constant Laplace, whose indicator reads only the
    sampled value, is the density integral of the corresponding event. *)
Lemma q_eval_laplace_indicator :
  forall (z : RealProgramVar) (loc b : R) (gamma : CFormula)
    (P : R -> Prop) (v : state),
    0 < b ->
    (forall r, satisfies (update_real v z r) gamma <-> P r) ->
    q_eval (QIntegral z (Laplace (TConst loc) (TConst b)) (QIndicator gamma)) v =
    real_integral (fun r => lap_density loc b r * real_indicator (P r)).
Proof.
  intros z loc b gamma P v Hb HP.
  rewrite q_integral_density by (cbn [distribution_valid term_eval]; exact Hb).
  apply real_integral_extensional; intro r.
  rewrite q_eval_indicatorE.
  rewrite (real_indicator_extensional _ (P r)) by apply HP.
  reflexivity.
Qed.

(** The syntactic Laplace CDF evaluates to the mass times the real CDF. *)
Lemma p_cdf_laplace_eval :
  forall (z : RealProgramVar) (loc b c : R) (ps : Pstate),
    0 < b ->
    pterm_eval (p_cdf z (Laplace (TConst loc) (TConst b)) (TConst c)) ps =
    lap_atmost loc b c *
      expectation (pstate_measure ps) (q_eval (QIndicator c_true)).
Proof.
  intros z loc b c ps Hb.
  cbn [p_cdf pterm_eval].
  rewrite <- expectation_constant.
  apply expectation_extensional; intro v.
  apply q_eval_laplace_indicator; [exact Hb |].
  intro r; cbn [satisfies]; rewrite update_real_same; reflexivity.
Qed.

Lemma pterm_eval_p_sub :
  forall (p1 p2 : Pterm) (ps : Pstate),
    pterm_eval (p_sub p1 p2) ps = pterm_eval p1 ps - pterm_eval p2 ps.
Proof. intros; cbn [p_sub pterm_eval]; ring. Qed.

(** An expectation of a construct that is constant across states is that
    constant times the total mass. *)
Lemma expect_const_construct :
  forall (mu : Measure) (q : PConstruct) (c : R),
    (forall v : state, q_eval q v = c) ->
    expectation mu (q_eval q) = c * expectation mu (q_eval (QIndicator c_true)).
Proof.
  intros mu q c Hc.
  rewrite <- expectation_constant.
  apply expectation_extensional; exact Hc.
Qed.

(** * Closed forms, for use inside proofs only

    These evaluate density integrals with the (proved) exponential-tail
    identity.  No Hoare triple mentions them. *)

Lemma lap_above_closed :
  forall b t : R, 0 < b -> 0 <= t -> lap_above 0 b t = (1 / 2) * exp (- t / b).
Proof.
  intros b t Hb Ht.
  unfold lap_above, lap_density.
  transitivity
    (real_integral (fun z => (1 / (2 * b)) * (real_indicator (t <= z) * exp (- / b * z)))).
  - apply real_integral_extensional; intro z.
    destruct (Rle_dec t z) as [Hz | Hz].
    + rewrite !(real_indicator_true (t <= z)) by exact Hz.
      rewrite Rminus_0_r, Rabs_right by lra.
      replace (- z / b) with (- / b * z) by (field; lra).
      ring.
    + rewrite !(real_indicator_false (t <= z)) by exact Hz; ring.
  - rewrite real_integral_scale
      by (apply real_integrable_exp_above;
          apply Ropp_lt_gt_0_contravar, Rinv_0_lt_compat; exact Hb).
    change (real_integral (fun z => real_indicator (t <= z) * exp (- / b * z)))
      with (real_integral_above t (fun z => exp (- / b * z))).
    rewrite real_integral_exp_above_proved
      by (apply Ropp_lt_gt_0_contravar, Rinv_0_lt_compat; exact Hb).
    replace (- t / b) with (- / b * t) by (field; lra).
    field; lra.
Qed.

Lemma lap_below_zero_half : forall b : R, 0 < b -> lap_below 0 b 0 = 1 / 2.
Proof.
  intros b Hb.
  pose proof (lap_below_above 0 b Hb 0) as H.
  rewrite (lap_above_closed b 0 Hb (Rle_refl 0)) in H.
  replace (- 0 / b) with 0 in H by (field; lra).
  rewrite exp_0 in H; lra.
Qed.

(** The exponential density with rate [a]. *)
Definition exp_density (a z : R) : R := real_indicator (0 <= z) * a * exp (- a * z).

Lemma exp_above_closed :
  forall a t : R, 0 < a -> 0 <= t ->
    real_integral (fun z => exp_density a z * real_indicator (t <= z)) = exp (- a * t).
Proof.
  intros a t Ha Ht.
  unfold exp_density.
  transitivity (real_integral (fun z => a * (real_indicator (t <= z) * exp (- a * z)))).
  - apply real_integral_extensional; intro z.
    destruct (Rle_dec t z) as [Hz | Hz].
    + rewrite (real_indicator_true (t <= z)) by exact Hz.
      rewrite (real_indicator_true (0 <= z)) by lra; ring.
    + rewrite (real_indicator_false (t <= z)) by exact Hz; ring.
  - rewrite real_integral_scale
      by (apply real_integrable_exp_above; lra).
    change (real_integral (fun z => real_indicator (t <= z) * exp (- a * z)))
      with (real_integral_above t (fun z => exp (- a * z))).
    rewrite real_integral_exp_above_proved by lra.
    field; lra.
Qed.

(** The exponential CDF: [P(Z <= t) = 1 - e^(-a t)] for [t >= 0]. *)
Lemma exp_atmost_closed :
  forall a t : R, 0 < a -> 0 <= t ->
    real_integral (fun z => exp_density a z * real_indicator (z <= t)) = 1 - exp (- a * t).
Proof.
  intros a t Ha Ht.
  assert (Hv : distribution_valid (Exponential (TConst a)) demo_valuation)
    by (cbn [distribution_valid term_eval]; exact Ha).
  assert (Hint : real_integrable (exp_density a)).
  { apply (real_integrable_ext (distribution_density (Exponential (TConst a)) demo_valuation)).
    - intro z; reflexivity.
    - apply distribution_density_integrable; exact Hv. }
  assert (Htot : real_integral (exp_density a) = 1).
  { transitivity (real_integral (distribution_density (Exponential (TConst a)) demo_valuation)).
    - apply real_integral_extensional; intro z; reflexivity.
    - exact (real_integral_distribution_density Hv). }
  (* Below [t] and from [t] on partition the line. *)
  assert (Hbelow :
    real_integral (fun z => exp_density a z * real_indicator (z < t)) = 1 - exp (- a * t)).
  { rewrite <- (exp_above_closed a t Ha Ht), <- Htot.
    assert (Hsum :
      real_integral (exp_density a) =
      real_integral (fun z => exp_density a z * real_indicator (z < t)) +
      real_integral (fun z => exp_density a z * real_indicator (t <= z))).
    { rewrite <- real_integral_add.
      - apply real_integral_extensional; intro z.
        destruct (Rlt_dec z t) as [Hz | Hz].
        + rewrite (real_indicator_true (z < t)) by exact Hz.
          rewrite (real_indicator_false (t <= z)) by lra; ring.
        + rewrite (real_indicator_false (z < t)) by exact Hz.
          rewrite (real_indicator_true (t <= z)) by lra; ring.
      - apply real_integrable_mask_right; [apply real_measurable_below | exact Hint].
      - apply real_integrable_mask_right; [apply real_measurable_above | exact Hint]. }
    lra. }
  (* The point [t] carries no mass. *)
  rewrite <- Hbelow.
  transitivity
    (real_integral (fun z => exp_density a z * real_indicator (z < t)) +
     real_integral (fun z => real_indicator (z = t) * exp_density a z)).
  - rewrite <- real_integral_add.
    + apply real_integral_extensional; intro z.
      destruct (Rlt_dec z t) as [Hlt | Hnlt].
      * rewrite (real_indicator_true (z <= t)) by lra.
        rewrite (real_indicator_true (z < t)) by lra.
        rewrite (real_indicator_false (z = t)) by lra; ring.
      * destruct (Req_dec z t) as [Heq | Hne].
        -- rewrite (real_indicator_true (z <= t)) by lra.
           rewrite (real_indicator_false (z < t)) by lra.
           rewrite (real_indicator_true (z = t)) by exact Heq; ring.
        -- rewrite (real_indicator_false (z <= t)) by lra.
           rewrite (real_indicator_false (z < t)) by lra.
           rewrite (real_indicator_false (z = t)) by exact Hne; ring.
    + apply real_integrable_mask_right; [apply real_measurable_below | exact Hint].
    + apply real_integrable_mask; [apply real_measurable_point | exact Hint].
  - assert (H0 : real_integral (fun z => real_indicator (z = t) * exp_density a z) = 0)
      by exact (real_integral_singleton_zero t (exp_density a)).
    rewrite H0; ring.
Qed.

(** Exponential counterpart of [q_eval_laplace_indicator]. *)
Lemma q_eval_exponential_indicator :
  forall (z : RealProgramVar) (a : R) (gamma : CFormula) (P : R -> Prop) (v : state),
    0 < a ->
    (forall r, satisfies (update_real v z r) gamma <-> P r) ->
    q_eval (QIntegral z (Exponential (TConst a)) (QIndicator gamma)) v =
    real_integral (fun r => exp_density a r * real_indicator (P r)).
Proof.
  intros z a gamma P v Ha HP.
  rewrite q_integral_density by (cbn [distribution_valid term_eval]; exact Ha).
  apply real_integral_extensional; intro r.
  rewrite q_eval_indicatorE.
  rewrite (real_indicator_extensional _ (P r)) by apply HP.
  reflexivity.
Qed.
