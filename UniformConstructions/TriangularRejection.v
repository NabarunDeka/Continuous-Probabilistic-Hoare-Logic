(**
  TriangularRejection.v -- von Neumann rejection under a NON-constant
  envelope, giving the triangular law.

      retry := tt;
      while retry do
        x     <- sample(Uniform(0,1));
        y     <- sample(Uniform(0,1));
        retry := (x <= y)                (* accept iff y < x *)
      end

  THE TRIPLE ([ta_correct], for [0 < t <= 1]):

      { E[1_tt] = w }
          ta_prog
      { Pr[x < t  /\  ~retry]  =  t * t * w }

  The accepted [x] has density [2x] on [0,1] -- the triangular law, i.e.
  Beta(2,1), equivalently the maximum of two independent uniforms.  The
  loop equation is

      s = (1/2) * s + t*t/2,      so   s = t*t.

  WHAT IS NEW HERE.  Every earlier example has an accept condition that
  FACTORS into an x-part and a y-part, so the inner integral collapses to a
  constant.  Here it does not: [y < x] couples the two draws, and the inner
  integral over [y] returns [uniform_cdf 0 1 k] -- a FUNCTION of the outer
  variable.  The outer integral is then a genuine polynomial integral,
  which is what [real_integral_between_linear] supplies.

  This is exactly von Neumann's rejection method (1951) with a polynomial
  envelope, and it is the whole class this framework can reach from uniform
  draws: the accept region's sections must be intervals whose endpoints are
  polynomial in the outer variable.  Marsaglia's polar sampler fails not
  because it is two-dimensional -- its sections are intervals too -- but
  because their length [2*sqrt(1-k^2)] is not a polynomial.

  THE BOUNDARY.  [0 < t] is required strictly.  At [t = 0] the answer is 0,
  but [while_progress] demands positive TARGET exit mass and [t*t/2]
  vanishes there.  Third independent witness to that defect, after
  TruncatedLaplaceRejection.v ([t = a]) and the zero-probability regions
  discussed in NoisyThresholdMonitor.v.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import ClassicalDescription.
From Stdlib Require Import Classical.
Require Import CPHL.
Require Import SampleBeforeLoop.
Require Import PersistentSampleLoop.
Require Import HalfLaplaceRejection.
Require Import UniformAxiomsAdditional.
Require Import UniformRejectionSampling.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * The program *)

Definition ta_x : RealProgramVar := real_program_var "ta_x".
Definition ta_y : RealProgramVar := real_program_var "ta_y".
Definition ta_retry : BoolProgramVar := bool_program_var "ta_retry".
Definition ta_w : ProbLogicVar := prob_logic_var "ta_w".

Lemma ta_x_neq_y : ta_x <> ta_y.
Proof. unfold ta_x, ta_y; intro H; inversion H. Qed.

Definition ta_unit : Distribution := <{ uniform(0, 1) }>.

(** Retry exactly when the draw is rejected, i.e. when [x <= y]. *)
Definition ta_reject : CFormula := <{ ta_x <= ta_y }>.

Definition ta_below (t : R) : CFormula := <{ ta_x < t }>.

Definition ta_guard : CFormula := <{ ta_retry }>.

Definition ta_body : Cmd :=
  <{ ta_x     sample $(ta_unit);
     ta_y     sample $(ta_unit);
     ta_retry b= $(ta_reject) }>.

Definition ta_loop : Cmd := <{ while $(ta_guard) do $(ta_body) end }>.

Definition ta_prog : Cmd := <{ ta_retry b= true; $(ta_loop) }>.

(** * Reading the coordinates back after both updates *)

Lemma ta_val_x :
  forall (v : state) (k m : R),
    real_program_values
      (update_real (update_real v ta_x k) ta_y m) ta_x = k.
Proof.
  intros v k m.
  unfold update_real, update_real_values.
  cbn [real_program_values].
  rewrite (rpv_eq_dec_neq ta_x ta_y _ _ _ ta_x_neq_y).
  rewrite rpv_eq_dec_refl.
  reflexivity.
Qed.

Lemma ta_val_y :
  forall (v : state) (k m : R),
    real_program_values
      (update_real (update_real v ta_x k) ta_y m) ta_y = m.
Proof.
  intros v k m.
  unfold update_real, update_real_values.
  cbn [real_program_values].
  rewrite rpv_eq_dec_refl.
  reflexivity.
Qed.

(** The rejection test couples the two draws: this is the indicator that
    does NOT factor. *)
Lemma ta_indicator_reject :
  forall (v : state) (k m : R),
    real_indicator
      (satisfies (update_real (update_real v ta_x k) ta_y m) ta_reject) =
    real_indicator (k <= m)%R.
Proof.
  intros v k m.
  apply real_indicator_extensional.
  unfold ta_reject.
  cbn [satisfies term_eval].
  rewrite ta_val_x, ta_val_y.
  split; intro H; exact H.
Qed.

Lemma ta_indicator_accept :
  forall (t : R) (v : state) (k m : R),
    real_indicator
      (satisfies (update_real (update_real v ta_x k) ta_y m)
         <{ $(ta_below t) /\ (~ $(ta_reject)) }>) =
    (real_indicator (k < t)%R * real_indicator (m < k)%R)%R.
Proof.
  intros t v k m.
  rewrite (real_indicator_extensional _ ((k < t)%R /\ (m < k)%R)).
  - apply ur_real_indicator_and.
  - rewrite satisfies_c_and.
    unfold ta_below, ta_reject, c_lt, c_not.
    cbn [satisfies term_eval].
    rewrite ta_val_x, ta_val_y.
    split.
    + intro H.
      destruct H as [Hlt Hnr].
      split.
      * destruct (Rlt_dec k t) as [Hd | Hd]; [exact Hd |].
        exfalso; apply Hlt; lra.
      * destruct (Rlt_dec m k) as [Hd | Hd]; [exact Hd |].
        exfalso; apply Hnr; lra.
    + intro H.
      destruct H as [Hkt Hmk].
      split; intro Hc; lra.
Qed.

(** * The inner integral returns a FUNCTION of the outer variable *)

Lemma ta_density_eq :
  forall (v : state) (z : R),
    distribution_density ta_unit v z = uniform_density_R 0 1 z.
Proof. reflexivity. Qed.

Lemma uniform_cdf_unit_inside :
  forall k : R, (0 <= k)%R -> (k < 1)%R -> uniform_cdf 0 1 k = k.
Proof.
  intros k H0 H1.
  unfold uniform_cdf.
  destruct (Rle_dec k 0) as [H | H].
  - assert (Hk : k = 0%R) by lra; subst k; reflexivity.
  - destruct (Rle_dec 1 k) as [H' | H']; [lra | field].
Qed.

Lemma uniform_cdf_unit_top : uniform_cdf 0 1 1 = 1%R.
Proof.
  unfold uniform_cdf.
  destruct (Rle_dec 1 0) as [H | H]; [lra |].
  destruct (Rle_dec 1 1) as [H' | H']; [reflexivity | lra].
Qed.

Lemma ta_inner_reject :
  forall (v : state) (k : R),
    q_eval [[ integral ta_y ~ $(ta_unit), indicator[$(ta_reject)] ]]
      (update_real v ta_x k) = (1 - uniform_cdf 0 1 k)%R.
Proof.
  intros v k.
  rewrite q_eval_integral.
  transitivity
    (real_integral
       (fun m => uniform_density_R 0 1 m * real_indicator (k <= m)%R)).
  - apply real_integral_extensional; intro m.
    rewrite ta_density_eq.
    cbn [q_eval].
    rewrite ta_indicator_reject.
    reflexivity.
  - apply uniform_integral_survival; lra.
Qed.

Lemma ta_inner_accept :
  forall (t : R) (v : state) (k : R),
    q_eval
      [[ integral ta_y ~ $(ta_unit),
         indicator[$(ta_below t) /\ (~ $(ta_reject))] ]]
      (update_real v ta_x k) =
    (real_indicator (k < t)%R * uniform_cdf 0 1 k)%R.
Proof.
  intros t v k.
  rewrite q_eval_integral.
  transitivity
    (real_indicator (k < t)%R *
     real_integral
       (fun m => uniform_density_R 0 1 m * real_indicator (m < k)%R))%R.
  - rewrite <- real_integral_scale.
    apply real_integral_extensional; intro m.
    rewrite ta_density_eq.
    cbn [q_eval].
    rewrite ta_indicator_accept.
    ring.
  - rewrite uniform_integral_strict_cdf by lra.
    reflexivity.
Qed.

(** * The outer integral is a genuine polynomial integral *)

Lemma ta_qeval_reject :
  forall v : state,
    q_eval
      [[ integral ta_x ~ $(ta_unit),
         integral ta_y ~ $(ta_unit),
         indicator[$(ta_reject)] ]]
      v = (1 / 2)%R.
Proof.
  intro v.
  rewrite q_eval_integral.
  transitivity
    (real_integral
       (fun k =>
          (real_indicator (0 <= k < 1)%R -
           real_indicator (0 <= k < 1)%R * k)%R)).
  - apply real_integral_extensional; intro k.
    rewrite ta_density_eq, ta_inner_reject.
    unfold uniform_density_R.
    destruct (Rlt_dec k 0) as [Hlo | Hlo].
    + rewrite (real_indicator_false (0 <= k <= 1)%R) by (intros [H1 H2]; lra).
      rewrite (real_indicator_false (0 <= k < 1)%R) by (intros [H1 H2]; lra).
      unfold Rdiv; ring.
    + destruct (Rlt_dec k 1) as [Hhi | Hhi].
      * rewrite (real_indicator_true (0 <= k <= 1)%R) by lra.
        rewrite (real_indicator_true (0 <= k < 1)%R) by lra.
        rewrite uniform_cdf_unit_inside by lra.
        field.
      * rewrite (real_indicator_false (0 <= k < 1)%R)
          by (intros [H1 H2]; lra).
        destruct (Rle_dec k 1) as [Heq | Hgt].
        -- assert (Hk : k = 1%R) by lra; subst k.
           rewrite (real_indicator_true (0 <= 1 <= 1)%R) by lra.
           rewrite uniform_cdf_unit_top.
           unfold Rdiv; ring.
        -- rewrite (real_indicator_false (0 <= k <= 1)%R)
             by (intros [H1 H2]; lra).
           unfold Rdiv; ring.
  - rewrite real_integral_minus.
    rewrite (real_integral_indicator_interval 0 1) by lra.
    rewrite (real_integral_indicator_linear 0 1) by lra.
    lra.
Qed.

Lemma ta_qeval_accept :
  forall (t : R) (v : state),
    (0 <= t)%R -> (t <= 1)%R ->
    q_eval
      [[ integral ta_x ~ $(ta_unit),
         integral ta_y ~ $(ta_unit),
         indicator[$(ta_below t) /\ (~ $(ta_reject))] ]] v =
    (t * t / 2)%R.
Proof.
  intros t v H0 H1.
  rewrite q_eval_integral.
  transitivity
    (real_integral (fun k => real_indicator (0 <= k < t)%R * k)).
  - apply real_integral_extensional; intro k.
    rewrite ta_density_eq, (ta_inner_accept t).
    unfold uniform_density_R.
    destruct (Rlt_dec k 0) as [Hlo | Hlo].
    + rewrite (real_indicator_false (0 <= k <= 1)%R) by (intros [Ha Hb]; lra).
      rewrite (real_indicator_false (0 <= k < t)%R) by (intros [Ha Hb]; lra).
      unfold Rdiv; ring.
    + destruct (Rlt_dec k t) as [Hkt | Hkt].
      * rewrite (real_indicator_true (k < t)%R Hkt).
        rewrite (real_indicator_true (0 <= k <= 1)%R) by lra.
        rewrite (real_indicator_true (0 <= k < t)%R) by lra.
        rewrite uniform_cdf_unit_inside by lra.
        field.
      * rewrite (real_indicator_false (k < t)%R) by lra.
        rewrite (real_indicator_false (0 <= k < t)%R)
          by (intros [Ha Hb]; lra).
        unfold Rdiv; ring.
  - rewrite (real_integral_indicator_linear 0 t) by lra.
    field.
Qed.

(** * Certificate data

    One region.  Half the pairs are rejected; of the accepted half, the
    fraction landing below [t] is [t*t]. *)

Definition ta_regions (_ : nat) : CFormula := ta_guard.
Definition ta_transitions (_ _ : nat) : R := 1 / 2.
Definition ta_exits (t : R) (_ : nat) : R := (t * t / 2)%R.
Definition ta_solution (t : R) (_ : nat) : R := (t * t)%R.
Definition ta_q (t : R) : PConstruct := [[ indicator[$(ta_below t)] ]].

Lemma ta_unit_valid_under :
  forall pre : PFormula,
    pformula_valid
      [[ $(pre) -> almost_sure[$(distribution_valid_formula ta_unit)] ]].
Proof.
  intros pre ps.
  cbn [psatisfies]; intro Hignore.
  clear Hignore; revert ps.
  apply p_almost_sure_of_pointwise.
  intro v.
  unfold ta_unit.
  cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
  intro Hle; lra.
Qed.

(** * The body premise *)

Lemma ta_body_step :
  forall (t : R) (i : nat),
    (0 <= t)%R -> (t <= 1)%R -> (i < 1)%nat ->
    {{ $(p_concentrated_mass (ta_regions i) (PConst 1)) }}
      $(ta_body)
    {{ $(while_body_post 1 ta_regions (ta_transitions i) ta_guard (ta_q t)
           (ta_exits t i)) }}.
Proof.
  intros t i H0 H1 Hi.
  unfold ta_body.
  eapply HSeq with
    (eta2 :=
       sample_pformula ta_y ta_unit
         (subst_bool_pformula ta_retry ta_reject
            (while_body_post 1 ta_regions (ta_transitions i) ta_guard
               (ta_q t) (ta_exits t i)))).
  - apply HRealSample; [| apply ta_unit_valid_under].
    intro ps.
    cbn [psatisfies].
    intro Hpre.
    apply psatisfies_p_and in Hpre.
    destruct Hpre as [_ Hmass].
    apply psatisfies_p_eq in Hmass.
    cbn [pterm_eval] in Hmass.
    unfold while_body_post, ta_q, ta_regions, ta_guard, ta_transitions,
      ta_exits.
    cbn [finite_p_and condition_pconstruct condition_pconstruct_fuel
         pconstruct_size].
    rewrite !subst_bool_pformula_p_and, !subst_bool_pformula_p_eq.
    rewrite !sample_pformula_p_and, !sample_pformula_p_eq.
    apply psatisfies_p_and; split; [apply psatisfies_p_and; split | ].
    + apply psatisfies_p_true.
    + apply psatisfies_p_eq.
      cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_cformula
           sample_pterm pterm_eval].
      rewrite !bpv_eq_dec_refl.
      rewrite (t3_expect_const ps _ (1 / 2)%R Hmass);
        [reflexivity | intro v; apply ta_qeval_reject].
    + apply psatisfies_p_eq.
      cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_cformula
           ta_below c_and c_not c_lt sample_pterm pterm_eval].
      rewrite !bpv_eq_dec_refl.
      rewrite (t3_expect_const ps _ (t * t / 2)%R Hmass);
        [reflexivity | intro v; apply ta_qeval_accept; assumption].
  - eapply HSeq with
      (eta2 :=
         subst_bool_pformula ta_retry ta_reject
           (while_body_post 1 ta_regions (ta_transitions i) ta_guard
              (ta_q t) (ta_exits t i))).
    + apply HRealSample; [| apply ta_unit_valid_under].
      intro ps; cbn [psatisfies]; intro H; exact H.
    + apply HBoolAssign.
Qed.

(** * The loop

    [0 < t] strictly: [while_progress] needs the target exit mass
    [t*t/2] to be positive, and it vanishes at [t = 0]. *)

Lemma ta_loop_derivable :
  forall t : R,
    (0 < t)%R -> (t <= 1)%R ->
    {{ $(p_concentrated_mass (ta_regions 0) (PVar ta_w)) }}
      $(ta_loop)
    {{ E[$(condition_pconstruct (ta_q t) (c_not ta_guard))]
         = $(ta_solution t 0) * ta_w }}.
Proof.
  intros t H0 H1.
  assert (Hsq0 : (0 < t * t)%R) by nra.
  assert (Hsq1 : (t * t <= 1)%R) by nra.
  eapply HWhile with
    (m := 1%nat) (k := 0%nat)
    (regions := ta_regions) (solution := ta_solution t)
    (exits := ta_exits t) (transitions := ta_transitions).
  - lia.
  - unfold while_regions_cover, cformula_valid, ta_regions.
    intro v; cbn [finite_c_or c_or c_not satisfies]; tauto.
  - unfold while_regions_in_guard, cformula_valid, ta_regions.
    intros i Hi v; cbn [satisfies]; tauto.
  - unfold while_regions_disjoint; intros i j Hi Hj; lia.
  - unfold while_progress, ta_exits.
    intros i Hi; left; lra.
  - intros i Hi; apply ta_body_step; [lra | lra | exact Hi].
  - unfold while_solution, ta_solution, ta_transitions, ta_exits.
    intros i Hi; cbn [finite_r_sum]; split; lra.
Qed.

(** * The sampler *)

Theorem ta_correct :
  forall t : R,
    (0 < t)%R -> (t <= 1)%R ->
    {{ Pr[true] = ta_w }}
      $(ta_prog)
    {{ E[$(condition_pconstruct (ta_q t) (c_not ta_guard))]
         = $(t * t) * ta_w }}.
Proof.
  intros t H0 H1.
  unfold ta_prog.
  eapply HSeq with
    (eta2 := p_concentrated_mass (ta_regions 0) (PVar ta_w)).
  - eapply HConseq with
      (eta1 :=
         subst_bool_pformula ta_retry c_true
           (p_concentrated_mass (ta_regions 0) (PVar ta_w)))
      (eta2 := p_concentrated_mass (ta_regions 0) (PVar ta_w)).
    + intro ps.
      cbn [psatisfies].
      intro Hpre.
      apply psatisfies_p_eq in Hpre.
      cbn [pterm_eval] in Hpre.
      unfold p_concentrated_mass, ta_regions, ta_guard.
      rewrite subst_bool_pformula_p_and, !subst_bool_pformula_p_eq.
      apply psatisfies_p_and; split; apply psatisfies_p_eq;
        cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_cformula
             pterm_eval].
      * rewrite !bpv_eq_dec_refl; reflexivity.
      * exact Hpre.
    + apply HBoolAssign.
    + intro ps; cbn [psatisfies]; tauto.
  - replace (t * t)%R with (ta_solution t 0) by reflexivity.
    apply ta_loop_derivable; assumption.
Qed.
