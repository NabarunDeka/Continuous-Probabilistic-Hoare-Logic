(**
  HalfLaplaceRejection.v -- the half-Laplace rejection sampler.

      retry := true;
      while retry do
        x <- sample(Laplace(0, b));
        retry := (x < 0)
      end

  Sampling happens INSIDE the loop, freshly on every iteration.  That is
  what makes this work where PersistentSampleLoop.v did not: a sample that persists across
  iterations forces the regions to pin it, and then the loop can never be
  entered (see [t2_split_blocks_entry]).  A sample redrawn each iteration
  leaves the one-step transition and exit probabilities constant, which is
  exactly what [HWhile]'s body premise demands.

  THE TRIPLE ([t3_correct], for every threshold [0 <= t] and scale [0 < b]):

      { E[1_tt] = y }
          t3_prog b
      { Pr[t <= x  /\  ~retry] = exp(-t/b) * y }

  Reading: conditioned on acceptance, the sampler returns the positive half
  of a Laplace, i.e. an Exponential(1/b) -- its survival function is exactly
  [exp(-t/b)].  At [t = 0] this specialises to almost-sure termination.

  The loop equation is scalar:  s = (1/2) * s + (1/2) * exp(-t/b),
  whose solution is [exp(-t/b)].  Half the mass is rejected each round; of
  the accepted half, a fraction [exp(-t/b)] lands above [t].

  No new axioms: the two integrals come from [laplace_integral_strict_cdf]
  and [laplace_integral_survival], both already proved in CPHL.v.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import ClassicalDescription.
From Stdlib Require Import Classical.
Require Import CPHL.
Require Import SampleBeforeLoop.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * Analytic facts *)

Lemma exp_le_compat :
  forall x y : R, (x <= y)%R -> (exp x <= exp y)%R.
Proof.
  intros x y Hxy.
  destruct (Rle_lt_or_eq_dec x y Hxy) as [Hlt | Heq].
  - left; apply exp_increasing; exact Hlt.
  - right; rewrite Heq; reflexivity.
Qed.

Lemma rpv_eq_dec_refl :
  forall (x : RealProgramVar) (A : Type) (a c : A),
    (if real_program_var_eq_dec x x then a else c) = a.
Proof.
  intros x A a c.
  destruct (real_program_var_eq_dec x x) as [_ | Hne];
    [reflexivity | contradiction].
Qed.

(** The upper tail of a centred Laplace.  Both branches of [laplace_cdf]
    collapse to the same closed form on [0 <= t]. *)
Lemma laplace_tail_centred :
  forall t b : R,
    (0 <= t)%R -> (0 < b)%R ->
    (1 - laplace_cdf 0 b t)%R = ((1 / 2) * exp (- t / b))%R.
Proof.
  intros t b Ht Hb.
  unfold laplace_cdf.
  destruct (Rle_dec t 0) as [Hle | Hgt].
  - assert (Ht0 : t = 0%R) by lra.
    subst t.
    replace ((0 - 0) / b)%R with 0%R by (field; lra).
    replace (- 0 / b)%R with 0%R by (field; lra).
    rewrite exp_0; lra.
  - replace (- (t - 0) / b)%R with (- t / b)%R by (field; lra).
    lra.
Qed.

Lemma laplace_cdf_centre :
  forall b : R, (0 < b)%R -> laplace_cdf 0 b 0 = (1 / 2)%R.
Proof.
  intros b Hb.
  pose proof (laplace_tail_centred 0 b (Rle_refl 0) Hb) as H.
  replace (- 0 / b)%R with 0%R in H by (field; lra).
  rewrite exp_0 in H; lra.
Qed.

(** * The program *)

Definition t3_x : RealProgramVar := real_program_var "t3_x".
Definition t3_retry : BoolProgramVar := bool_program_var "t3_retry".
Definition t3_y : ProbLogicVar := prob_logic_var "t3_y".

Definition t3_noise (b : R) : Distribution := <{ laplace(0, b) }>.

(** The rejection test: retry exactly when the draw was negative. *)
Definition t3_neg : CFormula := <{ t3_x < 0 }>.

(** The event whose probability we compute: the accepted draw is at least t. *)
Definition t3_tail (t : R) : CFormula := <{ t <= t3_x }>.

Definition t3_guard : CFormula := <{ t3_retry }>.

Definition t3_body (b : R) : Cmd :=
  <{ t3_x sample $(t3_noise b);
     t3_retry b= $(t3_neg) }>.

Definition t3_loop (b : R) : Cmd :=
  <{ while $(t3_guard) do $(t3_body b) end }>.

Definition t3_prog (b : R) : Cmd :=
  <{ t3_retry b= true; $(t3_loop b) }>.

(** * Certificate data.  One region: the guard itself. *)

Definition t3_regions (_ : nat) : CFormula := t3_guard.
Definition t3_transitions (_ _ : nat) : R := 1 / 2.
Definition t3_exits (t b : R) (_ : nat) : R := ((1 / 2) * exp (- t / b))%R.
Definition t3_solution (t b : R) (_ : nat) : R := exp (- t / b).
Definition t3_q (t : R) : PConstruct := [[ indicator[$(t3_tail t)] ]].

(** * The two integrals produced by the sample

    Both are instances of the Laplace closed forms already in CPHL.v. *)

Lemma t3_integral_reject :
  forall (b : R) (v : state),
    (0 < b)%R ->
    q_eval [[ integral t3_x ~ $(t3_noise b), indicator[$(t3_neg)] ]] v =
    (1 / 2)%R.
Proof.
  intros b v Hb.
  cbn [q_eval t3_noise distribution_density term_eval].
  rewrite (real_integral_extensional
             _ (fun z =>
                  ((1 / (2 * b)) * exp (- Rabs (z - 0) / b)) *
                  real_indicator (z < 0)%R)).
  - rewrite laplace_integral_strict_cdf by exact Hb.
    apply laplace_cdf_centre; exact Hb.
  - intro z.
    unfold t3_neg, c_lt, update_real, update_real_values.
    cbn [q_eval satisfies c_not term_eval real_program_values].
    rewrite rpv_eq_dec_refl.
    rewrite (real_indicator_extensional _ (z < 0)%R) by lra.
    ring.
Qed.

Lemma t3_integral_accept :
  forall (t b : R) (v : state),
    (0 <= t)%R -> (0 < b)%R ->
    q_eval
      [[ integral t3_x ~ $(t3_noise b),
         indicator[$(t3_tail t) /\ (~ $(t3_neg))] ]] v =
    ((1 / 2) * exp (- t / b))%R.
Proof.
  intros t b v Ht Hb.
  cbn [q_eval t3_noise distribution_density term_eval].
  rewrite (real_integral_extensional
             _ (fun z =>
                  ((1 / (2 * b)) * exp (- Rabs (z - 0) / b)) *
                  real_indicator (t <= z)%R)).
  - rewrite laplace_integral_survival by exact Hb.
    apply laplace_tail_centred; assumption.
  - intro z.
    unfold t3_tail, t3_neg, c_lt, c_and, c_not, update_real,
      update_real_values.
    cbn [q_eval satisfies term_eval real_program_values].
    rewrite !rpv_eq_dec_refl.
    rewrite (real_indicator_extensional _ (t <= z)%R).
    + ring.
    + split.
      * intro H.
        destruct (Rle_dec t z) as [Hz | Hz]; [exact Hz |].
        exfalso; apply H; intros Hle Hcontra; lra.
      * intros Hz Hf; apply (Hf Hz); intro Hneg; lra.
Qed.

(** * The body premise

    One [toss]-free iteration: sample, then recompute [retry].  Because the
    sample is fresh, both resulting expectations are CONSTANTS -- they do
    not depend on the incoming measure at all beyond its total mass.  That
    is the whole reason this loop is in range of [HWhile]. *)

Lemma t3_expect_const :
  forall (ps : Pstate) (q : PConstruct) (c : R),
    expectation (pstate_measure ps) (q_eval (QIndicator c_true)) = 1%R ->
    (forall v : state, q_eval q v = c) ->
    expectation (pstate_measure ps) (q_eval q) = c.
Proof.
  intros ps q c Hnorm Hval.
  transitivity (expectation (pstate_measure ps) (fun _ : state => c)).
  - apply expectation_extensional; exact Hval.
  - rewrite expectation_constant, Hnorm; ring.
Qed.

Lemma t3_body_step :
  forall t b : R,
    (0 <= t)%R -> (0 < b)%R ->
    forall i : nat,
      (i < 1)%nat ->
      {{ $(p_concentrated_mass (t3_regions i) (PConst 1)) }}
        $(t3_body b)
      {{ $(while_body_post 1 t3_regions (t3_transitions i) t3_guard (t3_q t)
             (t3_exits t b i)) }}.
Proof.
  intros t b Ht Hb i Hi.
  unfold t3_body.
  eapply HSeq with
    (eta2 :=
       subst_bool_pformula t3_retry t3_neg
         (while_body_post 1 t3_regions (t3_transitions i) t3_guard (t3_q t)
            (t3_exits t b i))).
  - apply HRealSample.
    + intro ps.
    + intro Hadm.
      cbn [psatisfies].
      intro Hpre.
      apply psatisfies_p_and in Hpre.
      destruct Hpre as [_ Hmass].
      apply psatisfies_p_eq in Hmass.
      cbn [pterm_eval] in Hmass.
      unfold while_body_post, t3_q, t3_regions, t3_guard, t3_transitions,
        t3_exits.
      cbn [finite_p_and condition_pconstruct condition_pconstruct_fuel
           pconstruct_size].
      rewrite !subst_bool_pformula_p_and, !subst_bool_pformula_p_eq.
      rewrite !sample_pformula_p_and, !sample_pformula_p_eq.
      apply psatisfies_p_and; split;
        [apply psatisfies_p_and; split | ].
      * apply psatisfies_p_true.
      * apply psatisfies_p_eq.
        cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_cformula].
        rewrite !bpv_eq_dec_refl.
        cbn [sample_pterm pterm_eval].
        rewrite (t3_expect_const ps _ (1 / 2)%R Hmass);
          [reflexivity | intro v; apply t3_integral_reject; exact Hb].
      * apply psatisfies_p_eq.
        cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_cformula
             t3_tail c_and c_not].
        rewrite !bpv_eq_dec_refl.
        cbn [sample_pterm pterm_eval].
        rewrite (t3_expect_const ps _ ((1 / 2) * exp (- t / b))%R Hmass);
          [reflexivity | intro v; apply t3_integral_accept; assumption].
    + intros ps _.
      revert ps.
      apply p_almost_sure_of_pointwise.
      intro v.
      unfold t3_noise.
      cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
      intro Hle; lra.
  - apply HBoolAssign.
Qed.

(** * The loop *)

Lemma t3_loop_derivable :
  forall t b : R,
    (0 <= t)%R -> (0 < b)%R ->
    {{ $(p_concentrated_mass (t3_regions 0) (PVar t3_y)) }}
      $(t3_loop b)
    {{ E[$(condition_pconstruct (t3_q t) (c_not t3_guard))]
         = $(t3_solution t b 0) * t3_y }}.
Proof.
  intros t b Ht Hb.
  assert (Hpos : (0 < exp (- t / b))%R) by apply exp_pos.
  assert (Hle1 : (exp (- t / b) <= 1)%R).
  { replace 1%R with (exp 0) by apply exp_0.
    apply exp_le_compat.
    assert (Hq : (0 <= t * / b)%R).
    { apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; lra]. }
    unfold Rdiv.
    replace (- t * / b)%R with (- (t * / b))%R by ring.
    lra. }
  eapply HWhile with
    (m := 1%nat) (k := 0%nat)
    (regions := t3_regions) (solution := t3_solution t b)
    (exits := t3_exits t b) (transitions := t3_transitions).
  - lia.
  - unfold while_regions_cover, cformula_valid, t3_regions.
    intro v; cbn [finite_c_or c_or c_not satisfies]; tauto.
  - unfold while_regions_in_guard, cformula_valid, t3_regions.
    intros i Hi v; cbn [satisfies]; tauto.
  - unfold while_regions_disjoint; intros i j Hi Hj; lia.
  - unfold while_progress, t3_exits.
    intros i Hi; left; lra.
  - apply t3_body_step; assumption.
  - unfold while_solution, t3_solution, t3_transitions, t3_exits.
    intros i Hi; cbn [finite_r_sum]; split; lra.
Qed.

(** * The whole sampler

    [retry := true] concentrates all mass on the single region, so unlike
    PersistentSampleLoop.v the loop can actually be entered. *)

Theorem t3_correct :
  forall t b : R,
    (0 <= t)%R -> (0 < b)%R ->
    {{ Pr[true] = t3_y }}
      $(t3_prog b)
    {{ E[$(condition_pconstruct (t3_q t) (c_not t3_guard))]
         = $(exp (- t / b)) * t3_y }}.
Proof.
  intros t b Ht Hb.
  unfold t3_prog.
  eapply HSeq with
    (eta2 := p_concentrated_mass (t3_regions 0) (PVar t3_y)).
  - eapply HConseq with
      (eta1 :=
         subst_bool_pformula t3_retry c_true
           (p_concentrated_mass (t3_regions 0) (PVar t3_y)))
      (eta2 := p_concentrated_mass (t3_regions 0) (PVar t3_y)).
    + intro ps.
    + intro Hadm.
      cbn [psatisfies].
      intro Hpre.
      apply psatisfies_p_eq in Hpre.
      cbn [pterm_eval] in Hpre.
      unfold p_concentrated_mass, t3_regions, t3_guard.
      rewrite subst_bool_pformula_p_and, !subst_bool_pformula_p_eq.
      apply psatisfies_p_and; split; apply psatisfies_p_eq;
        cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_cformula
             pterm_eval].
      * rewrite !bpv_eq_dec_refl; reflexivity.
      * exact Hpre.
    + apply HBoolAssign.
    + intro ps; cbn [psatisfies]; tauto.
  - apply t3_loop_derivable; assumption.
Qed.

(** At [t = 0] the tail probability is [exp 0 = 1]: all the mass that
    enters the loop eventually leaves it, so the sampler terminates almost
    surely.  Note this is the SAME theorem, not a separate argument -- the
    fixed point already carries it. *)
Corollary t3_terminates :
  forall b : R,
    (0 < b)%R ->
    {{ Pr[true] = t3_y }}
      $(t3_prog b)
    {{ E[$(condition_pconstruct (t3_q 0) (c_not t3_guard))] = $(1%R) * t3_y }}.
Proof.
  intros b Hb.
  replace 1%R with (exp (- 0 / b)).
  - apply t3_correct; [apply Rle_refl | exact Hb].
  - replace (- 0 / b)%R with 0%R by (field; lra).
    apply exp_0.
Qed.
