(**
  TruncatedLaplaceRejection.v -- truncated-Laplace rejection sampling.

      retry := true;
      while retry do
        x <- sample(Laplace(mu, b));
        retry := (x < a  \/  c <= x)
      end

  Same shape as HalfLaplaceRejection.v -- fresh sample each iteration, one region -- but
  the accepted draw is now conditioned on landing in a window [a, c), so
  the fixed point performs a genuine NORMALIZATION rather than just
  discarding a half-line.

  THE TRIPLE ([t4_correct], for [a < t <= c] and [0 < b], writing [F] for
  the Laplace CDF at [(mu, b)]):

      { E[1_tt] = y }
          t4_prog mu b a c
      { Pr[x < t  /\  ~retry]  =  (F t - F a) / (F c - F a) * y }

  i.e. conditioned on acceptance, [x] has the Laplace law truncated to
  [a, c).  The loop equation is

      s = (1 - (F c - F a)) * s + (F t - F a),

  the retry mass being everything outside the window.

  A NOTE ON THE BOUNDARY.  At [t = a] the correct answer is 0, but the rule
  cannot derive it: [while_progress] demands [0 < exits], and [exits] is the
  TARGET exit mass [F t - F a], which vanishes there.  This is the defect
  where progress should be stated over total exit mass instead.  The
  theorem below therefore assumes [a < t]; [t = a] is not a gap in the
  mathematics but in the rule.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import ClassicalDescription.
From Stdlib Require Import Classical.
Require Import CPHL.
Require Import SampleBeforeLoop.
Require Import HalfLaplaceRejection.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * Small analytic helpers *)

Lemma exp_le_1_of_nonpos :
  forall x : R, (x <= 0)%R -> (exp x <= 1)%R.
Proof.
  intros x Hx.
  replace 1%R with (exp 0) by apply exp_0.
  apply exp_le_compat; exact Hx.
Qed.

Lemma exp_lt_1_of_neg :
  forall x : R, (x < 0)%R -> (exp x < 1)%R.
Proof.
  intros x Hx.
  replace 1%R with (exp 0) by apply exp_0.
  apply exp_increasing; exact Hx.
Qed.

Lemma div_le_compat_r :
  forall x y s : R, (0 < s)%R -> (x <= y)%R -> (x / s <= y / s)%R.
Proof.
  intros x y s Hs Hxy.
  unfold Rdiv.
  apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; exact Hs | exact Hxy].
Qed.

Lemma div_lt_compat_r :
  forall x y s : R, (0 < s)%R -> (x < y)%R -> (x / s < y / s)%R.
Proof.
  intros x y s Hs Hxy.
  unfold Rdiv.
  apply Rmult_lt_compat_r; [apply Rinv_0_lt_compat; exact Hs | exact Hxy].
Qed.

Lemma real_integral_minus :
  forall f g : R -> R,
    real_integral (fun x => (f x - g x)%R) =
    (real_integral f - real_integral g)%R.
Proof.
  intros f g.
  transitivity (real_integral (fun x => (f x + (-1) * g x)%R)).
  - apply real_integral_extensional; intro x; ring.
  - rewrite real_integral_add, real_integral_scale; ring.
Qed.

(** * Monotonicity of the Laplace CDF

    Needed to discharge the certificate's positivity and range obligations
    from an ordering on the window endpoints. *)

Lemma laplace_cdf_le :
  forall loc s u v : R,
    (0 < s)%R -> (u <= v)%R ->
    (laplace_cdf loc s u <= laplace_cdf loc s v)%R.
Proof.
  intros loc s u v Hs Huv.
  unfold laplace_cdf.
  destruct (Rle_dec u loc) as [Hu | Hu]; destruct (Rle_dec v loc) as [Hv | Hv].
  - apply Rmult_le_compat_l; [lra |].
    apply exp_le_compat, div_le_compat_r; lra.
  - assert (H1 : (exp ((u - loc) / s) <= 1)%R).
    { apply exp_le_1_of_nonpos.
      replace 0%R with (0 / s)%R by (field; lra).
      apply div_le_compat_r; lra. }
    assert (H2 : (exp (- (v - loc) / s) <= 1)%R).
    { apply exp_le_1_of_nonpos.
      replace 0%R with (0 / s)%R by (field; lra).
      apply div_le_compat_r; lra. }
    lra.
  - lra.
  - assert (H : (exp (- (v - loc) / s) <= exp (- (u - loc) / s))%R).
    { apply exp_le_compat, div_le_compat_r; lra. }
    lra.
Qed.

Lemma laplace_cdf_lt :
  forall loc s u v : R,
    (0 < s)%R -> (u < v)%R ->
    (laplace_cdf loc s u < laplace_cdf loc s v)%R.
Proof.
  intros loc s u v Hs Huv.
  unfold laplace_cdf.
  destruct (Rle_dec u loc) as [Hu | Hu]; destruct (Rle_dec v loc) as [Hv | Hv].
  - apply Rmult_lt_compat_l; [lra |].
    apply exp_increasing, div_lt_compat_r; lra.
  - assert (H1 : (exp ((u - loc) / s) <= 1)%R).
    { apply exp_le_1_of_nonpos.
      replace 0%R with (0 / s)%R by (field; lra).
      apply div_le_compat_r; lra. }
    assert (H2 : (exp (- (v - loc) / s) < 1)%R).
    { apply exp_lt_1_of_neg.
      replace 0%R with (0 / s)%R by (field; lra).
      apply div_lt_compat_r; lra. }
    lra.
  - lra.
  - assert (H : (exp (- (v - loc) / s) < exp (- (u - loc) / s))%R).
    { apply exp_increasing, div_lt_compat_r; lra. }
    lra.
Qed.

(** Classical readings of the derived connectives, as elsewhere. *)
Lemma t4_satisfies_c_and :
  forall (v : state) (g1 g2 : CFormula),
    satisfies v (c_and g1 g2) <-> (satisfies v g1 /\ satisfies v g2).
Proof.
  intros v g1 g2.
  cbn [c_and c_not satisfies].
  split.
  - intro H.
    destruct (classic (satisfies v g1)) as [H1 | H1].
    + destruct (classic (satisfies v g2)) as [H2 | H2].
      * split; assumption.
      * exfalso; apply H; intros _ H2'; contradiction.
    + exfalso; apply H; intro H1'; contradiction.
  - intros [H1 H2] Hf; exact (Hf H1 H2).
Qed.

(** * The program *)

Definition t4_x : RealProgramVar := real_program_var "t4_x".
Definition t4_retry : BoolProgramVar := bool_program_var "t4_retry".
Definition t4_y : ProbLogicVar := prob_logic_var "t4_y".

Definition t4_noise (mu bb : R) : Distribution := <{ laplace(mu, bb) }>.

(** Reject when the draw falls outside the window [a, c). *)
Definition t4_reject (a c : R) : CFormula :=
  <{ (t4_x < a) \/ (c <= t4_x) }>.

Definition t4_below (t : R) : CFormula := <{ t4_x < t }>.

Definition t4_guard : CFormula := <{ t4_retry }>.

Definition t4_body (mu bb a c : R) : Cmd :=
  <{ t4_x sample $(t4_noise mu bb);
     t4_retry b= $(t4_reject a c) }>.

Definition t4_loop (mu bb a c : R) : Cmd :=
  <{ while $(t4_guard) do $(t4_body mu bb a c) end }>.

Definition t4_prog (mu bb a c : R) : Cmd :=
  <{ t4_retry b= true; $(t4_loop mu bb a c) }>.

Definition t4_F (mu bb u : R) : R := laplace_cdf mu bb u.

(** * The two pointwise indicator identities

    The window is a difference of half-lines, and its complement a disjoint
    union of two -- which is what lets the existing one-sided Laplace
    closed forms cover both integrals. *)

Lemma t4_reject_indicator :
  forall (a c z : R) (v : state),
    (a <= c)%R ->
    real_indicator (satisfies (update_real v t4_x z) (t4_reject a c)) =
    (real_indicator (z < a)%R + real_indicator (c <= z)%R)%R.
Proof.
  intros a c z v Hac.
  assert (Hsat :
    satisfies (update_real v t4_x z) (t4_reject a c) <->
    ((z < a)%R \/ (c <= z)%R)).
  { unfold t4_reject, c_or, c_lt, c_not, update_real, update_real_values.
    cbn [satisfies term_eval real_program_values].
    rewrite !rpv_eq_dec_refl.
    split.
    - intro H.
      destruct (Rlt_dec z a) as [Hz | Hz]; [left; exact Hz |].
      right; apply H; intro Hf; apply Hf; lra.
    - intros [Hz | Hz] Hn.
      + exfalso; apply Hn; intro Ha; lra.
      + exact Hz. }
  rewrite (real_indicator_extensional _ _ Hsat).
  destruct (Rlt_dec z a) as [Hz | Hz].
  - rewrite (real_indicator_true _ (or_introl Hz)).
    rewrite (real_indicator_true (z < a)%R Hz).
    rewrite (real_indicator_false (c <= z)%R) by lra.
    ring.
  - destruct (Rle_dec c z) as [Hc | Hc].
    + rewrite (real_indicator_true _ (or_intror Hc)).
      rewrite (real_indicator_false (z < a)%R) by lra.
      rewrite (real_indicator_true (c <= z)%R Hc).
      ring.
    + rewrite (real_indicator_false _) by (intros [H | H]; lra).
      rewrite (real_indicator_false (z < a)%R) by lra.
      rewrite (real_indicator_false (c <= z)%R) by lra.
      ring.
Qed.

Lemma t4_accept_indicator :
  forall (a c t z : R) (v : state),
    (a <= t)%R -> (t <= c)%R ->
    real_indicator
      (satisfies (update_real v t4_x z)
         (c_and (t4_below t) (c_not (t4_reject a c)))) =
    (real_indicator (z < t)%R - real_indicator (z < a)%R)%R.
Proof.
  intros a c t z v Hat Htc.
  assert (Hsat :
    satisfies (update_real v t4_x z)
      (c_and (t4_below t) (c_not (t4_reject a c))) <->
    ((a <= z)%R /\ (z < t)%R)).
  { rewrite t4_satisfies_c_and.
    unfold t4_below, t4_reject, c_or, c_lt, c_not, update_real,
      update_real_values.
    cbn [satisfies term_eval real_program_values].
    rewrite !rpv_eq_dec_refl.
    split.
    - intros [Hlt Hrej].
      assert (Hzt : (z < t)%R).
      { destruct (Rlt_dec z t) as [Hd | Hd]; [exact Hd |].
        exfalso; apply Hlt; lra. }
      split; [| exact Hzt].
      destruct (Rle_dec a z) as [Ha | Ha]; [exact Ha |].
      exfalso; apply Hrej; intro Hf; exfalso; exact (Hf Ha).
    - intros [Ha Hzt].
      split.
      + intro Hcontra; lra.
      + intro Hor.
        assert (Hcz : (c <= z)%R) by (apply Hor; intro Hf; apply Hf; lra).
        lra. }
  rewrite (real_indicator_extensional _ _ Hsat).
  destruct (Rlt_dec z a) as [Hz | Hz].
  - rewrite (real_indicator_false _) by (intros [H1 H2]; lra).
    rewrite (real_indicator_true (z < t)%R) by lra.
    rewrite (real_indicator_true (z < a)%R Hz).
    ring.
  - destruct (Rlt_dec z t) as [Ht | Ht].
    + rewrite (real_indicator_true _ (conj (Rnot_lt_le _ _ Hz) Ht)).
      rewrite (real_indicator_true (z < t)%R Ht).
      rewrite (real_indicator_false (z < a)%R) by lra.
      ring.
    + rewrite (real_indicator_false _) by (intros [H1 H2]; lra).
      rewrite (real_indicator_false (z < t)%R) by lra.
      rewrite (real_indicator_false (z < a)%R) by lra.
      ring.
Qed.

(** * The two integrals *)

Lemma t4_integral_reject :
  forall (mu bb a c : R) (v : state),
    (0 < bb)%R -> (a <= c)%R ->
    q_eval (QIntegral t4_x (t4_noise mu bb) (QIndicator (t4_reject a c))) v =
    (t4_F mu bb a + (1 - t4_F mu bb c))%R.
Proof.
  intros mu bb a c v Hb Hac.
  cbn [q_eval t4_noise distribution_density term_eval].
  transitivity
    ((real_integral
        (fun z =>
           ((1 / (2 * bb)) * exp (- Rabs (z - mu) / bb)) *
           real_indicator (z < a)%R) +
      real_integral
        (fun z =>
           ((1 / (2 * bb)) * exp (- Rabs (z - mu) / bb)) *
           real_indicator (c <= z)%R))%R).
  - rewrite <- real_integral_add.
    apply real_integral_extensional; intro z.
    rewrite (t4_reject_indicator a c z v Hac).
    ring.
  - rewrite laplace_integral_strict_cdf by exact Hb.
    rewrite laplace_integral_survival by exact Hb.
    unfold t4_F; ring.
Qed.

Lemma t4_integral_accept :
  forall (mu bb a c t : R) (v : state),
    (0 < bb)%R -> (a <= t)%R -> (t <= c)%R ->
    q_eval
      (QIntegral t4_x (t4_noise mu bb)
         (QIndicator (c_and (t4_below t) (c_not (t4_reject a c))))) v =
    (t4_F mu bb t - t4_F mu bb a)%R.
Proof.
  intros mu bb a c t v Hb Hat Htc.
  cbn [q_eval t4_noise distribution_density term_eval].
  transitivity
    ((real_integral
        (fun z =>
           ((1 / (2 * bb)) * exp (- Rabs (z - mu) / bb)) *
           real_indicator (z < t)%R) -
      real_integral
        (fun z =>
           ((1 / (2 * bb)) * exp (- Rabs (z - mu) / bb)) *
           real_indicator (z < a)%R))%R).
  - rewrite <- real_integral_minus.
    apply real_integral_extensional; intro z.
    rewrite (t4_accept_indicator a c t z v Hat Htc).
    ring.
  - rewrite !laplace_integral_strict_cdf by exact Hb.
    unfold t4_F; ring.
Qed.

(** * Certificate data.  One region, as in HalfLaplaceRejection.v. *)

Definition t4_regions (_ : nat) : CFormula := t4_guard.

Definition t4_transitions (mu bb a c : R) (_ _ : nat) : R :=
  (t4_F mu bb a + (1 - t4_F mu bb c))%R.

Definition t4_exits (mu bb a t : R) (_ : nat) : R :=
  (t4_F mu bb t - t4_F mu bb a)%R.

Definition t4_solution (mu bb a c t : R) (_ : nat) : R :=
  ((t4_F mu bb t - t4_F mu bb a) / (t4_F mu bb c - t4_F mu bb a))%R.

Definition t4_q (t : R) : PConstruct := QIndicator (t4_below t).

(** * The body premise *)

Lemma t4_body_step :
  forall mu bb a c t : R,
    (0 < bb)%R -> (a <= t)%R -> (t <= c)%R ->
    forall i : nat,
      (i < 1)%nat ->
      hoare_derivable
        (p_concentrated_mass (t4_regions i) (PConst 1))
        (t4_body mu bb a c)
        (while_body_post 1 t4_regions (t4_transitions mu bb a c i) t4_guard
           (t4_q t) (t4_exits mu bb a t i)).
Proof.
  intros mu bb a c t Hb Hat Htc i Hi.
  assert (Hac : (a <= c)%R) by lra.
  unfold t4_body.
  eapply HSeq with
    (eta2 :=
       subst_bool_pformula t4_retry (t4_reject a c)
         (while_body_post 1 t4_regions (t4_transitions mu bb a c i) t4_guard
            (t4_q t) (t4_exits mu bb a t i))).
  - apply HRealSample.
    + intro ps.
    + intro Hadm.
      cbn [psatisfies].
      intro Hpre.
      apply psatisfies_p_and in Hpre.
      destruct Hpre as [_ Hmass].
      apply psatisfies_p_eq in Hmass.
      cbn [pterm_eval] in Hmass.
      unfold while_body_post, t4_q, t4_regions, t4_guard, t4_transitions,
        t4_exits.
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
        rewrite (t3_expect_const ps _
                   (t4_F mu bb a + (1 - t4_F mu bb c))%R Hmass);
          [reflexivity | intro v; apply t4_integral_reject; assumption].
      * apply psatisfies_p_eq.
        cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_cformula
             t4_below c_and c_not].
        rewrite !bpv_eq_dec_refl.
        cbn [sample_pterm pterm_eval].
        rewrite (t3_expect_const ps _
                   (t4_F mu bb t - t4_F mu bb a)%R Hmass);
          [reflexivity | intro v; apply t4_integral_accept; assumption].
    + intros ps _.
      revert ps.
      apply p_almost_sure_of_pointwise.
      intro v.
      unfold t4_noise.
      cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
      intro Hle; lra.
  - apply HBoolAssign.
Qed.

(** * The loop

    [a < t] is required, not merely [a <= t]: [while_progress] needs the
    TARGET exit mass [F t - F a] to be positive.  At [t = a] the true answer
    is 0 and the rule cannot reach it. *)

Lemma t4_loop_derivable :
  forall mu bb a c t : R,
    (0 < bb)%R -> (a < t)%R -> (t <= c)%R ->
    hoare_derivable
      (p_concentrated_mass (t4_regions 0) (PVar t4_y))
      (t4_loop mu bb a c)
      (p_eq (PExpect (condition_pconstruct (t4_q t) (c_not t4_guard)))
         (PMul (PConst (t4_solution mu bb a c t 0)) (PVar t4_y))).
Proof.
  intros mu bb a c t Hb Hat Htc.
  assert (HN : (0 < t4_F mu bb t - t4_F mu bb a)%R).
  { unfold t4_F.
    pose proof (laplace_cdf_lt mu bb a t Hb Hat); lra. }
  assert (HD : (0 < t4_F mu bb c - t4_F mu bb a)%R).
  { unfold t4_F.
    pose proof (laplace_cdf_lt mu bb a c Hb ltac:(lra)); lra. }
  assert (HND : (t4_F mu bb t - t4_F mu bb a
                 <= t4_F mu bb c - t4_F mu bb a)%R).
  { unfold t4_F.
    pose proof (laplace_cdf_le mu bb t c Hb Htc); lra. }
  eapply HWhile with
    (m := 1%nat) (k := 0%nat)
    (regions := t4_regions) (solution := t4_solution mu bb a c t)
    (exits := t4_exits mu bb a t) (transitions := t4_transitions mu bb a c).
  - lia.
  - unfold while_regions_cover, cformula_valid, t4_regions.
    intro v; cbn [finite_c_or c_or c_not satisfies]; tauto.
  - unfold while_regions_in_guard, cformula_valid, t4_regions.
    intros i Hi v; cbn [satisfies]; tauto.
  - unfold while_regions_disjoint; intros i j Hi Hj; lia.
  - unfold while_progress, t4_exits.
    intros i Hi; left; lra.
  - apply t4_body_step; [exact Hb | lra | exact Htc].
  - unfold while_solution, t4_solution, t4_transitions, t4_exits.
    intros i Hi.
    cbn [finite_r_sum].
    assert (Hval :
      ((t4_F mu bb t - t4_F mu bb a) / (t4_F mu bb c - t4_F mu bb a) *
       (t4_F mu bb c - t4_F mu bb a))%R =
      (t4_F mu bb t - t4_F mu bb a)%R) by (field; lra).
    split.
    + field; lra.
    + split.
      * apply Rmult_le_reg_r
          with (r := (t4_F mu bb c - t4_F mu bb a)%R); [lra |].
        rewrite Hval; lra.
      * apply Rmult_le_reg_r
          with (r := (t4_F mu bb c - t4_F mu bb a)%R); [lra |].
        rewrite Hval; lra.
Qed.

(** * The sampler *)

Theorem t4_correct :
  forall mu bb a c t : R,
    (0 < bb)%R -> (a < t)%R -> (t <= c)%R ->
    {{ Pr[true] = t4_y }}
      $(t4_prog mu bb a c)
    {{ E[$(condition_pconstruct (t4_q t) (c_not t4_guard))]
         = $((t4_F mu bb t - t4_F mu bb a) /
             (t4_F mu bb c - t4_F mu bb a)) * t4_y }}.
Proof.
  intros mu bb a c t Hb Hat Htc.
  unfold t4_prog.
  eapply HSeq with
    (eta2 := p_concentrated_mass (t4_regions 0) (PVar t4_y)).
  - eapply HConseq with
      (eta1 :=
         subst_bool_pformula t4_retry c_true
           (p_concentrated_mass (t4_regions 0) (PVar t4_y)))
      (eta2 := p_concentrated_mass (t4_regions 0) (PVar t4_y)).
    + intro ps.
    + intro Hadm.
      cbn [psatisfies].
      intro Hpre.
      apply psatisfies_p_eq in Hpre.
      cbn [pterm_eval] in Hpre.
      unfold p_concentrated_mass, t4_regions, t4_guard.
      rewrite subst_bool_pformula_p_and, !subst_bool_pformula_p_eq.
      apply psatisfies_p_and; split; apply psatisfies_p_eq;
        cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_cformula
             pterm_eval].
      * rewrite !bpv_eq_dec_refl; reflexivity.
      * exact Hpre.
    + apply HBoolAssign.
    + intro ps; cbn [psatisfies]; tauto.
  - apply t4_loop_derivable; assumption.
Qed.
