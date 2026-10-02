(**
  SampleBeforeLoop.v -- a continuous sample taken BEFORE a discrete loop.

  TEST 1: continuous sampling OUTSIDE a while loop.

      x <- sample(Laplace(0, s));
      b <- ff;
      while ~b do toss(b, 1/2)

  THE TRIPLE ([t1_correct], for [0 < s]):

      { E[1_tt] = y }   t1_prog s   { Pr[b] = 1 * y }

  All the initial mass ends up with [b] true -- the loop terminates almost
  surely, and the sampled [x] is carried along untouched.

  This is the DiPWhile "bounded assignments" shape: no real variable is
  assigned inside the loop.  It composes [HRealSample], [HBoolAssign] and
  [HWhile] in one derivation, and it is the smallest program that does so.

  The loop is deliberately independent of [x].  That is forced, not chosen:
  [HWhile]'s precondition [p_concentrated_mass] demands the whole measure sit
  in a single region, so if the guard read [x] the post-sample measure --
  spread across [x < 0] and [0 <= x] -- could never enter the loop.  Fixing
  that needs the unimplemented [SUM] rule.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import ClassicalDescription.
From Stdlib Require Import Classical.
Require Import CPHL.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * Reusable helpers

    None of these are specific to the test; they are the small facts any
    calculation in this logic needs and that [CPHL.v] does not yet export. *)

(** ** Unfolding the derived connectives

    [p_and] and [p_eq] are encoded through negation and implication, so
    [psatisfies] on them is a nest of arrows.  These turn that back into
    ordinary conjunction and equality.  Both need classical reasoning. *)

Lemma psatisfies_p_and :
  forall (ps : Pstate) (eta1 eta2 : PFormula),
    psatisfies ps (p_and eta1 eta2) <->
    (psatisfies ps eta1 /\ psatisfies ps eta2).
Proof.
  intros ps eta1 eta2.
  unfold p_and, p_not.
  cbn [psatisfies].
  split.
  - intro H.
    destruct (classic (psatisfies ps eta1)) as [H1 | H1].
    + destruct (classic (psatisfies ps eta2)) as [H2 | H2].
      * split; assumption.
      * exfalso; apply H; intros _ H2'; contradiction.
    + exfalso; apply H; intro H1'; contradiction.
  - intros [H1 H2] Hf; exact (Hf H1 H2).
Qed.

Lemma psatisfies_p_eq :
  forall (ps : Pstate) (p1 p2 : Pterm),
    psatisfies ps (p_eq p1 p2) <-> pterm_eval p1 ps = pterm_eval p2 ps.
Proof.
  intros ps p1 p2.
  unfold p_eq.
  rewrite psatisfies_p_and.
  cbn [psatisfies].
  split.
  - intros [H1 H2]; apply Rle_antisym; assumption.
  - intro H; rewrite H; split; apply Rle_refl.
Qed.

Lemma psatisfies_p_true :
  forall ps : Pstate, psatisfies ps p_true.
Proof.
  intro ps; unfold p_true; cbn [psatisfies]; tauto.
Qed.

(** ** Discharging a decidable-equality test against itself

    [subst_bool_*] leaves [if bool_program_var_eq_dec b b then _ else _] in
    the goal, and [cbn] will not reduce it because the variable is an opaque
    definition.  This retires it without computation. *)
Lemma bpv_eq_dec_refl :
  forall (b : BoolProgramVar) (A : Type) (x y : A),
    (if bool_program_var_eq_dec b b then x else y) = x.
Proof.
  intros b A x y.
  destruct (bool_program_var_eq_dec b b) as [_ | Hne];
    [reflexivity | contradiction].
Qed.

(** ** Expectations of indicators that are constant *)

Lemma expect_indicator_unsat :
  forall (mu : Measure) (gamma : CFormula),
    (forall v : state, ~ satisfies v gamma) ->
    expectation mu (q_eval (QIndicator gamma)) = 0.
Proof.
  intros mu gamma Hno.
  rewrite expectation_indicator.
  rewrite <- (measure_empty mu).
  apply measure_extensional.
  intro v; unfold formula_assertion.
  split; [intro Hs; exact (Hno v Hs) | contradiction].
Qed.

Lemma expect_indicator_valid :
  forall (mu : Measure) (gamma : CFormula),
    (forall v : state, satisfies v gamma) ->
    expectation mu (q_eval (QIndicator gamma)) =
    expectation mu (q_eval (QIndicator c_true)).
Proof.
  intros mu gamma Hall.
  rewrite !expectation_indicator.
  apply measure_extensional.
  intro v; unfold formula_assertion; cbn [c_true satisfies].
  split; intro H; [tauto | apply Hall].
Qed.

(** A classical formula true at every valuation holds almost surely. *)
Lemma p_almost_sure_of_pointwise :
  forall gamma : CFormula,
    (forall v : state, satisfies v gamma) ->
    pformula_valid (p_almost_sure gamma).
Proof.
  intros gamma Hall ps Hadm.
  unfold p_almost_sure.
  apply psatisfies_p_eq.
  cbn [pterm_eval].
  apply expect_indicator_valid; exact Hall.
Qed.

(** ** The Laplace density integrates to one

    Derivable rather than assumed: split the line at 0 and add the CDF and
    survival closed forms already proved in [CPHL.v]. *)
Lemma laplace_density_total :
  forall location scale : R,
    (0 < scale)%R ->
    real_integral
      (fun z => (1 / (2 * scale)) * exp (- Rabs (z - location) / scale)) = 1.
Proof.
  intros location scale Hscale.
  transitivity
    (real_integral
       (fun z =>
          ((1 / (2 * scale)) * exp (- Rabs (z - location) / scale)) *
          real_indicator (z < 0)%R) +
     real_integral
       (fun z =>
          ((1 / (2 * scale)) * exp (- Rabs (z - location) / scale)) *
          real_indicator (0 <= z)%R))%R.
  - rewrite <- real_integral_add.
    apply real_integral_extensional; intro z.
    destruct (Rlt_dec z 0) as [Hz | Hz].
    + rewrite (real_indicator_true _ Hz).
      rewrite (real_indicator_false (0 <= z)%R) by lra.
      ring.
    + rewrite (real_indicator_false (z < 0)%R) by lra.
      rewrite (real_indicator_true (0 <= z)%R) by lra.
      ring.
  - rewrite laplace_integral_strict_cdf by exact Hscale.
    rewrite laplace_integral_survival by exact Hscale.
    ring.
Qed.

(** ** The transformers commute with the derived connectives

    [p_and] and [p_eq] are transparent, and every transformer recurses
    structurally, so these hold by computation.  Rewriting with them is far
    more robust than steering [cbn] through the encoding. *)

Lemma subst_bool_pformula_p_and :
  forall (b : BoolProgramVar) (beta : CFormula) (e1 e2 : PFormula),
    subst_bool_pformula b beta (p_and e1 e2) =
    p_and (subst_bool_pformula b beta e1) (subst_bool_pformula b beta e2).
Proof. reflexivity. Qed.

Lemma subst_bool_pformula_p_eq :
  forall (b : BoolProgramVar) (beta : CFormula) (p1 p2 : Pterm),
    subst_bool_pformula b beta (p_eq p1 p2) =
    p_eq (subst_bool_pterm b beta p1) (subst_bool_pterm b beta p2).
Proof. reflexivity. Qed.

Lemma sample_pformula_p_and :
  forall (x : RealProgramVar) (d : Distribution) (e1 e2 : PFormula),
    sample_pformula x d (p_and e1 e2) =
    p_and (sample_pformula x d e1) (sample_pformula x d e2).
Proof. reflexivity. Qed.

Lemma sample_pformula_p_eq :
  forall (x : RealProgramVar) (d : Distribution) (p1 p2 : Pterm),
    sample_pformula x d (p_eq p1 p2) =
    p_eq (sample_pterm x d p1) (sample_pterm x d p2).
Proof. reflexivity. Qed.

(** Sampling a valid Laplace and then testing a formula that holds
    everywhere returns the whole mass: the inner integral is the total
    density, which is one. *)
Lemma expect_laplace_integral_valid :
  forall (mu : Measure) (x : RealProgramVar) (loc sc : R) (gamma : CFormula),
    (0 < sc)%R ->
    (forall v : state, satisfies v gamma) ->
    expectation mu
      (q_eval (QIntegral x (Laplace (TConst loc) (TConst sc))
                 (QIndicator gamma)))
    = expectation mu (q_eval (QIndicator c_true)).
Proof.
  intros mu x loc sc gamma Hsc Hall.
  transitivity (expectation mu (fun _ : state => 1%R)).
  - apply expectation_extensional; intro v.
    cbn [q_eval distribution_density term_eval].
    rewrite (real_integral_extensional
               _ (fun z => (1 / (2 * sc)) * exp (- Rabs (z - loc) / sc)))
      by (intro z; rewrite real_indicator_true by apply Hall; ring).
    apply laplace_density_total; exact Hsc.
  - rewrite expectation_constant; ring.
Qed.

(** * TEST 1 *)

Definition t1_x : RealProgramVar := real_program_var "t1_x".
Definition t1_b : BoolProgramVar := bool_program_var "t1_b".
Definition t1_y : ProbLogicVar := prob_logic_var "t1_y".

Definition t1_noise (s : R) : Distribution := <{ laplace(0, s) }>.

Definition t1_guard : CFormula := <{ ~ t1_b }>.

Definition t1_body : Cmd := <{ t1_b toss $(1 / 2) }>.

Definition t1_loop : Cmd := <{ while $(t1_guard) do $(t1_body) end }>.

Definition t1_prog (s : R) : Cmd :=
  <{ t1_x sample $(t1_noise s);
     t1_b b= false;
     $(t1_loop) }>.

(** ** Certificate data for [HWhile]

    One region -- the guard itself.  A single toss leaves the guard with
    probability 1/2 and exits with probability 1/2, so the linear system is
    [x = x/2 + 1/2], whose bounded solution is 1: the loop terminates almost
    surely. *)

Definition t1_regions (_ : nat) : CFormula := t1_guard.
Definition t1_transitions (_ _ : nat) : R := 1 / 2.
Definition t1_exits (_ : nat) : R := 1 / 2.
Definition t1_solution (_ : nat) : R := 1.
Definition t1_q : PConstruct := QIndicator c_true.

(** ** The loop body

    One [toss] overwrites [b] outright, so the transition and exit
    probabilities depend only on the total mass -- not on how the incoming
    measure distributes [b] or [x].  That is what lets the body premise fix
    them to literal constants. *)

Lemma t1_body_step :
  forall i : nat,
    (i < 1)%nat ->
    hoare_derivable
      (p_concentrated_mass (t1_regions i) (PConst 1))
      t1_body
      (while_body_post 1 t1_regions (t1_transitions i) t1_guard t1_q
         (t1_exits i)).
Proof.
  intros i Hi.
  eapply HConseq with
    (eta1 :=
       toss_pformula t1_b (1 / 2)
         (while_body_post 1 t1_regions (t1_transitions i) t1_guard t1_q
            (t1_exits i)))
    (eta2 :=
       while_body_post 1 t1_regions (t1_transitions i) t1_guard t1_q
         (t1_exits i)).
  - (* the concentrated-mass precondition implies the tossed postcondition *)
    intro ps.
    intro Hadm.
    intro Hadm.
    cbn [psatisfies].
    intro Hpre.
    apply psatisfies_p_and in Hpre.
    destruct Hpre as [_ Hmass].
    apply psatisfies_p_eq in Hmass.
    cbn [pterm_eval] in Hmass.
    unfold while_body_post, t1_regions, t1_transitions, t1_exits, t1_q,
      t1_guard.
    cbn [finite_p_and toss_pformula toss_pterm].
    apply psatisfies_p_and; split.
    + apply psatisfies_p_and; split.
      * apply psatisfies_p_true.
      * apply psatisfies_p_eq.
        cbn [pterm_eval toss_pterm subst_bool_pconstruct
             subst_bool_cformula c_not].
        rewrite !bpv_eq_dec_refl.
        rewrite (expect_indicator_unsat _ (FImpl c_true FFalse))
          by (intro v; cbn [c_true satisfies]; tauto).
        rewrite (expect_indicator_valid _ (FImpl FFalse FFalse))
          by (intro v; cbn [satisfies]; tauto).
        lra.
    + apply psatisfies_p_eq.
      cbn [pterm_eval toss_pterm condition_pconstruct
           condition_pconstruct_fuel pconstruct_size subst_bool_pconstruct
           subst_bool_cformula c_and c_not].
      rewrite !bpv_eq_dec_refl.
      rewrite (expect_indicator_valid _
                 (c_and c_true (c_not (c_not c_true))))
        by (intro v; cbn [c_true c_and c_not satisfies]; tauto).
      rewrite (expect_indicator_unsat _
                 (c_and c_true (c_not (c_not FFalse))))
        by (intro v; cbn [c_true c_and c_not satisfies]; tauto).
      lra.
  - apply HBoolToss.
    unfold coin_probability_valid; lra.
  - intro ps; cbn [psatisfies]; tauto.
Qed.

(** ** The loop *)

Lemma t1_loop_derivable :
  hoare_derivable
    (p_concentrated_mass (t1_regions 0) (PVar t1_y))
    t1_loop
    (p_eq (PExpect (condition_pconstruct t1_q (c_not t1_guard)))
       (PMul (PConst (t1_solution 0)) (PVar t1_y))).
Proof.
  eapply HWhile with
    (m := 1%nat) (k := 0%nat)
    (regions := t1_regions) (solution := t1_solution)
    (exits := t1_exits) (transitions := t1_transitions).
  - lia.
  - unfold while_regions_cover, cformula_valid, t1_regions.
    intro v; cbn [finite_c_or c_or c_not satisfies]; tauto.
  - unfold while_regions_in_guard, cformula_valid, t1_regions.
    intros i Hi v; cbn [satisfies]; tauto.
  - unfold while_regions_disjoint; intros i j Hi Hj; lia.
  - unfold while_progress, t1_exits; intros i Hi; left; lra.
  - exact t1_body_step.
  - unfold while_solution, t1_solution, t1_transitions, t1_exits.
    intros i Hi; cbn [finite_r_sum]; split; lra.
Qed.

(** ** The whole program

    Precondition: the initial mass is [y].  Conclusion: all of it ends up
    with [b] true.  The rigid [y] stays in the conclusion because [HWhile]
    produces it there and no rule instantiates a rigid variable appearing in
    a postcondition -- the same shape PHL's loop theorems use. *)

Definition t1_pre : PFormula := [[ Pr[true] = t1_y ]].

Definition t1_post : PFormula :=
  [[ E[$(condition_pconstruct t1_q (c_not t1_guard))]
       = $(t1_solution 0) * t1_y ]].

Theorem t1_correct :
  forall s : R,
    (0 < s)%R ->
    {{ $(t1_pre) }} $(t1_prog s) {{ $(t1_post) }}.
Proof.
  intros s Hs.
  unfold t1_prog.
  eapply HSeq with
    (eta2 :=
       subst_bool_pformula t1_b FFalse
         (p_concentrated_mass (t1_regions 0) (PVar t1_y))).
  - (* x <- sample(Laplace(0,s)) *)
    apply HRealSample.
    + intro ps.
    + intro Hadm.
      intro Hadm.
      cbn [psatisfies].
      intro Hpre.
      unfold t1_pre in Hpre.
      apply psatisfies_p_eq in Hpre.
      cbn [pterm_eval] in Hpre.
      unfold p_concentrated_mass, t1_regions, t1_guard, t1_noise.
      rewrite subst_bool_pformula_p_and, !subst_bool_pformula_p_eq.
      rewrite sample_pformula_p_and, !sample_pformula_p_eq.
      apply psatisfies_p_and; split.
      * apply psatisfies_p_eq.
        cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_cformula
             c_not].
        rewrite !bpv_eq_dec_refl.
        cbn [sample_pterm pterm_eval].
        rewrite (expect_laplace_integral_valid _ _ _ _ (FImpl FFalse FFalse))
          by (exact Hs || (intro v; cbn [satisfies]; tauto)).
        rewrite (expect_laplace_integral_valid _ _ _ _ c_true)
          by (exact Hs || (intro v; cbn [c_true satisfies]; tauto)).
        reflexivity.
      * apply psatisfies_p_eq.
        cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_cformula
             sample_pterm pterm_eval].
        rewrite (expect_laplace_integral_valid _ _ _ _ c_true)
          by (exact Hs || (intro v; cbn [c_true satisfies]; tauto)).
        exact Hpre.
    + intros ps _.
      revert ps.
      apply p_almost_sure_of_pointwise.
      intro v.
      unfold t1_noise.
      cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
      intro Hle; lra.
  - (* b <- ff ; while *)
    eapply HSeq with
      (eta2 := p_concentrated_mass (t1_regions 0) (PVar t1_y)).
    + apply HBoolAssign.
    + exact t1_loop_derivable.
Qed.
