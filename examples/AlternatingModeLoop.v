(**
  AlternatingModeLoop.v -- a loop whose body flips a mode bit that nothing
  else reads.

      done := ff; mode := ff;
      while ~done do
        x    <- sample(Laplace(0, b));
        done := (0 <= x);
        mode := ~mode
      end

  THE TRIPLE ([am_terminates], for [0 < b]):

      { E[1_tt] = y }   am_prog b   { Pr[done] = 1 * y }

  ONE REGION.  Neither the guard nor the acceptance test mentions [mode], so
  the exit probability is 1/2 whatever the mode is, and the certificate needs
  a single region: the guard itself.  [mode] then appears in no assertion in
  the derivation, and [mode := ~mode] costs exactly one extra [HBoolAssign] --
  backward substitution into a mode-free assertion is the identity.

  WHY NOT TWO REGIONS.  An earlier version of this file partitioned the guard
  by [mode] and carried an off-diagonal 2x2 transition matrix.  It proved this
  same triple, and the extra structure earned nothing: both regions solve to
  1, so the chain lumps to the single-region one above, and the linear system
  was never actually coupled -- [while_solution] would have accepted the
  diagonal matrix just as happily.  A certificate that genuinely needs two
  regions wants a different exit rate per mode, whose post-sample integrand
  is a SUM of two scaled indicators; [expectation] has [expectation_scale]
  but no additivity axiom, so that sum cannot be split.  See FLAGS F3.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
Require Import CPHL.
Require Import SampleBeforeLoop.
Require Import PersistentSampleLoop.
Require Import HalfLaplaceRejection.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * The program *)

Definition am_x : RealProgramVar := real_program_var "am_x".
Definition am_mode : BoolProgramVar := bool_program_var "am_mode".
Definition am_done : BoolProgramVar := bool_program_var "am_done".
Definition am_y : ProbLogicVar := prob_logic_var "am_y".

Definition am_noise (b : R) : Distribution := <{ laplace(0, b) }>.

Definition am_accept : CFormula := <{ 0 <= am_x }>.

Definition am_guard : CFormula := <{ ~ am_done }>.

Definition am_body (b : R) : Cmd :=
  <{ am_x    sample $(am_noise b);
     am_done b= $(am_accept);
     am_mode b= (~ am_mode) }>.

Definition am_loop (b : R) : Cmd :=
  <{ while $(am_guard) do $(am_body b) end }>.

Definition am_prog (b : R) : Cmd :=
  <{ am_done b= false;
     am_mode b= false;
     $(am_loop b) }>.

(** * Certificate data

    One region -- the guard itself.  [mode] appears nowhere below. *)

Definition am_regions (_ : nat) : CFormula := am_guard.
Definition am_transitions (_ _ : nat) : R := 1 / 2.
Definition am_exits (_ : nat) : R := 1 / 2.
Definition am_solution (_ : nat) : R := 1.
Definition am_q : PConstruct := [[ indicator[true] ]].

(** * Satisfaction after a sample

    [update_real] touches only [am_x]. *)

Lemma am_sat_accept :
  forall (z : R) (v : state),
    satisfies (update_real v am_x z) am_accept <-> (0 <= z)%R.
Proof.
  intros z v.
  unfold am_accept, update_real, update_real_values.
  cbn [satisfies term_eval real_program_values].
  rewrite rpv_eq_dec_refl.
  split; intro H; exact H.
Qed.

(** * The two post-sample integrands

    Each is a constant: the acceptance test does not mention [mode], so
    nothing is read from the ambient valuation. *)

Definition am_psi_stay : CFormula := <{ ~ $(am_accept) }>.

Definition am_psi_exit : CFormula := <{ true /\ (~ (~ $(am_accept))) }>.

Lemma am_qeval_psi_stay :
  forall (b : R) (v : state),
    (0 < b)%R ->
    q_eval [[ integral am_x ~ $(am_noise b), indicator[$(am_psi_stay)] ]] v =
    (1 / 2)%R.
Proof.
  intros b v Hb.
  cbn [q_eval am_noise distribution_density term_eval].
  transitivity
    (real_integral
       (fun z => ((1 / (2 * b)) * exp (- Rabs (z - 0) / b)) *
                 real_indicator (z < 0)%R)).
  - apply real_integral_extensional; intro z.
    assert (Hiff :
      satisfies (update_real v am_x z) am_psi_stay <-> (z < 0)%R).
    { unfold am_psi_stay.
      cbn [c_not satisfies].
      split.
      - intro Hna.
        destruct (Rlt_dec z 0) as [Hd | Hd]; [exact Hd |].
        exfalso; apply Hna; apply am_sat_accept; lra.
      - intros Hz Ha; apply am_sat_accept in Ha; lra. }
    rewrite (real_indicator_extensional _ _ Hiff).
    reflexivity.
  - rewrite laplace_integral_strict_cdf by exact Hb.
    rewrite laplace_cdf_centre by exact Hb.
    lra.
Qed.

Lemma am_qeval_psi_exit :
  forall (b : R) (v : state),
    (0 < b)%R ->
    q_eval [[ integral am_x ~ $(am_noise b), indicator[$(am_psi_exit)] ]] v =
    (1 / 2)%R.
Proof.
  intros b v Hb.
  cbn [q_eval am_noise distribution_density term_eval].
  transitivity
    (real_integral
       (fun z => ((1 / (2 * b)) * exp (- Rabs (z - 0) / b)) *
                 real_indicator (0 <= z)%R)).
  - apply real_integral_extensional; intro z.
    assert (Hiff :
      satisfies (update_real v am_x z) am_psi_exit <-> (0 <= z)%R).
    { unfold am_psi_exit.
      rewrite satisfies_c_and.
      cbn [c_true c_not satisfies].
      split.
      - intros [_ Hnn].
        destruct (Rle_dec 0 z) as [Hd | Hd]; [exact Hd |].
        exfalso; apply Hnn; intro Ha.
        apply am_sat_accept in Ha; lra.
      - intro Hz.
        split; [tauto |].
        intro Hna; apply Hna; apply am_sat_accept; exact Hz. }
    rewrite (real_indicator_extensional _ _ Hiff).
    reflexivity.
  - rewrite laplace_integral_survival by exact Hb.
    rewrite laplace_cdf_centre by exact Hb.
    lra.
Qed.

(** * The backward substitutions land on the two integrands

    Substituting for [am_mode] is the identity in both: neither the region
    nor the exit formula mentions it. *)

Lemma am_subst_stay :
  subst_bool_cformula am_done am_accept
    (subst_bool_cformula am_mode <{ ~ am_mode }>
       (am_regions 0)) = am_psi_stay.
Proof. reflexivity. Qed.

Lemma am_subst_exit :
  subst_bool_cformula am_done am_accept
    (subst_bool_cformula am_mode <{ ~ am_mode }>
       <{ true /\ (~ $(am_guard)) }>) = am_psi_exit.
Proof. reflexivity. Qed.

(** * The body premise

    Both numbers are constants, so [t3_expect_const] carries them through the
    expectation; nothing has to be read off the region. *)

Lemma am_body_step :
  forall b : R,
    (0 < b)%R ->
    forall i : nat,
      (i < 1)%nat ->
      {{ $(p_concentrated_mass (am_regions i) (PConst 1)) }}
        $(am_body b)
      {{ $(while_body_post 1 am_regions (am_transitions i) am_guard am_q
             (am_exits i)) }}.
Proof.
  intros b Hb i Hi.
  unfold am_body.
  eapply HSeq with
    (eta2 :=
       subst_bool_pformula am_done am_accept
         (subst_bool_pformula am_mode (c_not (FProgBool am_mode))
            (while_body_post 1 am_regions (am_transitions i) am_guard am_q
               (am_exits i)))).
  - apply HRealSample.
    + intro ps.
    + intro Hadm.
      cbn [psatisfies].
      intro Hconc.
      assert (Hmass :
        expectation (pstate_measure ps) (q_eval (QIndicator c_true)) = 1%R).
      { apply psatisfies_p_and in Hconc.
        destruct Hconc as [_ Hm].
        apply psatisfies_p_eq in Hm.
        cbn [pterm_eval] in Hm; exact Hm. }
      unfold while_body_post, am_q.
      cbn [finite_p_and condition_pconstruct condition_pconstruct_fuel
           pconstruct_size].
      rewrite !subst_bool_pformula_p_and, !subst_bool_pformula_p_eq.
      rewrite !sample_pformula_p_and, !sample_pformula_p_eq.
      apply psatisfies_p_and; split; [apply psatisfies_p_and; split | ].
      * apply psatisfies_p_true.
      * apply psatisfies_p_eq.
        cbn [subst_bool_pterm subst_bool_pconstruct sample_pterm pterm_eval].
        rewrite am_subst_stay.
        rewrite (t3_expect_const ps _ (1 / 2)%R Hmass);
          [reflexivity | intro v; apply am_qeval_psi_stay; exact Hb].
      * apply psatisfies_p_eq.
        cbn [subst_bool_pterm subst_bool_pconstruct sample_pterm pterm_eval].
        rewrite am_subst_exit.
        rewrite (t3_expect_const ps _ (1 / 2)%R Hmass);
          [reflexivity | intro v; apply am_qeval_psi_exit; exact Hb].
    + intros ps _.
      revert ps.
      apply p_almost_sure_of_pointwise.
      intro v.
      unfold am_noise.
      cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
      intro Hle; lra.
  - eapply HSeq with
      (eta2 :=
         subst_bool_pformula am_mode (c_not (FProgBool am_mode))
           (while_body_post 1 am_regions (am_transitions i) am_guard am_q
              (am_exits i)));
      apply HBoolAssign.
Qed.

(** After both initialising assignments the region formula is a tautology. *)
Lemma am_prefix_formula_valid :
  forall v : state,
    satisfies v
      (subst_bool_cformula am_done <{ false }>
         (subst_bool_cformula am_mode <{ false }> (am_regions 0))).
Proof.
  intro v; vm_compute; tauto.
Qed.

Lemma am_subst_c_true :
  forall (b : BoolProgramVar) (beta : CFormula),
    subst_bool_cformula b beta <{ true }> = <{ true }>.
Proof. reflexivity. Qed.

(** * The loop *)

Lemma am_loop_derivable :
  forall (b : R) (k : nat),
    (0 < b)%R ->
    (k < 1)%nat ->
    {{ $(p_concentrated_mass (am_regions k) (PVar am_y)) }}
      $(am_loop b)
    {{ E[$(condition_pconstruct am_q (c_not am_guard))]
         = $(am_solution k) * am_y }}.
Proof.
  intros b k Hb Hk.
  eapply HWhile with
    (m := 1%nat) (k := k)
    (regions := am_regions) (solution := am_solution)
    (exits := am_exits) (transitions := am_transitions).
  - exact Hk.
  - unfold while_regions_cover, cformula_valid, am_regions.
    intro v; cbn [finite_c_or c_or c_not satisfies]; tauto.
  - unfold while_regions_in_guard, cformula_valid, am_regions.
    intros i Hi v; cbn [satisfies]; tauto.
  - unfold while_regions_disjoint.
    intros i j Hi Hj; lia.
  - unfold while_progress, am_exits.
    intros i Hi; left; lra.
  - apply am_body_step; exact Hb.
  - unfold while_solution, am_solution, am_transitions, am_exits.
    intros i Hi; cbn [finite_r_sum]; split; lra.
Qed.

(** * The whole program

    [done] is initialised first so the substitution reaching [mode] is the
    reflexive one. *)

Theorem am_terminates :
  forall b : R,
    (0 < b)%R ->
    {{ Pr[true] = am_y }}
      $(am_prog b)
    {{ E[$(condition_pconstruct am_q (c_not am_guard))] = 1 * am_y }}.
Proof.
  intros b Hb.
  unfold am_prog.
  eapply HSeq with
    (eta2 :=
       subst_bool_pformula am_mode FFalse
         (p_concentrated_mass (am_regions 0) (PVar am_y))).
  - eapply HConseq with
      (eta1 :=
         subst_bool_pformula am_done FFalse
           (subst_bool_pformula am_mode FFalse
              (p_concentrated_mass (am_regions 0) (PVar am_y))))
      (eta2 :=
         subst_bool_pformula am_mode FFalse
           (p_concentrated_mass (am_regions 0) (PVar am_y))).
    + intro ps.
    + intro Hadm.
      cbn [psatisfies].
      intro Hpre.
      apply psatisfies_p_eq in Hpre.
      cbn [pterm_eval] in Hpre.
      unfold p_concentrated_mass, am_regions, am_guard.
      rewrite !subst_bool_pformula_p_and, !subst_bool_pformula_p_eq.
      apply psatisfies_p_and; split; apply psatisfies_p_eq;
        cbn [subst_bool_pterm subst_bool_pconstruct pterm_eval];
        rewrite !am_subst_c_true.
      * rewrite (expect_indicator_valid _ _ am_prefix_formula_valid).
        reflexivity.
      * exact Hpre.
    + apply HBoolAssign.
    + intro ps; cbn [psatisfies]; tauto.
  - eapply HSeq with
      (eta2 := p_concentrated_mass (am_regions 0) (PVar am_y)).
    + apply HBoolAssign.
    + replace 1%R with (am_solution 0) by reflexivity.
      apply am_loop_derivable; [exact Hb | lia].
Qed.
