(**
  SVT.v

  Program ([svt_01 epsilon], which runs [svt_two_queries epsilon] on the
  query vector q1 = 0, q2 = 1):

      q1 := 0;  q2 := 1;
      out1 := ff;  out2 := ff;
      threshold <- sample(laplace(0, 2/epsilon));
      noisy1    <- sample(laplace(q1, 4/epsilon));
      above1    := (threshold <= noisy1);
      if above1 then out1 := tt
      else
        noisy2 <- sample(laplace(q2, 4/epsilon));
        above2 := (threshold <= noisy2);
        if above2 then out2 := tt else skip end
      end

  Triple ([svt_01_bot_top_probability], for 0 < epsilon and every p):

      { E[1_tt] = 1  /\
        E[ integral threshold ~ laplace(0, 2/epsilon),
           integral noisy1    ~ laplace(0, 4/epsilon),
           integral noisy2    ~ laplace(1, 4/epsilon),
             1_(noisy1 < threshold /\ threshold <= noisy2) ] = p }
          svt_01 epsilon
      { E[1_(~out1 /\ out2)] = p }

  Triple ([svt_symbolic_hoare], for 0 < epsilon and every p), the same
  statement for symbolic queries q1, q2:

      { E[1_tt] = 1  /\
        E[ integral threshold ~ laplace(0, 2/epsilon),
           integral noisy1    ~ laplace(q1, 4/epsilon),
           integral noisy2    ~ laplace(q2, 4/epsilon),
             1_(noisy1 < threshold /\ threshold <= noisy2) ] = p }
          svt_two_queries epsilon
      { E[1_(~out1 /\ out2)] = p }
*)


From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import Psatz.
From Stdlib Require Import Field.
From Stdlib Require Import Ring.
From Stdlib Require Import Logic.FunctionalExtensionality.

Require Import CPHL.

(** Keep propositional automation intuitionistic; when classical reasoning
    is needed, use MathComp's double-negation law rather than the default
    Stdlib fallback of [tauto]. *)
Local Ltac mathcomp_tauto :=
  first [solve [intuition fail] |
    apply (proj1 (boolp.not_notP _)); solve [intuition fail] ].
(** Concrete density rewrites require valid sampling parameters. Semantic
    assertion premises additionally introduce admissibility of the input. *)

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** Extensionality followed by the integral of zero, without a validity
    restriction on the sampling parameters. *)
Local Ltac zero_sampling_expectation :=
  etransitivity;
  [apply MeasureIntegration.ConcreteMeasure.expectation_ext |
   apply MeasureIntegration.ConcreteMeasure.expectation_zero].

(** Nested Boolean substitutions can expose another variable decision
    before their size/fuel reduces. Finish those reductions before using
    the syntax-to-event indicator bridge. *)
Local Ltac expose_construct_indicator :=
  repeat first
    [progress cbn [subst_bool_pconstruct subst_bool_pconstruct_fuel
       subst_bool_cformula condition_pconstruct condition_pconstruct_fuel
       pconstruct_size cformula_real_program_vars pconstruct_real_program_vars
       distribution_real_program_vars term_real_program_vars List.app List.in_dec
       list_rec list_rect q_eval c_and c_not c_true]
    | match goal with
      | |- context [bool_program_var_eq_dec ?x ?y] =>
          destruct (bool_program_var_eq_dec x y); try congruence
      | |- context [real_program_var_eq_dec ?x ?y] =>
          destruct (real_program_var_eq_dec x y); try congruence
      end];
  rewrite ?q_eval_indicatorE, ?formula_indicatorE.

(** Program variables. *)
Definition svt_q1 : RealProgramVar := real_program_var "svt_q1".
Definition svt_q2 : RealProgramVar := real_program_var "svt_q2".
Definition svt_threshold : RealProgramVar := real_program_var "svt_threshold".
Definition svt_noisy1 : RealProgramVar := real_program_var "svt_noisy1".
Definition svt_noisy2 : RealProgramVar := real_program_var "svt_noisy2".

Definition svt_above1 : BoolProgramVar := bool_program_var "svt_above1".
Definition svt_above2 : BoolProgramVar := bool_program_var "svt_above2".
Definition svt_out1 : BoolProgramVar := bool_program_var "svt_out1".
Definition svt_out2 : BoolProgramVar := bool_program_var "svt_out2".

(** Rigid variables used only inside the derived conditional proof. *)
Definition svt_y_then : ProbLogicVar := prob_logic_var "svt_y_then".
Definition svt_y_else : ProbLogicVar := prob_logic_var "svt_y_else".

Definition svt_threshold_distribution (epsilon : R) : Distribution :=
  <{ laplace ( 0, $((2 / epsilon)%R) ) }>.

Definition svt_query_distribution
  (epsilon : R) (query : RealProgramVar) : Distribution :=
  <{ laplace ( query, $((4 / epsilon)%R) ) }>.

Definition svt_first_comparison : CFormula :=
  <{ svt_threshold <= svt_noisy1 }>.

Definition svt_second_comparison : CFormula :=
  <{ svt_threshold <= svt_noisy2 }>.

(** The second unfolded iteration is executed only after the first answer was
    [bot]. *)
Definition svt_second_iteration (epsilon : R) : Cmd :=
  <{
    svt_noisy2 sample $(svt_query_distribution epsilon svt_q2);
    svt_above2 b= $(svt_second_comparison);
    if svt_above2 then svt_out2 b= true else skip end
  }>.

(** The generic [N = 2], [c = 1] SVT command.  The output initialization is
    explicit, and the true branch of the first comparison implements the
    early exit. *)
Definition svt_two_queries (epsilon : R) : Cmd :=
  <{
    svt_out1 b= false;
    svt_out2 b= false;
    svt_threshold sample $(svt_threshold_distribution epsilon);
    svt_noisy1 sample $(svt_query_distribution epsilon svt_q1);
    svt_above1 b= $(svt_first_comparison);
    if svt_above1 then svt_out1 b= true
    else $(svt_second_iteration epsilon)
    end
  }>.

(** A concrete run on the input vector [[0, 1]]. *)
Definition svt_01 (epsilon : R) : Cmd :=
  <{ svt_q1 := 0; svt_q2 := 1; $(svt_two_queries epsilon) }>.

Definition svt_bot_top : CFormula :=
  <{ ~ svt_out1 /\ svt_out2 }>.

Definition svt_path_event : CFormula :=
  <{ svt_noisy1 < svt_threshold /\ svt_threshold <= svt_noisy2 }>.

Definition svt_path_construct (epsilon : R) : PConstruct :=
  [[
    integral svt_threshold ~ $(svt_threshold_distribution epsilon),
    integral svt_noisy1 ~ $(svt_query_distribution epsilon svt_q1),
    integral svt_noisy2 ~ $(svt_query_distribution epsilon svt_q2),
    indicator[$(svt_path_event)]
  ]].

Definition svt_path_construct_01 (epsilon : R) : PConstruct :=
  [[
    integral svt_threshold ~ $(svt_threshold_distribution epsilon),
    integral svt_noisy1 ~ laplace ( 0, $((4 / epsilon)%R) ),
    integral svt_noisy2 ~ laplace ( 1, $((4 / epsilon)%R) ),
    indicator[$(svt_path_event)]
  ]].

Definition probability_of_bot_top_equals (r : R) : PFormula :=
  [[ Pr[$(svt_bot_top)] = $(r) ]].

Definition normalized : PFormula :=
  [[ Pr[true] = 1 ]].

Lemma svt_threshold_scale_positive :
  forall epsilon : R, (0 < epsilon)%R -> (0 < 2 / epsilon)%R.
Proof.
  intros epsilon Hepsilon.
  unfold Rdiv.
  apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; exact Hepsilon].
Qed.

Lemma svt_query_scale_positive :
  forall epsilon : R, (0 < epsilon)%R -> (0 < 4 / epsilon)%R.
Proof.
  intros epsilon Hepsilon.
  unfold Rdiv.
  apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; exact Hepsilon].
Qed.

(** Raw analytical presentation of the nested probability construct. *)

Definition svt_event_probability (r : R) (gamma : CFormula) : PFormula :=
  [[ $(r) = Pr[$(gamma)] ]].

Definition svt_rigid_constant
  (y : ProbLogicVar) (r : R) : PFormula :=
  [[ y = $(r) ]].

Lemma svt_rigid_constant_analytical :
  forall (y : ProbLogicVar) (r : R),
    pformula_analytical (svt_rigid_constant y r).
Proof.
  intros y r.
  cbn [svt_rigid_constant p_eq p_and p_not
    pformula_analytical pterm_analytical].
  mathcomp_tauto.
Qed.

Lemma svt_add_rigid_constant :
  forall (eta : PFormula) (s : Cmd) (gamma : CFormula)
    (y : ProbLogicVar) (r : R),
    {{ $(eta) }} $(s) {{ $(svt_event_probability r gamma) }} ->
    {{ $(eta) /\ $(svt_rigid_constant y r) }} $(s)
      {{ y = Pr[$(gamma)] }}.
Proof.
  intros eta s gamma y r Hbranch.
  assert (Hevent :
    hoare_derivable (p_and eta (svt_rigid_constant y r)) s
      (svt_event_probability r gamma)).
  {
    eapply HConseq with
      (eta1 := eta) (eta2 := svt_event_probability r gamma).
    - unfold pformula_valid.
      intros ps Hps_admissible.
      cbn [p_and p_not psatisfies].
      mathcomp_tauto.
    - exact Hbranch.
    - unfold pformula_valid.
      intros ps Hps_admissible; cbn [psatisfies]; mathcomp_tauto.
  }
  assert (Hrigid :
    hoare_derivable (p_and eta (svt_rigid_constant y r)) s
      (svt_rigid_constant y r)).
  {
    eapply HConseq with
      (eta1 := svt_rigid_constant y r)
      (eta2 := svt_rigid_constant y r).
    - unfold pformula_valid.
      intros ps Hps_admissible.
      cbn [p_and p_not psatisfies].
      mathcomp_tauto.
    - apply HFree.
      apply svt_rigid_constant_analytical.
    - unfold pformula_valid.
      intros ps Hps_admissible; cbn [psatisfies]; mathcomp_tauto.
  }
  eapply HConseq with
    (eta1 := p_and eta (svt_rigid_constant y r))
    (eta2 := p_and (svt_event_probability r gamma)
      (svt_rigid_constant y r)).
  - unfold pformula_valid.
    intros ps Hps_admissible; cbn [psatisfies]; mathcomp_tauto.
  - apply HAnd; assumption.
  - unfold pformula_valid, svt_event_probability, svt_rigid_constant.
    intros ps Hps_admissible.
    cbn [p_and p_not p_eq psatisfies pterm_eval] in *.
    clear Hps_admissible.
    intuition lra.
Qed.

(** A local exact conditional rule.  The rigid variables record the two
    branch masses, [HIfEq] adds them, [HFree]/[HAnd] retain their constant
    values, and [HElimv] removes the auxiliary names. *)
Lemma svt_if_constants :
  forall (eta1 eta2 : PFormula) (guard gamma : CFormula)
    (s1 s2 : Cmd) (r1 r2 : R),
    {{ $(eta1) }} $(s1) {{ $(svt_event_probability r1 gamma) }} ->
    {{ $(eta2) }} $(s2) {{ $(svt_event_probability r2 gamma) }} ->
    {{ $(subst_prob_pformula svt_y_then [[ $(r1) ]]
          (subst_prob_pformula svt_y_else [[ $(r2) ]]
            (if_precondition eta1 eta2 guard))) }}
      if $(guard) then $(s1) else $(s2) end
    {{ $(svt_event_probability (r1 + r2) gamma) }}.
Proof.
  intros eta1 eta2 guard gamma s1 s2 r1 r2 Hbranch1 Hbranch2.
  set (base := if_precondition eta1 eta2 guard).
  set (eq1 := svt_rigid_constant svt_y_then r1).
  set (eq2 := svt_rigid_constant svt_y_else r2).
  assert (Hif :
    hoare_derivable
      (if_precondition (p_and eta1 eq1) (p_and eta2 eq2) guard)
      (CIf guard s1 s2)
      (p_eq (PAdd (PVar svt_y_then) (PVar svt_y_else))
        (PExpect (QIndicator gamma)))).
  {
    apply HIfEq with
      (eta1 := p_and eta1 eq1) (eta2 := p_and eta2 eq2).
    - unfold eq1.
      apply svt_add_rigid_constant.
      exact Hbranch1.
    - unfold eq2.
      apply svt_add_rigid_constant.
      exact Hbranch2.
  }
  set (with_constants := p_and (p_and base eq1) eq2).
  assert (Hif_from_constants :
    hoare_derivable with_constants (CIf guard s1 s2)
      (p_eq (PAdd (PVar svt_y_then) (PVar svt_y_else))
        (PExpect (QIndicator gamma)))).
  {
    eapply HConseq with
      (eta1 := if_precondition (p_and eta1 eq1) (p_and eta2 eq2) guard)
      (eta2 := p_eq (PAdd (PVar svt_y_then) (PVar svt_y_else))
        (PExpect (QIndicator gamma))).
    - unfold pformula_valid, with_constants, base, eq1, eq2,
        if_precondition, svt_rigid_constant.
      intros ps Hps_admissible.
      cbn [condition_pformula condition_pterm p_and p_not p_eq
        psatisfies pterm_eval] in *.
      clear Hps_admissible.
      intuition lra.
    - exact Hif.
    - unfold pformula_valid.
      intros ps Hps_admissible; cbn [psatisfies]; mathcomp_tauto.
  }
  assert (Hconstants :
    hoare_derivable with_constants (CIf guard s1 s2) (p_and eq1 eq2)).
  {
    eapply HConseq with (eta1 := p_and eq1 eq2) (eta2 := p_and eq1 eq2).
    - unfold pformula_valid, with_constants.
      intros ps Hps_admissible.
      cbn [p_and p_not psatisfies].
      mathcomp_tauto.
    - apply HFree.
      unfold eq1, eq2.
      cbn [svt_rigid_constant p_eq p_and p_not
        pformula_analytical pterm_analytical].
      mathcomp_tauto.
    - unfold pformula_valid.
      intros ps Hps_admissible; cbn [psatisfies]; mathcomp_tauto.
  }
  assert (Hwithout_rigids :
    hoare_derivable with_constants (CIf guard s1 s2)
      (svt_event_probability (r1 + r2) gamma)).
  {
    eapply HConseq with
      (eta1 := with_constants)
      (eta2 := p_and
        (p_eq (PAdd (PVar svt_y_then) (PVar svt_y_else))
          (PExpect (QIndicator gamma)))
        (p_and eq1 eq2)).
    - unfold pformula_valid.
      intros ps Hps_admissible; cbn [psatisfies]; mathcomp_tauto.
    - apply HAnd; assumption.
    - unfold pformula_valid, svt_event_probability, eq1, eq2,
        svt_rigid_constant.
      intros ps Hps_admissible.
      cbn [p_and p_not p_eq psatisfies pterm_eval] in *.
      clear Hps_admissible.
      intuition lra.
  }
  assert (Helim_else :
    hoare_derivable
      (subst_prob_pformula svt_y_else (PConst r2)
        (p_and base eq1))
      (CIf guard s1 s2)
      (svt_event_probability (r1 + r2) gamma)).
  {
    eapply HElimv with
      (eta1 := p_and base eq1) (y := svt_y_else) (p := PConst r2).
    - change (hoare_derivable with_constants (CIf guard s1 s2)
        (svt_event_probability (r1 + r2) gamma)).
      exact Hwithout_rigids.
    - cbn [prob_logic_var_occurs_pterm]; mathcomp_tauto.
    - cbn [svt_event_probability p_eq p_and p_not
        prob_logic_var_occurs_pformula prob_logic_var_occurs_pterm].
      mathcomp_tauto.
  }
  assert (Helim_then :
    hoare_derivable
      (subst_prob_pformula svt_y_then (PConst r1)
        (subst_prob_pformula svt_y_else (PConst r2) base))
      (CIf guard s1 s2)
      (svt_event_probability (r1 + r2) gamma)).
  {
    eapply HElimv with
      (eta1 := subst_prob_pformula svt_y_else (PConst r2) base)
      (y := svt_y_then) (p := PConst r1).
    - change (hoare_derivable
        (subst_prob_pformula svt_y_else (PConst r2) (p_and base eq1))
        (CIf guard s1 s2)
        (svt_event_probability (r1 + r2) gamma)).
      exact Helim_else.
    - cbn [prob_logic_var_occurs_pterm]; mathcomp_tauto.
    - cbn [svt_event_probability p_eq p_and p_not
        prob_logic_var_occurs_pformula prob_logic_var_occurs_pterm].
      mathcomp_tauto.
  }
  unfold base in Helim_then.
  exact Helim_then.
Qed.

Lemma svt_laplace_constant_valid :
  forall (location : Term) (scale : R),
    (0 < scale)%R ->
    pformula_valid
      [[ almost_sure[$(distribution_valid_formula
          <{ laplace ( $(location), $(scale) ) }>)] ]].
Proof.
  intros location scale Hscale.
  unfold pformula_valid.
  intros ps Hps_admissible.
  assert (Heq :
    expectation (pstate_measure ps)
      (q_eval
        (QIndicator
          (distribution_valid_formula
            (Laplace location (TConst scale))))) =
    expectation (pstate_measure ps) (q_eval (QIndicator c_true))).
  {
    rewrite !expectation_indicator.
    apply measure_extensional.
    intro v.
    unfold formula_assertion, distribution_valid_formula, c_lt, c_not,
      c_true.
    cbn [satisfies term_eval].
    split.
    - intros _ Hfalse; exact Hfalse.
    - intros _ Hle; lra.
  }
  unfold p_almost_sure, p_eq, p_and, p_not.
  cbn [psatisfies pterm_eval].
  lra.
Qed.

Lemma svt_laplace_sample :
  forall (eta : PFormula) (x : RealProgramVar) (location : Term)
    (scale : R),
    (0 < scale)%R ->
    {{ $(sample_pformula x <{ laplace ( $(location), $(scale) ) }> eta) }}
      x sample laplace ( $(location), $(scale) )
    {{ $(eta) }}.
Proof.
  intros eta x location scale Hscale.
  apply HRealSample.
  - unfold pformula_valid.
    intros ps Hps_admissible; cbn [psatisfies]; mathcomp_tauto.
  - unfold pformula_valid.
    intros ps Hps_admissible.
    cbn [psatisfies].
    intro Hpre.
    apply (svt_laplace_constant_valid location scale Hscale ps Hps_admissible).
Qed.

Definition svt_output_probability (r : R) : PFormula :=
  svt_event_probability r svt_bot_top.

Definition svt_inner_true_pre (p : R) : PFormula :=
  subst_bool_pformula svt_out2 <{ true }> (svt_output_probability p).

Definition svt_inner_false_pre : PFormula :=
  svt_output_probability 0.

Definition svt_inner_if_pre (p : R) : PFormula :=
  subst_prob_pformula svt_y_then [[ $(p) ]]
    (subst_prob_pformula svt_y_else [[ 0 ]]
      (if_precondition (svt_inner_true_pre p) svt_inner_false_pre
        <{ svt_above2 }>)).

Definition svt_after_noisy2 (p : R) : PFormula :=
  subst_bool_pformula svt_above2 svt_second_comparison
    (svt_inner_if_pre p).

Definition svt_before_noisy2 (epsilon p : R) : PFormula :=
  sample_pformula svt_noisy2
    (svt_query_distribution epsilon svt_q2)
    (svt_after_noisy2 p).

Lemma svt_inner_if_derivable :
  forall p : R,
    {{ $(svt_inner_if_pre p) }}
      if svt_above2 then svt_out2 b= true else skip end
    {{ $(svt_output_probability p) }}.
Proof.
  intro p.
  unfold svt_inner_if_pre, svt_output_probability.
  replace p with (p + 0)%R at 3 by ring.
  apply svt_if_constants.
  - unfold svt_inner_true_pre.
    apply HBoolAssign.
  - unfold svt_inner_false_pre.
    apply HSkip.
Qed.

Lemma svt_second_iteration_derivable :
  forall epsilon p : R,
    (0 < epsilon)%R ->
    {{ $(svt_before_noisy2 epsilon p) }}
      $(svt_second_iteration epsilon)
    {{ $(svt_output_probability p) }}.
Proof.
  intros epsilon p Hepsilon.
  unfold svt_second_iteration, svt_before_noisy2,
    svt_query_distribution.
  eapply HSeq with (eta2 := svt_after_noisy2 p).
  - apply svt_laplace_sample.
    apply svt_query_scale_positive; exact Hepsilon.
  - eapply HSeq with (eta2 := svt_inner_if_pre p).
    + unfold svt_after_noisy2.
      apply HBoolAssign.
    + apply svt_inner_if_derivable.
Qed.

Definition svt_outer_true_pre : PFormula :=
  subst_bool_pformula svt_out1 <{ true }> (svt_output_probability 0).

Definition svt_outer_if_pre (epsilon p : R) : PFormula :=
  subst_prob_pformula svt_y_then [[ 0 ]]
    (subst_prob_pformula svt_y_else [[ $(p) ]]
      (if_precondition svt_outer_true_pre
        (svt_before_noisy2 epsilon p) <{ svt_above1 }>)).

Definition svt_after_noisy1 (epsilon p : R) : PFormula :=
  subst_bool_pformula svt_above1 svt_first_comparison
    (svt_outer_if_pre epsilon p).

Definition svt_before_noisy1 (epsilon p : R) : PFormula :=
  sample_pformula svt_noisy1
    (svt_query_distribution epsilon svt_q1)
    (svt_after_noisy1 epsilon p).

Definition svt_before_threshold (epsilon p : R) : PFormula :=
  sample_pformula svt_threshold (svt_threshold_distribution epsilon)
    (svt_before_noisy1 epsilon p).

Definition svt_before_output2 (epsilon p : R) : PFormula :=
  subst_bool_pformula svt_out2 <{ false }>
    (svt_before_threshold epsilon p).

Definition svt_generic_pre (epsilon p : R) : PFormula :=
  subst_bool_pformula svt_out1 <{ false }>
    (svt_before_output2 epsilon p).

Lemma svt_outer_if_derivable :
  forall epsilon p : R,
    (0 < epsilon)%R ->
    {{ $(svt_outer_if_pre epsilon p) }}
      if svt_above1 then svt_out1 b= true
      else $(svt_second_iteration epsilon)
      end
    {{ $(svt_output_probability p) }}.
Proof.
  intros epsilon p Hepsilon.
  unfold svt_outer_if_pre, svt_output_probability.
  replace p with (0 + p)%R at 3 by ring.
  apply svt_if_constants.
  - unfold svt_outer_true_pre.
    apply HBoolAssign.
  - apply svt_second_iteration_derivable.
    exact Hepsilon.
Qed.

Theorem svt_generic_wp_derivable :
  forall epsilon p : R,
    (0 < epsilon)%R ->
    {{ $(svt_generic_pre epsilon p) }}
      $(svt_two_queries epsilon)
    {{ $(svt_output_probability p) }}.
Proof.
  intros epsilon p Hepsilon.
  unfold svt_two_queries, svt_generic_pre.
  eapply HSeq with (eta2 := svt_before_output2 epsilon p).
  - apply HBoolAssign.
  - eapply HSeq with (eta2 := svt_before_threshold epsilon p).
    + unfold svt_before_output2.
      apply HBoolAssign.
    + eapply HSeq with (eta2 := svt_before_noisy1 epsilon p).
      * unfold svt_before_threshold, svt_threshold_distribution.
        apply svt_laplace_sample.
        apply svt_threshold_scale_positive; exact Hepsilon.
      * eapply HSeq with (eta2 := svt_after_noisy1 epsilon p).
        -- unfold svt_before_noisy1, svt_query_distribution.
           apply svt_laplace_sample.
           apply svt_query_scale_positive; exact Hepsilon.
        -- eapply HSeq with (eta2 := svt_outer_if_pre epsilon p).
           ++ unfold svt_after_noisy1.
              apply HBoolAssign.
           ++ apply svt_outer_if_derivable.
              exact Hepsilon.
Qed.

Definition svt_concrete_pre (epsilon p : R) : PFormula :=
  subst_real_pformula svt_q1 <{ 0 }>
    (subst_real_pformula svt_q2 <{ 1 }>
      (svt_generic_pre epsilon p)).

Theorem svt_concrete_wp_derivable :
  forall epsilon p : R,
    (0 < epsilon)%R ->
    {{ $(svt_concrete_pre epsilon p) }}
      $(svt_01 epsilon)
    {{ $(svt_output_probability p) }}.
Proof.
  intros epsilon p Hepsilon.
  unfold svt_01, svt_concrete_pre.
  eapply HSeq with
    (eta2 := subst_real_pformula svt_q2 (TConst 1)
      (svt_generic_pre epsilon p)).
  - apply HRealAssign.
  - eapply HSeq with (eta2 := svt_generic_pre epsilon p).
    + apply HRealAssign.
    + apply svt_generic_wp_derivable.
      exact Hepsilon.
Qed.


Definition svt_symbolic_pre (epsilon p : R) : PFormula :=
  [[ $(normalized) /\ E[$(svt_path_construct epsilon)] = $(p) ]].

(** The three expectation constructs occurring in the generated weakest
    precondition: an impossible first-true branch, the desired path, and an
    impossible second-false branch. *)
Definition svt_wp_outer_zero_construct (epsilon : R) : PConstruct :=
  subst_bool_pconstruct svt_out1 <{ false }>
    (subst_bool_pconstruct svt_out2 <{ false }>
      [[
        integral svt_threshold ~ $(svt_threshold_distribution epsilon),
        integral svt_noisy1 ~ $(svt_query_distribution epsilon svt_q1),
        $(subst_bool_pconstruct svt_above1 svt_first_comparison
          (condition_pconstruct
            [[ indicator[$(subst_bool_cformula svt_out1 <{ true }> svt_bot_top)] ]]
            <{ svt_above1 }>))
      ]]).

Definition svt_wp_path_construct (epsilon : R) : PConstruct :=
  subst_bool_pconstruct svt_out1 <{ false }>
    (subst_bool_pconstruct svt_out2 <{ false }>
      [[
        integral svt_threshold ~ $(svt_threshold_distribution epsilon),
        integral svt_noisy1 ~ $(svt_query_distribution epsilon svt_q1),
        $(subst_bool_pconstruct svt_above1 svt_first_comparison
          (condition_pconstruct
            [[
              integral svt_noisy2 ~ $(svt_query_distribution epsilon svt_q2),
              $(subst_bool_pconstruct svt_above2 svt_second_comparison
                (condition_pconstruct
                  [[ indicator[$(subst_bool_cformula
                    svt_out2 <{ true }> svt_bot_top)] ]]
                  <{ svt_above2 }>))
            ]]
            <{ ~ svt_above1 }>))
      ]]).

Definition svt_wp_inner_zero_construct (epsilon : R) : PConstruct :=
  subst_bool_pconstruct svt_out1 <{ false }>
    (subst_bool_pconstruct svt_out2 <{ false }>
      [[
        integral svt_threshold ~ $(svt_threshold_distribution epsilon),
        integral svt_noisy1 ~ $(svt_query_distribution epsilon svt_q1),
        $(subst_bool_pconstruct svt_above1 svt_first_comparison
          (condition_pconstruct
            [[
              integral svt_noisy2 ~ $(svt_query_distribution epsilon svt_q2),
              $(subst_bool_pconstruct svt_above2 svt_second_comparison
                (condition_pconstruct
                  [[ indicator[$(svt_bot_top)] ]]
                  <{ ~ svt_above2 }>))
            ]]
            <{ ~ svt_above1 }>))
      ]]).

Lemma svt_generic_pre_shape :
  forall epsilon p : R,
    svt_generic_pre epsilon p =
      [[ 0 = E[$(svt_wp_outer_zero_construct epsilon)] /\
         $(p) = E[$(svt_wp_path_construct epsilon)] /\
         0 = E[$(svt_wp_inner_zero_construct epsilon)] ]].
Proof.
  intros epsilon p.
  unfold svt_generic_pre, svt_before_output2, svt_before_threshold,
    svt_before_noisy1, svt_after_noisy1, svt_outer_if_pre,
    svt_outer_true_pre, svt_before_noisy2, svt_after_noisy2,
    svt_inner_if_pre, svt_inner_true_pre, svt_inner_false_pre,
    svt_output_probability, svt_event_probability,
    svt_wp_outer_zero_construct, svt_wp_path_construct,
    svt_wp_inner_zero_construct, if_precondition.
  cbn [subst_prob_pformula subst_prob_pterm condition_pformula
    condition_pterm sample_pformula sample_pterm subst_bool_pformula
    subst_bool_pterm].
  reflexivity.
Qed.

Lemma svt_wp_path_construct_eval :
  forall (epsilon : R) (v : state),
    q_eval (svt_wp_path_construct epsilon) v =
      q_eval (svt_path_construct epsilon) v.
Proof.
  intros epsilon v.
  unfold svt_wp_path_construct, svt_path_construct,
    svt_threshold_distribution, svt_query_distribution,
    svt_first_comparison, svt_second_comparison, svt_bot_top,
    svt_path_event, svt_q1, svt_q2, svt_threshold, svt_noisy1,
    svt_noisy2, svt_above1, svt_above2, svt_out1, svt_out2.
  cbn [subst_bool_pconstruct subst_bool_pconstruct_fuel subst_bool_cformula
    condition_pconstruct condition_pconstruct_fuel
    cformula_real_program_vars pconstruct_real_program_vars
    distribution_real_program_vars term_real_program_vars pconstruct_size
    List.in_dec real_program_var_eq_dec bool_program_var_eq_dec
    q_eval distribution_density term_eval satisfies update_real
    update_real_values real_program_values c_and c_not c_lt c_true].
  (** Recover the event-mask interface after reducing a construct leaf. *)
  repeat rewrite (FunctionalExtensionality.functional_extensionality
    _ _ (formula_indicatorE _)).
  cbn [subst_bool_pconstruct subst_bool_pconstruct_fuel subst_bool_cformula condition_pconstruct
    condition_pconstruct_fuel cformula_real_program_vars pconstruct_real_program_vars
    distribution_real_program_vars term_real_program_vars pconstruct_size List.in_dec
    real_program_var_eq_dec bool_program_var_eq_dec distribution_density term_eval
    satisfies update_real update_real_values real_program_values c_and c_not c_lt
    c_true].
  apply MeasureIntegration.ConcreteMeasure.expectation_ext.
  intro threshold.
  apply MeasureIntegration.ConcreteMeasure.expectation_ext.
  intro noisy1.
  apply MeasureIntegration.ConcreteMeasure.expectation_ext.
  intro noisy2.
  expose_construct_indicator; apply real_indicator_extensional.
  repeat match goal with
  | |- context [bool_program_var_eq_dec ?x ?y] =>
      destruct (bool_program_var_eq_dec x y); try congruence
  end.
  cbn [subst_bool_cformula satisfies c_and c_not c_true term_eval
    update_real update_real_values real_program_values
    real_program_var_eq_dec].
  repeat match goal with
  | |- context [real_program_var_eq_dec ?x ?y] =>
      destruct (real_program_var_eq_dec x y); try congruence
  end.
  cbn [satisfies c_and c_not c_true term_eval update_real
    update_real_values real_program_values].
  mathcomp_tauto.
Qed.

Lemma svt_wp_outer_zero_construct_eval :
  forall (epsilon : R) (v : state),
    q_eval (svt_wp_outer_zero_construct epsilon) v = 0%R.
Proof.
  intros epsilon v.
  unfold svt_wp_outer_zero_construct, svt_threshold_distribution,
    svt_query_distribution, svt_first_comparison, svt_bot_top,
    svt_q1, svt_threshold, svt_noisy1, svt_above1,
    svt_out1, svt_out2.
  cbn [subst_bool_pconstruct subst_bool_pconstruct_fuel subst_bool_cformula
    condition_pconstruct condition_pconstruct_fuel
    cformula_real_program_vars pconstruct_real_program_vars
    distribution_real_program_vars term_real_program_vars pconstruct_size
    List.in_dec real_program_var_eq_dec bool_program_var_eq_dec
    q_eval distribution_density term_eval satisfies update_real
    update_real_values real_program_values c_and c_not c_lt c_true].
  (** Recover the event-mask interface after reducing a construct leaf. *)
  repeat rewrite (FunctionalExtensionality.functional_extensionality
    _ _ (formula_indicatorE _)).
  cbn [subst_bool_pconstruct subst_bool_pconstruct_fuel subst_bool_cformula condition_pconstruct
    condition_pconstruct_fuel cformula_real_program_vars pconstruct_real_program_vars
    distribution_real_program_vars term_real_program_vars pconstruct_size List.in_dec
    real_program_var_eq_dec bool_program_var_eq_dec distribution_density term_eval
    satisfies update_real update_real_values real_program_values c_and c_not c_lt
    c_true].
  (* The zero reward integrates to zero under every sampling measure. *)
  zero_sampling_expectation; intro threshold.
  zero_sampling_expectation; intro noisy1.
  expose_construct_indicator; apply real_indicator_false.
  repeat match goal with
        | |- context [bool_program_var_eq_dec ?x ?y] =>
            destruct (bool_program_var_eq_dec x y); try congruence
        end.
        cbn [subst_bool_cformula satisfies c_and c_not c_true term_eval
          update_real update_real_values real_program_values].
        repeat match goal with
        | |- context [real_program_var_eq_dec ?x ?y] =>
            destruct (real_program_var_eq_dec x y); try congruence
        end.
        cbn [satisfies c_and c_not c_true term_eval update_real
          update_real_values real_program_values].
        mathcomp_tauto.
Qed.

Lemma svt_wp_inner_zero_construct_eval :
  forall (epsilon : R) (v : state),
    q_eval (svt_wp_inner_zero_construct epsilon) v = 0%R.
Proof.
  intros epsilon v.
  unfold svt_wp_inner_zero_construct, svt_threshold_distribution,
    svt_query_distribution, svt_first_comparison, svt_second_comparison,
    svt_bot_top, svt_q1, svt_q2, svt_threshold, svt_noisy1,
    svt_noisy2, svt_above1, svt_above2, svt_out1, svt_out2.
  cbn [subst_bool_pconstruct subst_bool_pconstruct_fuel subst_bool_cformula
    condition_pconstruct condition_pconstruct_fuel
    cformula_real_program_vars pconstruct_real_program_vars
    distribution_real_program_vars term_real_program_vars pconstruct_size
    List.in_dec real_program_var_eq_dec bool_program_var_eq_dec
    q_eval distribution_density term_eval satisfies update_real
    update_real_values real_program_values c_and c_not c_lt c_true].
  (** Recover the event-mask interface after reducing a construct leaf. *)
  repeat rewrite (FunctionalExtensionality.functional_extensionality
    _ _ (formula_indicatorE _)).
  cbn [subst_bool_pconstruct subst_bool_pconstruct_fuel subst_bool_cformula condition_pconstruct
    condition_pconstruct_fuel cformula_real_program_vars pconstruct_real_program_vars
    distribution_real_program_vars term_real_program_vars pconstruct_size List.in_dec
    real_program_var_eq_dec bool_program_var_eq_dec distribution_density term_eval
    satisfies update_real update_real_values real_program_values c_and c_not c_lt
    c_true].
  (* The zero reward integrates to zero under every sampling measure. *)
  zero_sampling_expectation; intro threshold.
  zero_sampling_expectation; intro noisy1.
  zero_sampling_expectation; intro noisy2.
  expose_construct_indicator; apply real_indicator_false.
  repeat match goal with
           | |- context [bool_program_var_eq_dec ?x ?y] =>
               destruct (bool_program_var_eq_dec x y); try congruence
           end.
           cbn [subst_bool_cformula satisfies c_and c_not c_true term_eval
             update_real update_real_values real_program_values].
           repeat match goal with
           | |- context [real_program_var_eq_dec ?x ?y] =>
               destruct (real_program_var_eq_dec x y); try congruence
           end.
           cbn [satisfies c_and c_not c_true term_eval update_real
             update_real_values real_program_values].
           mathcomp_tauto.
Qed.

Lemma svt_symbolic_pre_implies_wp :
  forall epsilon p : R,
    pformula_valid
      [[ $(svt_symbolic_pre epsilon p) -> $(svt_generic_pre epsilon p) ]].
Proof.
  intros epsilon p.
  unfold pformula_valid.
  intros ps Hps_admissible.
  rewrite svt_generic_pre_shape.
  assert (Houter_zero :
    expectation (pstate_measure ps)
      (q_eval (svt_wp_outer_zero_construct epsilon)) = 0%R).
  {
    transitivity
      (expectation (pstate_measure ps) (fun _ : state => 0%R)).
    - apply expectation_extensional.
      intro v; apply svt_wp_outer_zero_construct_eval.
    - apply expectation_zero.
  }
  assert (Hinner_zero :
    expectation (pstate_measure ps)
      (q_eval (svt_wp_inner_zero_construct epsilon)) = 0%R).
  {
    transitivity
      (expectation (pstate_measure ps) (fun _ : state => 0%R)).
    - apply expectation_extensional.
      intro v; apply svt_wp_inner_zero_construct_eval.
    - apply expectation_zero.
  }
  assert (Hpath :
    expectation (pstate_measure ps)
      (q_eval (svt_wp_path_construct epsilon)) =
    expectation (pstate_measure ps)
      (q_eval (svt_path_construct epsilon))).
  {
    apply expectation_extensional.
    intro v; apply svt_wp_path_construct_eval.
  }
  unfold svt_symbolic_pre, normalized.
  cbn [p_and p_not p_eq psatisfies pterm_eval] in *.
  clear Hps_admissible.
  (* Eliminate zero branches before arithmetic automation inspects the
     concrete integral expressions. *)
  rewrite Houter_zero, Hinner_zero, Hpath.
  clear Houter_zero Hinner_zero Hpath.
  intuition lra.
Qed.

Theorem svt_symbolic_hoare :
  forall epsilon p : R,
    (0 < epsilon)%R ->
    {{ $(svt_symbolic_pre epsilon p) }}
      $(svt_two_queries epsilon)
    {{ $(probability_of_bot_top_equals p) }}.
Proof.
  intros epsilon p Hepsilon.
  eapply HConseq with
    (eta1 := svt_generic_pre epsilon p)
    (eta2 := svt_output_probability p).
  - apply svt_symbolic_pre_implies_wp.
  - apply svt_generic_wp_derivable.
    exact Hepsilon.
  - unfold pformula_valid, svt_output_probability,
      svt_event_probability, probability_of_bot_top_equals.
    intros ps Hps_admissible.
    cbn [p_eq p_and p_not psatisfies pterm_eval] in *.
    clear Hps_admissible.
    intuition lra.
Qed.

Definition svt_symbolic_concrete_pre (epsilon p : R) : PFormula :=
  subst_real_pformula svt_q1 <{ 0 }>
    (subst_real_pformula svt_q2 <{ 1 }>
      (svt_symbolic_pre epsilon p)).

Theorem svt_symbolic_concrete_hoare :
  forall epsilon p : R,
    (0 < epsilon)%R ->
    {{ $(svt_symbolic_concrete_pre epsilon p) }}
      $(svt_01 epsilon)
    {{ $(probability_of_bot_top_equals p) }}.
Proof.
  intros epsilon p Hepsilon.
  unfold svt_01, svt_symbolic_concrete_pre.
  eapply HSeq with
    (eta2 := subst_real_pformula svt_q2 (TConst 1)
      (svt_symbolic_pre epsilon p)).
  - apply HRealAssign.
  - eapply HSeq with (eta2 := svt_symbolic_pre epsilon p).
    + apply HRealAssign.
    + apply svt_symbolic_hoare.
      exact Hepsilon.
Qed.

Lemma svt_path_substitution_01 :
  forall epsilon : R,
    subst_real_pconstruct svt_q1 <{ 0 }>
      (subst_real_pconstruct svt_q2 <{ 1 }>
        (svt_path_construct epsilon)) =
      svt_path_construct_01 epsilon.
Proof.
  intro epsilon.
  unfold svt_path_construct, svt_path_construct_01,
    svt_threshold_distribution, svt_query_distribution,
    svt_q1, svt_q2, svt_threshold, svt_noisy1, svt_noisy2.
  cbn [subst_real_pconstruct subst_real_pconstruct_fuel
    subst_real_distribution subst_real_term subst_real_cformula
    pconstruct_size pconstruct_real_program_vars
    distribution_real_program_vars term_real_program_vars
    cformula_real_program_vars List.in_dec real_program_var_eq_dec].
  reflexivity.
Qed.

Lemma svt_symbolic_concrete_pre_shape :
  forall epsilon p : R,
    svt_symbolic_concrete_pre epsilon p =
      [[ $(normalized) /\
         E[$(subst_real_pconstruct svt_q1 <{ 0 }>
           (subst_real_pconstruct svt_q2 <{ 1 }>
             (svt_path_construct epsilon)))] = $(p) ]].
Proof.
  intros epsilon p.
  unfold svt_symbolic_concrete_pre, svt_symbolic_pre, normalized.
  cbn [subst_real_pformula subst_real_pterm].
  reflexivity.
Qed.


(** The headline triple: the probability of (bot, top) on the query vector
    (0, 1) is the state-logic path integral in the precondition. *)
Theorem svt_01_bot_top_probability :
  forall epsilon p : R,
    (0 < epsilon)%R ->
    {{ $(normalized) /\ E[$(svt_path_construct_01 epsilon)] = $(p) }}
      $(svt_01 epsilon)
    {{ $(probability_of_bot_top_equals p) }}.
Proof.
  intros epsilon p Hepsilon.
  pose proof (svt_symbolic_concrete_hoare epsilon p Hepsilon) as H.
  rewrite svt_symbolic_concrete_pre_shape, svt_path_substitution_01 in H.
  exact H.
Qed.
