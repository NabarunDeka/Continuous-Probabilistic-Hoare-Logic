(** Fixed-horizon Monte Carlo estimator for the area of a quarter disk. *)

From Stdlib Require Import Reals.
From Stdlib Require Import Reals.Binomial.
From Stdlib Require Import Reals.Machin.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lia.
From Stdlib Require Import Lra.
From Stdlib Require Import Psatz.
From Stdlib Require Import Field.
From Stdlib Require Import Ring.
From Stdlib Require Import ClassicalDescription.
From Stdlib Require Import Logic.FunctionalExtensionality.

Require Import CPHL.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.
Import ListNotations.

(** Program variables and readable surface syntax. *)
Definition monte_carlo_i : RealProgramVar := real_program_var "mc_i".
Definition monte_carlo_H : RealProgramVar := real_program_var "mc_H".
Definition monte_carlo_X : RealProgramVar := real_program_var "mc_X".
Definition monte_carlo_Y : RealProgramVar := real_program_var "mc_Y".

Definition monte_carlo_guard (M : nat) : CFormula :=
  <{ 0 <= monte_carlo_i /\ monte_carlo_i < $(INR M) }>.

Definition monte_carlo_hit : CFormula :=
  <{ monte_carlo_X * monte_carlo_X + monte_carlo_Y * monte_carlo_Y <= 1 }>.

Definition monte_carlo_body : Cmd :=
  <{
    monte_carlo_X sample uniform ( 0, 1 );
    monte_carlo_Y sample uniform ( 0, 1 );
    if $(monte_carlo_hit) then
      monte_carlo_H := monte_carlo_H + 1
    else skip end;
    monte_carlo_i := monte_carlo_i + 1
  }>.

Definition monte_carlo_estimator (M : nat) : Cmd :=
  <{
    monte_carlo_i := 0;
    monte_carlo_H := 0;
    while $(monte_carlo_guard M) do $(monte_carlo_body) end
  }>.

Definition monte_carlo_target (k : nat) : CFormula :=
  <{ monte_carlo_H = $(INR k) }>.

Definition monte_carlo_not_target (k : nat) : CFormula :=
  <{ ~ $(monte_carlo_target k) }>.

Definition monte_carlo_normalized : PFormula :=
  [[ Pr[true] = 1 ]].

Definition monte_carlo_hit_probability : R := (PI / 4)%R.

Definition monte_carlo_binomial_mass (M k : nat) : R :=
  (C M k * monte_carlo_hit_probability ^ k *
    (1 - monte_carlo_hit_probability) ^ (M - k))%R.

(** Probability constructs used for the two independent uniform samples. *)
Definition monte_carlo_hit_construct : PConstruct :=
  [[
    integral monte_carlo_X ~ uniform ( 0, 1 ),
    integral monte_carlo_Y ~ uniform ( 0, 1 ),
    indicator[$(monte_carlo_hit)]
  ]].

Definition monte_carlo_miss_construct : PConstruct :=
  [[
    integral monte_carlo_X ~ uniform ( 0, 1 ),
    integral monte_carlo_Y ~ uniform ( 0, 1 ),
    indicator[~ $(monte_carlo_hit)]
  ]].

Definition monte_carlo_two_uniforms_construct : PConstruct :=
  [[
    integral monte_carlo_X ~ uniform ( 0, 1 ),
    integral monte_carlo_Y ~ uniform ( 0, 1 ),
    indicator[true]
  ]].

Lemma monte_carlo_uniform_density_eval :
  forall (v : state) (z : R),
    distribution_density <{ uniform ( 0, 1 ) }> v z =
      real_indicator (0 <= z /\ z <= 1)%R.
Proof.
  intros v z.
  cbn [distribution_density term_eval Rdiv].
  rewrite Rminus_0_r, Rdiv_1_r.
  reflexivity.
Qed.

Lemma monte_carlo_uniform_integral_one :
  real_integral
    (fun z => distribution_density <{ uniform ( 0, 1 ) }>
      (update_real
        {| real_program_values := fun _ => 0%R;
           bool_program_values := fun _ => false;
           real_logic_values := fun _ => 0%R;
           bool_logic_values := fun _ => false |}
        monte_carlo_X 0) z) = 1%R.
Proof.
  transitivity
    (real_integral
      (fun z => real_indicator (0 <= z /\ z <= 1)%R / (1 - 0))).
  - apply real_integral_extensional.
    intro z; cbn [distribution_density term_eval]; reflexivity.
  - apply real_integral_uniform_density; lra.
Qed.

(** The constant parameters make uniform normalization state-independent. *)
Lemma monte_carlo_uniform_integral_state_independent :
  forall v : state,
    real_integral
      (fun z => distribution_density <{ uniform ( 0, 1 ) }> v z) = 1%R.
Proof.
  intro v.
  transitivity
    (real_integral
      (fun z => real_indicator (0 <= z /\ z <= 1)%R / (1 - 0))).
  - apply real_integral_extensional.
    intro z; cbn [distribution_density term_eval]; reflexivity.
  - apply real_integral_uniform_density; lra.
Qed.

Lemma monte_carlo_two_uniforms_eval :
  forall v : state,
    q_eval monte_carlo_two_uniforms_construct v = 1%R.
Proof.
  intro v.
  unfold monte_carlo_two_uniforms_construct.
  change
    (real_integral
      (fun x =>
        distribution_density <{ uniform ( 0, 1 ) }> v x *
        real_integral
          (fun y =>
            distribution_density <{ uniform ( 0, 1 ) }>
              (update_real v monte_carlo_X x) y *
            real_indicator
              (satisfies
                (update_real
                  (update_real v monte_carlo_X x) monte_carlo_Y y)
                c_true))) = 1%R).
  transitivity
    (real_integral
      (fun x =>
        distribution_density <{ uniform ( 0, 1 ) }> v x * 1)).
  - apply real_integral_extensional.
    intro x.
    cbn [c_true satisfies].
    rewrite real_indicator_true by tauto.
    replace
      (real_integral
        (fun y =>
          distribution_density <{ uniform ( 0, 1 ) }>
            (update_real v monte_carlo_X x) y * 1))
      with
      (real_integral
        (fun y =>
          distribution_density <{ uniform ( 0, 1 ) }>
            (update_real v monte_carlo_X x) y)).
    2:{ apply real_integral_extensional; intro y; ring. }
    rewrite monte_carlo_uniform_integral_state_independent.
    ring.
  - transitivity
      (real_integral
        (fun x => distribution_density <{ uniform ( 0, 1 ) }> v x)).
    + apply real_integral_extensional; intro x; ring.
    + apply monte_carlo_uniform_integral_state_independent.
Qed.

Lemma monte_carlo_hit_construct_eval :
  forall v : state,
    q_eval monte_carlo_hit_construct v = monte_carlo_hit_probability.
Proof.
  intro v.
  unfold monte_carlo_hit_construct, monte_carlo_hit_probability,
    monte_carlo_hit.
  cbn [q_eval distribution_density term_eval update_real update_real_values].
  repeat match goal with
  | |- context [real_program_var_eq_dec ?x ?y] =>
      destruct (real_program_var_eq_dec x y); [congruence |]
  end.
  transitivity
    (real_integral
      (fun x =>
        real_indicator (0 <= x /\ x <= 1)%R *
        real_integral
          (fun y =>
            real_indicator (0 <= y /\ y <= 1)%R *
            real_indicator (x * x + y * y <= 1)%R))).
  - apply real_integral_extensional.
    intro x.
    apply f_equal2 with (f := Rmult).
    + rewrite Rminus_0_r, Rdiv_1_r; reflexivity.
    + apply real_integral_extensional.
      intro y.
      rewrite Rminus_0_r, Rdiv_1_r.
      apply f_equal2 with (f := Rmult); [reflexivity |].
      apply real_indicator_extensional.
      cbn [satisfies term_eval update_real update_real_values].
      repeat match goal with
      | |- context [real_program_var_eq_dec ?a ?b] =>
          destruct (real_program_var_eq_dec a b); [congruence |]
      end.
      tauto.
  - apply real_integral_unit_square_quarter_disk.
Qed.

Lemma monte_carlo_indicator_complement :
  forall P : Prop,
    (real_indicator P + real_indicator (~ P) = 1)%R.
Proof.
  intro P.
  destruct (excluded_middle_informative P) as [HP | HnP].
  - rewrite (real_indicator_true P HP).
    rewrite (real_indicator_false (~ P)) by tauto.
    ring.
  - rewrite (real_indicator_false P HnP).
    rewrite (real_indicator_true (~ P) HnP).
    ring.
Qed.

Lemma monte_carlo_miss_construct_eval :
  forall v : state,
    q_eval monte_carlo_miss_construct v =
      (1 - monte_carlo_hit_probability)%R.
Proof.
  intro v.
  assert (Hpartition :
    (q_eval monte_carlo_hit_construct v +
      q_eval monte_carlo_miss_construct v =
      q_eval monte_carlo_two_uniforms_construct v)%R).
  {
    unfold monte_carlo_hit_construct, monte_carlo_miss_construct,
      monte_carlo_two_uniforms_construct, monte_carlo_hit.
    cbn [q_eval].
    rewrite <- real_integral_add.
    apply real_integral_extensional.
    intro x.
    rewrite <- Rmult_plus_distr_l.
    apply f_equal2 with (f := Rmult); [reflexivity |].
    rewrite <- real_integral_add.
    apply real_integral_extensional.
    intro y.
    cbn [c_not c_true satisfies].
    replace (real_indicator (False -> False)) with 1%R.
    2:{ symmetry; apply real_indicator_true; tauto. }
    match goal with
    | |- ?d * real_indicator ?P + ?d * real_indicator (?P -> False) =
          ?d * 1 =>
        pose proof (monte_carlo_indicator_complement P) as Hind;
        replace (P -> False) with (~ P) by tauto;
        nra
    end.
  }
  rewrite monte_carlo_hit_construct_eval in Hpartition.
  rewrite monte_carlo_two_uniforms_eval in Hpartition.
  lra.
Qed.

Lemma monte_carlo_hit_probability_bounds :
  (0 < monte_carlo_hit_probability < 1)%R.
Proof.
  unfold monte_carlo_hit_probability.
  pose proof PI_RGT_0 as Hpositive.
  pose proof (PI_2_3_7_ineq 0%nat) as [_ Hupper].
  replace (2 * 0)%nat with 0%nat in Hupper by lia.
  cbn [sum_f_R0] in Hupper.
  unfold tg_alt, PI_2_3_7_tg, Ratan_seq in Hupper.
  cbn in Hupper.
  assert (H3 : (3 * / 3 = 1)%R) by (apply Rinv_r; lra).
  assert (H7 : (7 * / 7 = 1)%R) by (apply Rinv_r; lra).
  lra.
Qed.

(** Recursive Bernoulli point masses.  The recursion is convenient for the
    while fixed-point proof; the closed form is proved below. *)
Fixpoint monte_carlo_bernoulli_mass (r s : nat) : R :=
  match r, s with
  | O, O => 1%R
  | O, S _ => 0%R
  | S r', O =>
      ((1 - monte_carlo_hit_probability) *
        monte_carlo_bernoulli_mass r' O)%R
  | S r', S s' =>
      (monte_carlo_hit_probability *
          monte_carlo_bernoulli_mass r' s' +
       (1 - monte_carlo_hit_probability) *
          monte_carlo_bernoulli_mass r' (S s'))%R
  end.

Lemma monte_carlo_bernoulli_mass_outside :
  forall r s : nat,
    (r < s)%nat -> monte_carlo_bernoulli_mass r s = 0%R.
Proof.
  induction r as [|r IHr]; intros s Hrs.
  - destruct s; cbn; [lia | reflexivity].
  - destruct s as [|s].
    + lia.
    + cbn.
      rewrite IHr by lia.
      rewrite IHr by lia.
      ring.
Qed.

Lemma monte_carlo_bernoulli_mass_bounds :
  forall r s : nat,
    (0 <= monte_carlo_bernoulli_mass r s <= 1)%R.
Proof.
  induction r as [|r IHr]; intro s.
  - destruct s; cbn; lra.
  - destruct s as [|s].
    + cbn.
      pose proof (IHr 0%nat) as Hr0.
      pose proof monte_carlo_hit_probability_bounds.
      nra.
    + cbn.
      pose proof (IHr s) as Hrs.
      pose proof (IHr (S s)) as HrSs.
      pose proof monte_carlo_hit_probability_bounds.
      nra.
Qed.

Lemma monte_carlo_binomial_zero :
  forall r : nat, C r 0%nat = 1%R.
Proof.
  intro r.
  unfold C.
  rewrite Nat.sub_0_r.
  cbn [Factorial.fact].
  rewrite Rmult_1_l.
  apply Rdiv_diag.
  apply not_0_INR.
  apply Factorial.fact_neq_0.
Qed.

Lemma monte_carlo_binomial_diagonal :
  forall r : nat, C r r = 1%R.
Proof.
  intro r.
  unfold C.
  rewrite Nat.sub_diag.
  cbn [Factorial.fact].
  rewrite Rmult_1_r.
  apply Rdiv_diag.
  apply not_0_INR.
  apply Factorial.fact_neq_0.
Qed.

Lemma monte_carlo_bernoulli_mass_closed_form :
  forall r s : nat,
    (s <= r)%nat ->
    monte_carlo_bernoulli_mass r s =
      (C r s * monte_carlo_hit_probability ^ s *
        (1 - monte_carlo_hit_probability) ^ (r - s))%R.
Proof.
  induction r as [|r IHr]; intros s Hsr.
  - assert (s = 0)%nat by lia; subst s.
    cbn [monte_carlo_bernoulli_mass].
    rewrite monte_carlo_binomial_zero.
    replace (0 - 0)%nat with 0%nat by lia.
    cbn [pow].
    ring.
  - destruct s as [|s].
    + cbn [monte_carlo_bernoulli_mass].
      rewrite IHr by lia.
      rewrite !monte_carlo_binomial_zero.
      rewrite !Nat.sub_0_r.
      cbn [pow].
      ring.
    + destruct (Nat.eq_dec s r) as [Hsr_eq | Hsr_neq].
      * subst s.
        cbn [monte_carlo_bernoulli_mass].
        rewrite IHr by lia.
        rewrite monte_carlo_bernoulli_mass_outside by lia.
        rewrite monte_carlo_binomial_diagonal.
        rewrite monte_carlo_binomial_diagonal.
        rewrite !Nat.sub_diag.
        cbn [pow].
        cbn [pow].
        ring.
      * assert (Hsr_lt : (s < r)%nat) by lia.
        cbn [monte_carlo_bernoulli_mass].
        rewrite IHr by lia.
        rewrite IHr by lia.
        rewrite <- pascal by exact Hsr_lt.
        replace (S r - S s)%nat with (r - s)%nat by lia.
        cbn [pow].
        replace (r - s)%nat with (S (r - S s))%nat by lia.
        cbn [pow].
        ring.
Qed.

Corollary monte_carlo_bernoulli_mass_is_binomial :
  forall M k : nat,
    (k <= M)%nat ->
    monte_carlo_bernoulli_mass M k = monte_carlo_binomial_mass M k.
Proof.
  intros M k Hk.
  apply monte_carlo_bernoulli_mass_closed_form; exact Hk.
Qed.

(** Hoare-logic plumbing for exact event probabilities. *)
Definition monte_carlo_event_probability
  (r : R) (gamma : CFormula) : PFormula :=
  [[ $(r) = Pr[$(gamma)] ]].

Definition monte_carlo_hit_mass_var : ProbLogicVar :=
  prob_logic_var "mc_hit_mass".

Definition monte_carlo_miss_mass_var : ProbLogicVar :=
  prob_logic_var "mc_miss_mass".

Definition monte_carlo_rigid_constant
  (y : ProbLogicVar) (r : R) : PFormula :=
  [[ y = $(r) ]].

Lemma monte_carlo_rigid_constant_analytical :
  forall (y : ProbLogicVar) (r : R),
    pformula_analytical (monte_carlo_rigid_constant y r).
Proof.
  intros y r.
  cbn [monte_carlo_rigid_constant p_eq p_and p_not
    pformula_analytical pterm_analytical].
  tauto.
Qed.

Lemma monte_carlo_add_rigid_constant :
  forall (eta : PFormula) (s : Cmd) (gamma : CFormula)
    (y : ProbLogicVar) (r : R),
    {{ $(eta) }} $(s) {{ $(monte_carlo_event_probability r gamma) }} ->
    {{ $(eta) /\ $(monte_carlo_rigid_constant y r) }} $(s)
      {{ y = Pr[$(gamma)] }}.
Proof.
  intros eta s gamma y r Hbranch.
  assert (Hevent :
    {{ $(eta) /\ $(monte_carlo_rigid_constant y r) }} $(s)
      {{ $(monte_carlo_event_probability r gamma) }}).
  {
    eapply HConseq with
      (eta1 := eta) (eta2 := monte_carlo_event_probability r gamma).
    - unfold pformula_valid.
      intro ps; cbn [p_and p_not psatisfies]; tauto.
    - exact Hbranch.
    - unfold pformula_valid.
      intro ps; cbn [psatisfies]; tauto.
  }
  assert (Hrigid :
    {{ $(eta) /\ $(monte_carlo_rigid_constant y r) }} $(s)
      {{ $(monte_carlo_rigid_constant y r) }}).
  {
    eapply HConseq with
      (eta1 := monte_carlo_rigid_constant y r)
      (eta2 := monte_carlo_rigid_constant y r).
    - unfold pformula_valid.
      intro ps; cbn [p_and p_not psatisfies]; tauto.
    - apply HFree.
      apply monte_carlo_rigid_constant_analytical.
    - unfold pformula_valid.
      intro ps; cbn [psatisfies]; tauto.
  }
  eapply HConseq with
    (eta1 := [[ $(eta) /\ $(monte_carlo_rigid_constant y r) ]])
    (eta2 := [[ $(monte_carlo_event_probability r gamma) /\
      $(monte_carlo_rigid_constant y r) ]]).
  - unfold pformula_valid.
    intro ps; cbn [psatisfies]; tauto.
  - apply HAnd; assumption.
  - unfold pformula_valid, monte_carlo_event_probability,
      monte_carlo_rigid_constant.
    intro ps.
    cbn [p_and p_not p_eq psatisfies pterm_eval] in *.
    intuition lra.
Qed.

Lemma monte_carlo_if_constants :
  forall (eta1 eta2 : PFormula) (guard gamma : CFormula)
    (s1 s2 : Cmd) (r1 r2 : R),
    {{ $(eta1) }} $(s1)
      {{ $(monte_carlo_event_probability r1 gamma) }} ->
    {{ $(eta2) }} $(s2)
      {{ $(monte_carlo_event_probability r2 gamma) }} ->
    {{ $(subst_prob_pformula monte_carlo_hit_mass_var [[ $(r1) ]]
          (subst_prob_pformula monte_carlo_miss_mass_var [[ $(r2) ]]
            (if_precondition eta1 eta2 guard))) }}
      if $(guard) then $(s1) else $(s2) end
    {{ $(monte_carlo_event_probability (r1 + r2) gamma) }}.
Proof.
  intros eta1 eta2 guard gamma s1 s2 r1 r2 Hbranch1 Hbranch2.
  set (base := if_precondition eta1 eta2 guard).
  set (eq1 := monte_carlo_rigid_constant monte_carlo_hit_mass_var r1).
  set (eq2 := monte_carlo_rigid_constant monte_carlo_miss_mass_var r2).
  assert (Hif :
    {{ $(if_precondition [[ $(eta1) /\ $(eq1) ]]
          [[ $(eta2) /\ $(eq2) ]] guard) }}
      if $(guard) then $(s1) else $(s2) end
    {{ monte_carlo_hit_mass_var + monte_carlo_miss_mass_var =
       Pr[$(gamma)] }}).
  {
    apply HIfEq with
      (eta1 := [[ $(eta1) /\ $(eq1) ]])
      (eta2 := [[ $(eta2) /\ $(eq2) ]]).
    - unfold eq1.
      apply monte_carlo_add_rigid_constant; exact Hbranch1.
    - unfold eq2.
      apply monte_carlo_add_rigid_constant; exact Hbranch2.
  }
  set (with_constants := [[ ($(base) /\ $(eq1)) /\ $(eq2) ]]).
  assert (Hif_from_constants :
    {{ $(with_constants) }}
      if $(guard) then $(s1) else $(s2) end
    {{ monte_carlo_hit_mass_var + monte_carlo_miss_mass_var =
       Pr[$(gamma)] }}).
  {
    eapply HConseq with
      (eta1 := if_precondition [[ $(eta1) /\ $(eq1) ]]
        [[ $(eta2) /\ $(eq2) ]] guard)
      (eta2 := [[ monte_carlo_hit_mass_var +
        monte_carlo_miss_mass_var = Pr[$(gamma)] ]]).
    - unfold pformula_valid, with_constants, base, eq1, eq2,
        if_precondition, monte_carlo_rigid_constant.
      intro ps.
      cbn [condition_pformula condition_pterm p_and p_not p_eq
        psatisfies pterm_eval] in *.
      intuition lra.
    - exact Hif.
    - unfold pformula_valid.
      intro ps; cbn [psatisfies]; tauto.
  }
  assert (Hconstants :
    {{ $(with_constants) }}
      if $(guard) then $(s1) else $(s2) end
    {{ $(eq1) /\ $(eq2) }}).
  {
    eapply HConseq with
      (eta1 := [[ $(eq1) /\ $(eq2) ]])
      (eta2 := [[ $(eq1) /\ $(eq2) ]]).
    - unfold pformula_valid, with_constants.
      intro ps; cbn [p_and p_not psatisfies]; tauto.
    - apply HFree.
      unfold eq1, eq2.
      cbn [monte_carlo_rigid_constant p_eq p_and p_not
        pformula_analytical pterm_analytical].
      tauto.
    - unfold pformula_valid.
      intro ps; cbn [psatisfies]; tauto.
  }
  assert (Hwithout_rigids :
    {{ $(with_constants) }}
      if $(guard) then $(s1) else $(s2) end
    {{ $(monte_carlo_event_probability (r1 + r2) gamma) }}).
  {
    eapply HConseq with
      (eta1 := with_constants)
      (eta2 := [[
        (monte_carlo_hit_mass_var + monte_carlo_miss_mass_var =
          Pr[$(gamma)]) /\ $(eq1) /\ $(eq2)
      ]]).
    - unfold pformula_valid.
      intro ps; cbn [psatisfies]; tauto.
    - apply HAnd; assumption.
    - unfold pformula_valid, monte_carlo_event_probability, eq1, eq2,
        monte_carlo_rigid_constant.
      intro ps.
      cbn [p_and p_not p_eq psatisfies pterm_eval] in *.
      intuition lra.
  }
  assert (Helim_miss :
    {{ $(subst_prob_pformula monte_carlo_miss_mass_var [[ $(r2) ]]
          [[ $(base) /\ $(eq1) ]]) }}
      if $(guard) then $(s1) else $(s2) end
    {{ $(monte_carlo_event_probability (r1 + r2) gamma) }}).
  {
    eapply HElimv with
      (eta1 := [[ $(base) /\ $(eq1) ]])
      (y := monte_carlo_miss_mass_var) (p := [[ $(r2) ]]).
    - change ({{ $(with_constants) }}
        if $(guard) then $(s1) else $(s2) end
        {{ $(monte_carlo_event_probability (r1 + r2) gamma) }}).
      exact Hwithout_rigids.
    - cbn [prob_logic_var_occurs_pterm]; tauto.
    - cbn [monte_carlo_event_probability p_eq p_and p_not
        prob_logic_var_occurs_pformula prob_logic_var_occurs_pterm].
      tauto.
  }
  assert (Helim_hit :
    {{ $(subst_prob_pformula monte_carlo_hit_mass_var [[ $(r1) ]]
          (subst_prob_pformula monte_carlo_miss_mass_var [[ $(r2) ]] base)) }}
      if $(guard) then $(s1) else $(s2) end
    {{ $(monte_carlo_event_probability (r1 + r2) gamma) }}).
  {
    eapply HElimv with
      (eta1 := subst_prob_pformula monte_carlo_miss_mass_var
        [[ $(r2) ]] base)
      (y := monte_carlo_hit_mass_var) (p := [[ $(r1) ]]).
    - change ({{ $(subst_prob_pformula monte_carlo_miss_mass_var
          [[ $(r2) ]] [[ $(base) /\ $(eq1) ]]) }}
        if $(guard) then $(s1) else $(s2) end
        {{ $(monte_carlo_event_probability (r1 + r2) gamma) }}).
      exact Helim_miss.
    - cbn [prob_logic_var_occurs_pterm]; tauto.
    - cbn [monte_carlo_event_probability p_eq p_and p_not
        prob_logic_var_occurs_pformula prob_logic_var_occurs_pterm].
      tauto.
  }
  unfold base in Helim_hit.
  exact Helim_hit.
Qed.

Lemma monte_carlo_uniform_valid :
  pformula_valid
    [[ almost_sure[$(distribution_valid_formula
      <{ uniform ( 0, 1 ) }>)] ]].
Proof.
  intro ps.
  unfold p_almost_sure, p_eq.
  cbn [p_and p_not psatisfies pterm_eval].
  assert (Heq :
    expectation (pstate_measure ps)
      (q_eval [[ indicator[$(distribution_valid_formula
        <{ uniform ( 0, 1 ) }>)] ]]) =
    expectation (pstate_measure ps) (q_eval [[ indicator[true] ]])).
  {
    rewrite !expectation_indicator.
    apply measure_extensional.
    intro v.
    unfold formula_assertion, distribution_valid_formula, c_lt, c_not,
      c_true.
    cbn [satisfies term_eval].
    split.
    - intros _ Hfalse; exact Hfalse.
    - intros _ Hfalse; lra.
  }
  lra.
Qed.

Lemma monte_carlo_uniform_sample :
  forall (eta : PFormula) (x : RealProgramVar),
    {{ $(sample_pformula x <{ uniform ( 0, 1 ) }> eta) }}
      x sample uniform ( 0, 1 )
    {{ $(eta) }}.
Proof.
  intros eta x.
  apply HRealSample.
  - unfold pformula_valid.
    intro ps; cbn [psatisfies]; tauto.
  - unfold pformula_valid.
    intros ps _.
    apply monte_carlo_uniform_valid.
Qed.

Definition monte_carlo_after_i (gamma : CFormula) : CFormula :=
  subst_real_cformula monte_carlo_i <{ monte_carlo_i + 1 }> gamma.

Definition monte_carlo_after_hit (gamma : CFormula) : CFormula :=
  subst_real_cformula monte_carlo_H <{ monte_carlo_H + 1 }>
    (monte_carlo_after_i gamma).

Definition monte_carlo_if_wp
  (gamma : CFormula) (rhit rmiss : R) : PFormula :=
  subst_prob_pformula monte_carlo_hit_mass_var [[ $(rhit) ]]
    (subst_prob_pformula monte_carlo_miss_mass_var [[ $(rmiss) ]]
      (if_precondition
        (monte_carlo_event_probability rhit
          (monte_carlo_after_hit gamma))
        (monte_carlo_event_probability rmiss
          (monte_carlo_after_i gamma))
        monte_carlo_hit)).

Definition monte_carlo_body_wp
  (gamma : CFormula) (rhit rmiss : R) : PFormula :=
  sample_pformula monte_carlo_X <{ uniform ( 0, 1 ) }>
    (sample_pformula monte_carlo_Y <{ uniform ( 0, 1 ) }>
      (monte_carlo_if_wp gamma rhit rmiss)).

Lemma monte_carlo_body_event_derivable :
  forall (gamma : CFormula) (rhit rmiss : R),
    {{ $(monte_carlo_body_wp gamma rhit rmiss) }}
      $(monte_carlo_body)
    {{ $(monte_carlo_event_probability (rhit + rmiss) gamma) }}.
Proof.
  intros gamma rhit rmiss.
  unfold monte_carlo_body, monte_carlo_body_wp.
  eapply HSeq with
    (eta2 := sample_pformula monte_carlo_Y <{ uniform ( 0, 1 ) }>
      (monte_carlo_if_wp gamma rhit rmiss)).
  - apply monte_carlo_uniform_sample.
  - eapply HSeq with (eta2 := monte_carlo_if_wp gamma rhit rmiss).
    + apply monte_carlo_uniform_sample.
    + eapply HSeq with
        (eta2 := monte_carlo_event_probability (rhit + rmiss)
          (monte_carlo_after_i gamma)).
      * unfold monte_carlo_if_wp.
        apply monte_carlo_if_constants.
        -- unfold monte_carlo_after_hit.
           change
             ({{ $(subst_real_pformula monte_carlo_H
                    <{ monte_carlo_H + 1 }>
                    (monte_carlo_event_probability rhit
                      (monte_carlo_after_i gamma))) }}
                monte_carlo_H := monte_carlo_H + 1
              {{ $(monte_carlo_event_probability rhit
                    (monte_carlo_after_i gamma)) }}).
           apply HRealAssign.
        -- apply HSkip.
      * unfold monte_carlo_after_i.
        change
          ({{ $(subst_real_pformula monte_carlo_i
                 <{ monte_carlo_i + 1 }>
                 (monte_carlo_event_probability (rhit + rmiss) gamma)) }}
             monte_carlo_i := monte_carlo_i + 1
           {{ $(monte_carlo_event_probability (rhit + rmiss) gamma) }}).
        apply HRealAssign.
Qed.

Definition monte_carlo_hit_pre_construct (gamma : CFormula) : PConstruct :=
  [[
    integral monte_carlo_X ~ uniform ( 0, 1 ),
    integral monte_carlo_Y ~ uniform ( 0, 1 ),
    indicator[$(monte_carlo_after_hit gamma) /\ $(monte_carlo_hit)]
  ]].

Definition monte_carlo_miss_pre_construct (gamma : CFormula) : PConstruct :=
  [[
    integral monte_carlo_X ~ uniform ( 0, 1 ),
    integral monte_carlo_Y ~ uniform ( 0, 1 ),
    indicator[$(monte_carlo_after_i gamma) /\ (~ $(monte_carlo_hit))]
  ]].

Lemma monte_carlo_body_wp_shape :
  forall (gamma : CFormula) (rhit rmiss : R),
    monte_carlo_body_wp gamma rhit rmiss =
      [[
        $(rhit) = E[$(monte_carlo_hit_pre_construct gamma)] /\
        $(rmiss) = E[$(monte_carlo_miss_pre_construct gamma)]
      ]].
Proof.
  intros gamma rhit rmiss.
  unfold monte_carlo_body_wp, monte_carlo_if_wp,
    monte_carlo_event_probability, monte_carlo_hit_pre_construct,
    monte_carlo_miss_pre_construct.
  cbn [sample_pformula sample_pterm subst_prob_pformula
    subst_prob_pterm if_precondition condition_pformula condition_pterm
    condition_pconstruct condition_pconstruct_fuel p_eq p_and p_not].
  reflexivity.
Qed.

(** Rectangular enumeration of the finite region family.  Each block has the
    exact slots [0..r], one catch-all slot [M+1], and syntactically false
    padding slots.  The padding keeps index arithmetic transparent and cannot
    contain program mass. *)
Definition monte_carlo_time_band (M r : nat) : CFormula :=
  <{
    $(INR (M - r)) <= monte_carlo_i /\
    monte_carlo_i < $(INR (M - r + 1))
  }>.

Definition monte_carlo_exact_region
  (M k r s : nat) : CFormula :=
  <{
    $(monte_carlo_time_band M r) /\
    monte_carlo_H = $(INR k - INR s)
  }>.

Definition monte_carlo_exact_regions (M k r : nat) : CFormula :=
  finite_c_or (S r) (fun s => monte_carlo_exact_region M k r s).

Definition monte_carlo_other_region (M k r : nat) : CFormula :=
  <{
    $(monte_carlo_time_band M r) /\
    ~ $(monte_carlo_exact_regions M k r)
  }>.

Definition monte_carlo_block_width (M : nat) : nat := S (S M).

Definition monte_carlo_region_count (M : nat) : nat :=
  (monte_carlo_block_width M * M)%nat.

Definition monte_carlo_region_remaining (M index : nat) : nat :=
  S (index / monte_carlo_block_width M).

Definition monte_carlo_region_slot (M index : nat) : nat :=
  index mod monte_carlo_block_width M.

Definition monte_carlo_region (M k index : nat) : CFormula :=
  let r := monte_carlo_region_remaining M index in
  let s := monte_carlo_region_slot M index in
  if Nat.leb r M then
    if Nat.leb s r then monte_carlo_exact_region M k r s
    else if Nat.eqb s (S M) then monte_carlo_other_region M k r
    else FFalse
  else FFalse.

Definition monte_carlo_region_index (M r s : nat) : nat :=
  ((r - 1) * monte_carlo_block_width M + s)%nat.

Lemma monte_carlo_block_width_positive :
  forall M : nat, (0 < monte_carlo_block_width M)%nat.
Proof. intros M; unfold monte_carlo_block_width; lia. Qed.

Lemma monte_carlo_region_decode_index :
  forall M r s : nat,
    (1 <= r <= M)%nat ->
    (s < monte_carlo_block_width M)%nat ->
    monte_carlo_region_remaining M (monte_carlo_region_index M r s) = r /\
    monte_carlo_region_slot M (monte_carlo_region_index M r s) = s.
Proof.
  intros M r s Hr Hs.
  unfold monte_carlo_region_remaining, monte_carlo_region_slot,
    monte_carlo_region_index.
  set (w := monte_carlo_block_width M).
  assert (Hw : w <> 0%nat) by
    (unfold w; pose proof (monte_carlo_block_width_positive M); lia).
  split.
  - rewrite Nat.div_add_l by exact Hw.
    rewrite Nat.div_small by exact Hs.
    lia.
  - rewrite Nat.add_comm.
    rewrite Nat.Private_NDivProp.mod_add by exact Hw.
    rewrite Nat.mod_small by exact Hs.
    reflexivity.
Qed.

Lemma monte_carlo_region_index_bound :
  forall M r s : nat,
    (1 <= r <= M)%nat ->
    (s < monte_carlo_block_width M)%nat ->
    (monte_carlo_region_index M r s < monte_carlo_region_count M)%nat.
Proof.
  intros M r s Hr Hs.
  unfold monte_carlo_region_index, monte_carlo_region_count.
  nia.
Qed.

Lemma monte_carlo_region_index_exact :
  forall M k r s : nat,
    (1 <= r <= M)%nat ->
    (s <= r)%nat ->
    monte_carlo_region M k (monte_carlo_region_index M r s) =
      monte_carlo_exact_region M k r s.
Proof.
  intros M k r s Hr Hsr.
  assert (Hs : (s < monte_carlo_block_width M)%nat).
  { unfold monte_carlo_block_width; lia. }
  pose proof (monte_carlo_region_decode_index M r s Hr Hs)
    as [Hremaining Hslot].
  unfold monte_carlo_region.
  rewrite Hremaining, Hslot.
  assert (HrM : (r <=? M)%nat = true) by (apply Nat.leb_le; lia).
  assert (Hsr' : (s <=? r)%nat = true) by (apply Nat.leb_le; lia).
  rewrite HrM, Hsr'.
  reflexivity.
Qed.

Lemma monte_carlo_region_index_other :
  forall M k r : nat,
    (1 <= r <= M)%nat ->
    monte_carlo_region M k (monte_carlo_region_index M r (S M)) =
      monte_carlo_other_region M k r.
Proof.
  intros M k r Hr.
  assert (Hs : (S M < monte_carlo_block_width M)%nat) by
    (unfold monte_carlo_block_width; lia).
  pose proof (monte_carlo_region_decode_index M r (S M) Hr Hs)
    as [Hremaining Hslot].
  unfold monte_carlo_region.
  rewrite Hremaining, Hslot.
  assert (HrM : (r <=? M)%nat = true) by (apply Nat.leb_le; lia).
  assert (Hslotr : (S M <=? r)%nat = false) by
    (apply Nat.leb_gt; lia).
  rewrite HrM, Hslotr.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Lemma monte_carlo_region_bounded_decode :
  forall M index : nat,
    (index < monte_carlo_region_count M)%nat ->
    (1 <= monte_carlo_region_remaining M index <= M)%nat /\
    (monte_carlo_region_slot M index < monte_carlo_block_width M)%nat.
Proof.
  intros M index Hindex.
  assert (Hw : monte_carlo_block_width M <> 0%nat) by
    (pose proof (monte_carlo_block_width_positive M); lia).
  split.
  - assert (Hdiv :
      (index / monte_carlo_block_width M < M)%nat).
    {
      apply Nat.Private_NDivProp.div_lt_upper_bound; [exact Hw |].
      exact Hindex.
    }
    unfold monte_carlo_region_remaining.
    lia.
  - unfold monte_carlo_region_slot.
    apply Nat.mod_upper_bound; exact Hw.
Qed.

Lemma monte_carlo_finite_c_or_spec :
  forall (n : nat) (formulas : nat -> CFormula) (v : state),
    satisfies v (finite_c_or n formulas) <->
      exists j : nat, (j < n)%nat /\ satisfies v (formulas j).
Proof.
  induction n as [|n IH]; intros formulas v.
  - cbn [finite_c_or satisfies]; split; [tauto |].
    intros Hex.
    destruct Hex as [j Hex].
    destruct Hex as [Hj Hsat].
    lia.
  - cbn [finite_c_or c_or c_not satisfies].
    rewrite IH.
    split.
    + intro Hor.
      assert (Hcases :
        (exists j : nat, (j < n)%nat /\ satisfies v (formulas j)) \/
        satisfies v (formulas n)) by tauto.
      destruct Hcases as [Hex | Hsat].
      * destruct Hex as [j Hex].
        destruct Hex as [Hj Hsat].
        exists j; split; [lia | exact Hsat].
      * exists n; split; [lia | exact Hsat].
    + intro Hex.
      destruct Hex as [j Hex].
      destruct Hex as [Hj Hsat].
      intro Hnot_previous.
      destruct (Nat.eq_dec j n) as [-> | Hne].
      * exact Hsat.
      * exfalso.
        apply Hnot_previous.
        exists j; split; [lia | exact Hsat].
Qed.

Lemma monte_carlo_c_and_spec :
  forall (v : state) (gamma delta : CFormula),
    satisfies v (c_and gamma delta) <->
      satisfies v gamma /\ satisfies v delta.
Proof.
  intros v gamma delta.
  unfold c_and, c_not.
  cbn [satisfies].
  split.
  - intro H.
    split.
    + apply NNPP; intro Hnot.
      apply H; intros Hgamma.
      exfalso; apply Hnot; exact Hgamma.
    + apply NNPP; intro Hnot.
      apply H; intros _ Hdelta.
      apply Hnot; exact Hdelta.
  - intros [Hgamma Hdelta] Hbad.
    apply (Hbad Hgamma Hdelta).
Qed.

Lemma monte_carlo_nonnegative_real_floor :
  forall x : R,
    (0 <= x)%R ->
    exists n : nat, (INR n <= x < INR (S n))%R.
Proof.
  intros x Hx.
  pose proof (archimed x) as [Hup Hgap].
  assert (Hup_positive : (0 < up x)%Z).
  {
    apply lt_0_IZR.
    lra.
  }
  set (n := Z.to_nat (up x - 1)).
  assert (Hnonnegative : (0 <= up x - 1)%Z) by lia.
  assert (Hnat : Z.of_nat n = (up x - 1)%Z).
  {
    unfold n.
    apply Znat.Z2Nat.id; exact Hnonnegative.
  }
  exists n.
  rewrite !INR_IZR_INZ.
  rewrite Hnat.
  replace (Z.of_nat (S n)) with (Z.of_nat n + 1)%Z by lia.
  rewrite Hnat, plus_IZR, minus_IZR.
  cbn [IZR].
  lra.
Qed.

Lemma monte_carlo_region_bounded_shape :
  forall M k index : nat,
    (index < monte_carlo_region_count M)%nat ->
    let r := monte_carlo_region_remaining M index in
    let s := monte_carlo_region_slot M index in
    ((s <= r)%nat /\
       monte_carlo_region M k index = monte_carlo_exact_region M k r s) \/
    (s = S M /\
       monte_carlo_region M k index = monte_carlo_other_region M k r) \/
    monte_carlo_region M k index = FFalse.
Proof.
  intros M k index Hindex.
  pose proof (monte_carlo_region_bounded_decode M index Hindex)
    as [Hr Hs].
  cbn -[monte_carlo_region_remaining monte_carlo_region_slot].
  unfold monte_carlo_region.
  assert (HrM :
    (monte_carlo_region_remaining M index <=? M)%nat = true) by
    (apply Nat.leb_le; lia).
  rewrite HrM.
  destruct (Nat.leb
    (monte_carlo_region_slot M index)
    (monte_carlo_region_remaining M index)) eqn:Hslot_le.
  - left; split.
    + apply Nat.leb_le; exact Hslot_le.
    + reflexivity.
  - apply Nat.leb_gt in Hslot_le.
    destruct (Nat.eqb (monte_carlo_region_slot M index) (S M))
      eqn:Hslot_other.
    + right; left; split.
      * apply Nat.eqb_eq; exact Hslot_other.
      * reflexivity.
    + right; right; reflexivity.
Qed.

Lemma monte_carlo_time_band_in_guard :
  forall M r : nat,
    (1 <= r <= M)%nat ->
    cformula_valid
      <{ $(monte_carlo_time_band M r) -> $(monte_carlo_guard M) }>.
Proof.
  intros M r Hr v Hband.
  unfold monte_carlo_time_band, monte_carlo_guard in *.
  cbn [satisfies c_and c_not c_lt term_eval] in *.
  pose proof (le_INR 0 (M - r) (Nat.le_0_l _)) as Hzero.
  assert (Hlast : (M - r + 1 <= M)%nat) by lia.
  pose proof (le_INR (M - r + 1) M Hlast) as Hupper.
  cbn in Hzero.
  assert (Hband_lower :
    (INR (M - r) <= real_program_values v monte_carlo_i)%R).
  {
    apply NNPP; intro Hnot_lower.
    apply Hband; intros Hlower.
    exfalso; apply Hnot_lower; exact Hlower.
  }
  assert (Hband_upper :
    (real_program_values v monte_carlo_i < INR (M - r + 1))%R).
  {
    apply Rnot_le_lt; intro Hnot_upper.
    apply Hband; intros _ Hstrict.
    apply Hstrict; exact Hnot_upper.
  }
  assert (Hguard' :
    (0 <= real_program_values v monte_carlo_i < INR M)%R).
  { split; lra. }
  intros Hbad.
  apply (Hbad (proj1 Hguard')).
  exact (Rlt_not_le _ _ (proj2 Hguard')).
Qed.

Lemma monte_carlo_regions_in_guard :
  forall M k : nat,
    while_regions_in_guard (monte_carlo_region_count M)
      (monte_carlo_guard M) (monte_carlo_region M k).
Proof.
  intros M k index Hindex.
  pose proof (monte_carlo_region_bounded_decode M index Hindex)
    as [Hr Hs].
  pose proof (monte_carlo_region_bounded_shape M k index Hindex)
    as Hshape.
  destruct Hshape as [Hexact_case | Hrest].
  - destruct Hexact_case as [Hsr Hexact].
    rewrite Hexact.
    intros v Hregion.
    unfold monte_carlo_exact_region in Hregion.
    apply monte_carlo_c_and_spec in Hregion.
    eapply monte_carlo_time_band_in_guard;
      [exact Hr | exact (proj1 Hregion)].
  - destruct Hrest as [Hother_case | Hfalse].
    + destruct Hother_case as [Hsother Hother].
      rewrite Hother.
      intros v Hregion.
      unfold monte_carlo_other_region in Hregion.
      apply monte_carlo_c_and_spec in Hregion.
      eapply monte_carlo_time_band_in_guard;
        [exact Hr | exact (proj1 Hregion)].
    + rewrite Hfalse.
      intros v Hregion.
      cbn [satisfies] in Hregion; contradiction.
Qed.

Lemma monte_carlo_time_band_spec :
  forall (M r : nat) (v : state),
    satisfies v (monte_carlo_time_band M r) <->
      (INR (M - r) <= real_program_values v monte_carlo_i <
        INR (M - r + 1))%R.
Proof.
  intros M r v.
  unfold monte_carlo_time_band.
  rewrite monte_carlo_c_and_spec.
  cbn [satisfies c_lt c_not term_eval].
  split.
  - intros [Hlower Hupper].
    split; [exact Hlower | apply Rnot_le_lt; exact Hupper].
  - intros [Hlower Hupper].
    split; [exact Hlower | exact (Rlt_not_le _ _ Hupper)].
Qed.

Lemma monte_carlo_exact_region_spec :
  forall (M k r s : nat) (v : state),
    satisfies v (monte_carlo_exact_region M k r s) <->
      satisfies v (monte_carlo_time_band M r) /\
      real_program_values v monte_carlo_H = (INR k - INR s)%R.
Proof.
  intros M k r s v.
  unfold monte_carlo_exact_region.
  rewrite monte_carlo_c_and_spec.
  split.
  - intros [Hband Heq].
    apply monte_carlo_c_and_spec in Heq.
    cbn [satisfies term_eval] in Heq.
    split; [exact Hband | lra].
  - intros [Hband Heq].
    split; [exact Hband |].
    apply monte_carlo_c_and_spec.
    cbn [satisfies term_eval].
    split; lra.
Qed.

Lemma monte_carlo_regions_cover :
  forall M k : nat,
    while_regions_cover (monte_carlo_region_count M)
      (monte_carlo_guard M) (monte_carlo_region M k).
Proof.
  intros M k v Hguard.
  unfold monte_carlo_guard in Hguard.
  apply monte_carlo_c_and_spec in Hguard.
  destruct Hguard as [Hnonnegative Hless].
  cbn [satisfies c_lt c_not term_eval] in Hnonnegative, Hless.
  apply Rnot_le_lt in Hless.
  destruct (monte_carlo_nonnegative_real_floor
    (real_program_values v monte_carlo_i) Hnonnegative)
    as [n Hfloor].
  assert (HnM : (n < M)%nat).
  {
    apply INR_lt.
    lra.
  }
  set (r := (M - n)%nat).
  assert (Hr : (1 <= r <= M)%nat) by (unfold r; lia).
  assert (Hband : satisfies v (monte_carlo_time_band M r)).
  {
    apply monte_carlo_time_band_spec.
    unfold r.
    replace (M - (M - n) + 1)%nat with (S n) by lia.
    replace (M - (M - n))%nat with n by lia.
    exact Hfloor.
  }
  destruct (classic
    (exists s : nat,
      (s <= r)%nat /\
      real_program_values v monte_carlo_H = (INR k - INR s)%R))
    as [Hexact | Hother].
  - destruct Hexact as [s Hexact].
    destruct Hexact as [Hsr HH].
    set (index := monte_carlo_region_index M r s).
    assert (Hswidth : (s < monte_carlo_block_width M)%nat) by
      (unfold monte_carlo_block_width; lia).
    apply monte_carlo_finite_c_or_spec.
    exists index; split.
    + unfold index.
      apply monte_carlo_region_index_bound; assumption.
    + unfold index.
      rewrite monte_carlo_region_index_exact by assumption.
      apply monte_carlo_exact_region_spec.
      split; assumption.
  - set (index := monte_carlo_region_index M r (S M)).
    apply monte_carlo_finite_c_or_spec.
    exists index; split.
    + unfold index.
      apply monte_carlo_region_index_bound; [exact Hr |].
      unfold monte_carlo_block_width; lia.
    + unfold index.
      rewrite monte_carlo_region_index_other by exact Hr.
      unfold monte_carlo_other_region.
      apply monte_carlo_c_and_spec.
      split; [exact Hband |].
      unfold c_not.
      cbn [satisfies].
      intro Hsome.
      apply monte_carlo_finite_c_or_spec in Hsome.
      destruct Hsome as [s Hsome].
      destruct Hsome as [Hsr Hregion].
      apply monte_carlo_exact_region_spec in Hregion.
      apply Hother.
      exists s; split; [lia | exact (proj2 Hregion)].
Qed.

Lemma monte_carlo_region_reconstruct :
  forall M index : nat,
    index = monte_carlo_region_index M
      (monte_carlo_region_remaining M index)
      (monte_carlo_region_slot M index).
Proof.
  intros M index.
  unfold monte_carlo_region_index, monte_carlo_region_remaining,
    monte_carlo_region_slot.
  pose proof (Nat.div_mod index (monte_carlo_block_width M)) as Hdivmod.
  assert (Hw : monte_carlo_block_width M <> 0%nat) by
    (pose proof (monte_carlo_block_width_positive M); lia).
  specialize (Hdivmod Hw).
  replace (S (index / monte_carlo_block_width M) - 1)%nat with
    (index / monte_carlo_block_width M)%nat by lia.
  nia.
Qed.

Lemma monte_carlo_time_bands_disjoint :
  forall M r1 r2 : nat,
    (r1 <= M)%nat -> (r2 <= M)%nat -> r1 <> r2 ->
    cformula_valid
      <{ ~ ($(monte_carlo_time_band M r1) /\
             $(monte_carlo_time_band M r2)) }>.
Proof.
  intros M r1 r2 Hr1 Hr2 Hneq v Hboth.
  apply monte_carlo_c_and_spec in Hboth.
  destruct Hboth as [Hband1 Hband2].
  apply monte_carlo_time_band_spec in Hband1.
  apply monte_carlo_time_band_spec in Hband2.
  assert (Hstarts : (M - r1 <> M - r2)%nat) by lia.
  destruct (Nat.lt_ge_cases (M - r1) (M - r2)) as [Hlt | Hge].
  - assert (Hsep : (M - r1 + 1 <= M - r2)%nat) by lia.
    pose proof (le_INR _ _ Hsep); lra.
  - assert (Hsep : (M - r2 + 1 <= M - r1)%nat) by lia.
    pose proof (le_INR _ _ Hsep); lra.
Qed.

Lemma monte_carlo_exact_regions_same_band_disjoint :
  forall M k r s1 s2 : nat,
    s1 <> s2 ->
    cformula_valid
      <{ ~ ($(monte_carlo_exact_region M k r s1) /\
             $(monte_carlo_exact_region M k r s2)) }>.
Proof.
  intros M k r s1 s2 Hneq v Hboth.
  apply monte_carlo_c_and_spec in Hboth.
  destruct Hboth as [Hregion1 Hregion2].
  apply monte_carlo_exact_region_spec in Hregion1.
  apply monte_carlo_exact_region_spec in Hregion2.
  assert (HINR : INR s1 <> INR s2).
  {
    intro Heq.
    apply Hneq.
    apply INR_eq; exact Heq.
  }
  apply HINR; lra.
Qed.

Lemma monte_carlo_exact_other_disjoint :
  forall M k r s : nat,
    (s <= r)%nat ->
    cformula_valid
      <{ ~ ($(monte_carlo_exact_region M k r s) /\
             $(monte_carlo_other_region M k r)) }>.
Proof.
  intros M k r s Hsr v Hboth.
  apply monte_carlo_c_and_spec in Hboth.
  destruct Hboth as [Hexact Hother].
  unfold monte_carlo_other_region in Hother.
  apply monte_carlo_c_and_spec in Hother.
  destruct Hother as [_ Hnot].
  unfold c_not in Hnot.
  cbn [satisfies] in Hnot.
  apply Hnot.
  apply monte_carlo_finite_c_or_spec.
  exists s; split; [lia | exact Hexact].
Qed.

Lemma monte_carlo_regions_disjoint :
  forall M k : nat,
    while_regions_disjoint (monte_carlo_region_count M)
      (monte_carlo_region M k).
Proof.
  intros M k index1 index2 Hindex1 Hindex2.
  pose proof (monte_carlo_region_bounded_decode M index1 Hindex1)
    as [Hr1 Hs1].
  assert (Hindex2_bound :
    (index2 < monte_carlo_region_count M)%nat) by lia.
  pose proof (monte_carlo_region_bounded_decode M index2 Hindex2_bound)
    as [Hr2 Hs2].
  pose proof (monte_carlo_region_bounded_shape M k index1 Hindex1)
    as Hshape1.
  pose proof (monte_carlo_region_bounded_shape M k index2 Hindex2_bound)
    as Hshape2.
  destruct Hshape1 as [Hexact1 | Hrest1].
  - destruct Hexact1 as [Hslot1 Hregion1].
    destruct Hshape2 as [Hexact2 | Hrest2].
    + destruct Hexact2 as [Hslot2 Hregion2].
      rewrite Hregion1, Hregion2.
      destruct (Nat.eq_dec
        (monte_carlo_region_remaining M index1)
        (monte_carlo_region_remaining M index2)) as [Hr_eq | Hr_neq].
      * rewrite Hr_eq.
        apply monte_carlo_exact_regions_same_band_disjoint.
        intro Hslot_eq.
        pose proof (monte_carlo_region_reconstruct M index1) as Hrec1.
        pose proof (monte_carlo_region_reconstruct M index2) as Hrec2.
        rewrite Hr_eq in Hrec1.
        rewrite Hslot_eq in Hrec1.
        lia.
      * intros v Hboth.
        apply monte_carlo_c_and_spec in Hboth.
        destruct Hboth as [Hone Htwo].
        eapply (monte_carlo_time_bands_disjoint M
          (monte_carlo_region_remaining M index1)
          (monte_carlo_region_remaining M index2)
          (proj2 Hr1) (proj2 Hr2) Hr_neq v).
        apply monte_carlo_c_and_spec.
        split.
        -- apply monte_carlo_exact_region_spec in Hone; exact (proj1 Hone).
        -- apply monte_carlo_exact_region_spec in Htwo; exact (proj1 Htwo).
    + destruct Hrest2 as [Hother2 | Hfalse2].
      * destruct Hother2 as [Hslot2 Hregion2].
        rewrite Hregion1, Hregion2.
        destruct (Nat.eq_dec
          (monte_carlo_region_remaining M index1)
          (monte_carlo_region_remaining M index2)) as [Hr_eq | Hr_neq].
        -- rewrite Hr_eq.
           apply monte_carlo_exact_other_disjoint; lia.
        -- intros v Hboth.
           apply monte_carlo_c_and_spec in Hboth.
           destruct Hboth as [Hone Htwo].
           eapply (monte_carlo_time_bands_disjoint M
             (monte_carlo_region_remaining M index1)
             (monte_carlo_region_remaining M index2)
             (proj2 Hr1) (proj2 Hr2) Hr_neq v).
           apply monte_carlo_c_and_spec.
           split.
           ++ apply monte_carlo_exact_region_spec in Hone; exact (proj1 Hone).
           ++ unfold monte_carlo_other_region in Htwo.
              apply monte_carlo_c_and_spec in Htwo; exact (proj1 Htwo).
      * rewrite Hfalse2.
        intros v Hboth.
        apply monte_carlo_c_and_spec in Hboth.
        cbn [satisfies] in Hboth; tauto.
  - destruct Hrest1 as [Hother1 | Hfalse1].
    + destruct Hother1 as [Hslot1 Hregion1].
      destruct Hshape2 as [Hexact2 | Hrest2].
      * destruct Hexact2 as [Hslot2 Hregion2].
        rewrite Hregion1, Hregion2.
        destruct (Nat.eq_dec
          (monte_carlo_region_remaining M index1)
          (monte_carlo_region_remaining M index2)) as [Hr_eq | Hr_neq].
        -- rewrite Hr_eq.
           intros v Hboth.
           apply monte_carlo_c_and_spec in Hboth.
           eapply monte_carlo_exact_other_disjoint;
             [exact Hslot2 |].
           apply monte_carlo_c_and_spec.
           split; [exact (proj2 Hboth) | exact (proj1 Hboth)].
        -- intros v Hboth.
           apply monte_carlo_c_and_spec in Hboth.
           destruct Hboth as [Hone Htwo].
           eapply (monte_carlo_time_bands_disjoint M
             (monte_carlo_region_remaining M index1)
             (monte_carlo_region_remaining M index2)
             (proj2 Hr1) (proj2 Hr2) Hr_neq v).
           apply monte_carlo_c_and_spec.
           split.
           ++ unfold monte_carlo_other_region in Hone.
              apply monte_carlo_c_and_spec in Hone; exact (proj1 Hone).
           ++ apply monte_carlo_exact_region_spec in Htwo; exact (proj1 Htwo).
      * destruct Hrest2 as [Hother2 | Hfalse2].
        -- destruct Hother2 as [Hslot2 Hregion2].
           rewrite Hregion1, Hregion2.
           assert (Hr_neq :
             monte_carlo_region_remaining M index1 <>
             monte_carlo_region_remaining M index2).
           {
             intro Hr_eq.
             pose proof (monte_carlo_region_reconstruct M index1) as Hrec1.
             pose proof (monte_carlo_region_reconstruct M index2) as Hrec2.
             rewrite Hr_eq in Hrec1.
             rewrite Hslot1 in Hrec1.
             rewrite Hslot2 in Hrec2.
             lia.
           }
           intros v Hboth.
           apply monte_carlo_c_and_spec in Hboth.
           destruct Hboth as [Hone Htwo].
           eapply (monte_carlo_time_bands_disjoint M
             (monte_carlo_region_remaining M index1)
             (monte_carlo_region_remaining M index2)
             (proj2 Hr1) (proj2 Hr2) Hr_neq v).
           apply monte_carlo_c_and_spec.
           unfold monte_carlo_other_region in Hone, Htwo.
           apply monte_carlo_c_and_spec in Hone.
           apply monte_carlo_c_and_spec in Htwo.
           split; [exact (proj1 Hone) | exact (proj1 Htwo)].
        -- rewrite Hfalse2.
           intros v Hboth.
           apply monte_carlo_c_and_spec in Hboth.
           cbn [satisfies] in Hboth; tauto.
    + rewrite Hfalse1.
      intros v Hboth.
      apply monte_carlo_c_and_spec in Hboth.
      cbn [satisfies] in Hboth; tauto.
Qed.

(** Transition matrices and fixed-point candidates. *)
Definition monte_carlo_row_active (M index : nat) : bool :=
  let r := monte_carlo_region_remaining M index in
  let s := monte_carlo_region_slot M index in
  orb (s <=? r)%nat (s =? S M)%nat.

Definition monte_carlo_hit_destination_slot (M index : nat) : nat :=
  let s := monte_carlo_region_slot M index in
  if (s =? S M)%nat then S M
  else match s with O => S M | S s' => s' end.

Definition monte_carlo_miss_destination_slot (M index : nat) : nat :=
  let r := monte_carlo_region_remaining M index in
  let s := monte_carlo_region_slot M index in
  if (s =? S M)%nat then S M
  else if (s =? r)%nat then S M else s.

Definition monte_carlo_hit_destination (M index : nat) : nat :=
  monte_carlo_region_index M
    (monte_carlo_region_remaining M index - 1)
    (monte_carlo_hit_destination_slot M index).

Definition monte_carlo_miss_destination (M index : nat) : nat :=
  monte_carlo_region_index M
    (monte_carlo_region_remaining M index - 1)
    (monte_carlo_miss_destination_slot M index).

Definition monte_carlo_transitions
  (M : nat) (index destination : nat) : R :=
  if andb (monte_carlo_row_active M index)
       (1 <? monte_carlo_region_remaining M index)%nat then
    ((if (destination =? monte_carlo_hit_destination M index)%nat
       then monte_carlo_hit_probability else 0) +
     (if (destination =? monte_carlo_miss_destination M index)%nat
       then (1 - monte_carlo_hit_probability)%R else 0))%R
  else 0%R.

Definition monte_carlo_termination_exits (M index : nat) : R :=
  if monte_carlo_row_active M index then
    if (monte_carlo_region_remaining M index =? 1)%nat
    then 1%R else 0%R
  else 1%R.

Definition monte_carlo_complement_exits (M index : nat) : R :=
  if monte_carlo_row_active M index then
    if (monte_carlo_region_remaining M index =? 1)%nat then
      if (monte_carlo_region_slot M index =? S M)%nat then 1%R
      else if (monte_carlo_region_slot M index =? 0)%nat
           then monte_carlo_hit_probability
           else (1 - monte_carlo_hit_probability)%R
    else 0%R
  else 1%R.

Definition monte_carlo_termination_solution (_ : nat) : R := 1%R.

Definition monte_carlo_complement_solution (M index : nat) : R :=
  let r := monte_carlo_region_remaining M index in
  let s := monte_carlo_region_slot M index in
  if (s <=? r)%nat
  then (1 - monte_carlo_bernoulli_mass r s)%R
  else 1%R.

Lemma monte_carlo_row_active_spec :
  forall M index : nat,
    monte_carlo_row_active M index = true <->
      (monte_carlo_region_slot M index <=
        monte_carlo_region_remaining M index)%nat \/
      monte_carlo_region_slot M index = S M.
Proof.
  intros M index.
  unfold monte_carlo_row_active.
  rewrite Bool.orb_true_iff, Nat.leb_le, Nat.eqb_eq.
  tauto.
Qed.

Lemma monte_carlo_row_inactive_spec :
  forall M index : nat,
    monte_carlo_row_active M index = false <->
      (monte_carlo_region_remaining M index <
        monte_carlo_region_slot M index)%nat /\
      monte_carlo_region_slot M index <> S M.
Proof.
  intros M index.
  unfold monte_carlo_row_active.
  rewrite Bool.orb_false_iff, Nat.leb_gt, Nat.eqb_neq.
  tauto.
Qed.

Lemma monte_carlo_destination_slots_bounded :
  forall M index : nat,
    (index < monte_carlo_region_count M)%nat ->
    monte_carlo_row_active M index = true ->
    (monte_carlo_hit_destination_slot M index <
       monte_carlo_block_width M)%nat /\
    (monte_carlo_miss_destination_slot M index <
       monte_carlo_block_width M)%nat.
Proof.
  intros M index Hindex Hactive.
  pose proof (monte_carlo_region_bounded_decode M index Hindex)
    as [Hr Hs].
  apply monte_carlo_row_active_spec in Hactive.
  unfold monte_carlo_hit_destination_slot,
    monte_carlo_miss_destination_slot.
  destruct (Nat.eqb (monte_carlo_region_slot M index) (S M))
    eqn:Hother.
  - split; unfold monte_carlo_block_width; lia.
  - apply Nat.eqb_neq in Hother.
    destruct Hactive as [Hsr | Hother_eq]; [|contradiction].
    split.
    + destruct (monte_carlo_region_slot M index); cbn;
        unfold monte_carlo_block_width in *; lia.
    + destruct (monte_carlo_region_slot M index =?
        monte_carlo_region_remaining M index)%nat;
        unfold monte_carlo_block_width in *; lia.
Qed.

Lemma monte_carlo_destinations_bound :
  forall M index : nat,
    (index < monte_carlo_region_count M)%nat ->
    monte_carlo_row_active M index = true ->
    (1 < monte_carlo_region_remaining M index)%nat ->
    (monte_carlo_hit_destination M index <
       monte_carlo_region_count M)%nat /\
    (monte_carlo_miss_destination M index <
       monte_carlo_region_count M)%nat.
Proof.
  intros M index Hindex Hactive Hrmore.
  pose proof (monte_carlo_region_bounded_decode M index Hindex)
    as [Hr Hs].
  pose proof (monte_carlo_destination_slots_bounded M index Hindex Hactive)
    as [Hhit Hmiss].
  split;
    [unfold monte_carlo_hit_destination |
     unfold monte_carlo_miss_destination];
    apply monte_carlo_region_index_bound; lia.
Qed.

Lemma monte_carlo_destinations_earlier :
  forall M index : nat,
    (index < monte_carlo_region_count M)%nat ->
    monte_carlo_row_active M index = true ->
    (1 < monte_carlo_region_remaining M index)%nat ->
    (monte_carlo_hit_destination M index < index)%nat /\
    (monte_carlo_miss_destination M index < index)%nat.
Proof.
  intros M index Hindex Hactive Hrmore.
  pose proof (monte_carlo_region_bounded_decode M index Hindex)
    as [Hr Hs].
  pose proof (monte_carlo_destination_slots_bounded M index Hindex Hactive)
    as [Hhit Hmiss].
  pose proof (monte_carlo_region_reconstruct M index) as Hreconstruct.
  unfold monte_carlo_hit_destination, monte_carlo_miss_destination,
    monte_carlo_region_index in *.
  unfold monte_carlo_block_width in *.
  split; nia.
Qed.

Lemma monte_carlo_progress :
  forall M : nat,
    while_progress (monte_carlo_region_count M)
      (monte_carlo_transitions M) (monte_carlo_termination_exits M).
Proof.
  intros M index Hindex.
  destruct (monte_carlo_row_active M index) eqn:Hactive.
  - destruct (Nat.eq_dec
      (monte_carlo_region_remaining M index) 1%nat) as [Hr_one | Hr_not_one].
    + left.
      unfold monte_carlo_termination_exits.
      rewrite Hactive.
      assert (Hreq :
        (monte_carlo_region_remaining M index =? 1)%nat = true) by
        (apply Nat.eqb_eq; exact Hr_one).
      rewrite Hreq.
      lra.
    + right.
      assert (Hrmore : (1 < monte_carlo_region_remaining M index)%nat).
      {
        pose proof (monte_carlo_region_bounded_decode M index Hindex)
          as [Hr Hs]; lia.
      }
      exists (monte_carlo_hit_destination M index).
      split.
      * apply (proj1
          (monte_carlo_destinations_earlier M index Hindex Hactive Hrmore)).
      * assert (Hlt :
          (1 <? monte_carlo_region_remaining M index)%nat = true) by
          (apply Nat.ltb_lt; exact Hrmore).
        unfold monte_carlo_transitions.
        rewrite Hactive, Hlt; cbn [andb].
        rewrite Nat.eqb_refl.
        destruct (monte_carlo_hit_destination M index =?
          monte_carlo_miss_destination M index)%nat eqn:Hsame;
          cbn;
          pose proof monte_carlo_hit_probability_bounds; lra.
  - left.
    unfold monte_carlo_termination_exits.
    rewrite Hactive.
    lra.
Qed.

Lemma monte_carlo_complement_progress :
  forall M : nat,
    while_progress (monte_carlo_region_count M)
      (monte_carlo_transitions M) (monte_carlo_complement_exits M).
Proof.
  intros M index Hindex.
  destruct (monte_carlo_row_active M index) eqn:Hactive.
  - destruct (Nat.eq_dec
      (monte_carlo_region_remaining M index) 1%nat) as [Hr_one | Hr_not_one].
    + left.
      unfold monte_carlo_complement_exits.
      rewrite Hactive.
      assert (Hreq :
        (monte_carlo_region_remaining M index =? 1)%nat = true) by
        (apply Nat.eqb_eq; exact Hr_one).
      rewrite Hreq.
      destruct (monte_carlo_region_slot M index =? S M)%nat eqn:Hother;
        [lra |].
      destruct (monte_carlo_region_slot M index =? 0)%nat;
        pose proof monte_carlo_hit_probability_bounds; lra.
    + right.
      assert (Hrmore : (1 < monte_carlo_region_remaining M index)%nat).
      {
        pose proof (monte_carlo_region_bounded_decode M index Hindex)
          as [Hr Hs]; lia.
      }
      exists (monte_carlo_hit_destination M index).
      split.
      * apply (proj1
          (monte_carlo_destinations_earlier M index Hindex Hactive Hrmore)).
      * assert (Hlt :
          (1 <? monte_carlo_region_remaining M index)%nat = true) by
          (apply Nat.ltb_lt; exact Hrmore).
        unfold monte_carlo_transitions.
        rewrite Hactive, Hlt; cbn [andb].
        rewrite Nat.eqb_refl.
        destruct (monte_carlo_hit_destination M index =?
          monte_carlo_miss_destination M index)%nat eqn:Hsame;
          cbn;
          pose proof monte_carlo_hit_probability_bounds; lra.
  - left.
    unfold monte_carlo_complement_exits.
    rewrite Hactive.
    lra.
Qed.

Lemma monte_carlo_finite_r_sum_zero :
  forall (m : nat) (terms : nat -> R),
    (forall j : nat, (j < m)%nat -> terms j = 0%R) ->
    finite_r_sum m terms = 0%R.
Proof.
  induction m as [|m IH]; intros terms Hterms.
  - reflexivity.
  - cbn [finite_r_sum].
    rewrite IH.
    + rewrite Hterms by lia; ring.
    + intros j Hj; apply Hterms; lia.
Qed.

Lemma monte_carlo_finite_r_sum_add :
  forall (m : nat) (left right : nat -> R),
    finite_r_sum m (fun j => (left j + right j)%R) =
      (finite_r_sum m left + finite_r_sum m right)%R.
Proof.
  induction m as [|m IH]; intros left right.
  - cbn [finite_r_sum]; ring.
  - cbn [finite_r_sum].
    rewrite IH; ring.
Qed.

Lemma monte_carlo_finite_r_sum_delta :
  forall (m target : nat) (coefficient : R) (solution : nat -> R),
    (target < m)%nat ->
    finite_r_sum m
      (fun j =>
        (if (j =? target)%nat then coefficient else 0%R) * solution j)%R =
      (coefficient * solution target)%R.
Proof.
  induction m as [|m IH]; intros target coefficient solution Htarget.
  - lia.
  - cbn [finite_r_sum].
    destruct (Nat.eq_dec target m) as [-> | Hneq].
    + rewrite Nat.eqb_refl.
      rewrite monte_carlo_finite_r_sum_zero.
      * ring.
      * intros j Hj.
        assert ((j =? m)%nat = false) by (apply Nat.eqb_neq; lia).
        rewrite H; ring.
    + rewrite IH by lia.
      assert ((m =? target)%nat = false) by
        (apply Nat.eqb_neq; lia).
      rewrite H; ring.
Qed.

Lemma monte_carlo_transition_sum_eval :
  forall (M index : nat) (solution : nat -> R),
    (index < monte_carlo_region_count M)%nat ->
    monte_carlo_row_active M index = true ->
    (1 < monte_carlo_region_remaining M index)%nat ->
    finite_r_sum (monte_carlo_region_count M)
      (fun destination =>
        monte_carlo_transitions M index destination * solution destination)%R =
      (monte_carlo_hit_probability *
         solution (monte_carlo_hit_destination M index) +
       (1 - monte_carlo_hit_probability) *
         solution (monte_carlo_miss_destination M index))%R.
Proof.
  intros M index solution Hindex Hactive Hrmore.
  pose proof (monte_carlo_destinations_bound M index Hindex Hactive Hrmore)
    as [Hhit_bound Hmiss_bound].
  assert (Hlt :
    (1 <? monte_carlo_region_remaining M index)%nat = true) by
    (apply Nat.ltb_lt; exact Hrmore).
  transitivity
    (finite_r_sum (monte_carlo_region_count M)
      (fun destination =>
        ((if (destination =? monte_carlo_hit_destination M index)%nat
          then monte_carlo_hit_probability else 0%R) * solution destination +
         (if (destination =? monte_carlo_miss_destination M index)%nat
          then (1 - monte_carlo_hit_probability)%R else 0%R) *
            solution destination)%R)).
  - apply f_equal.
    apply functional_extensionality; intro destination.
    unfold monte_carlo_transitions.
    rewrite Hactive, Hlt; cbn [andb].
    ring.
  - rewrite monte_carlo_finite_r_sum_add.
    rewrite monte_carlo_finite_r_sum_delta by exact Hhit_bound.
    rewrite monte_carlo_finite_r_sum_delta by exact Hmiss_bound.
    reflexivity.
Qed.

Lemma monte_carlo_transition_sum_zero :
  forall (M index : nat) (solution : nat -> R),
    (monte_carlo_row_active M index = false \/
      (monte_carlo_region_remaining M index <= 1)%nat) ->
    finite_r_sum (monte_carlo_region_count M)
      (fun destination =>
        monte_carlo_transitions M index destination * solution destination)%R =
      0%R.
Proof.
  intros M index solution Hzero.
  apply monte_carlo_finite_r_sum_zero.
  intros destination Hdestination.
  unfold monte_carlo_transitions.
  destruct Hzero as [Hactive | Hr].
  - rewrite Hactive; cbn [andb]; ring.
  - assert (Hlt :
      (1 <? monte_carlo_region_remaining M index)%nat = false) by
      (apply Nat.ltb_ge; exact Hr).
    rewrite Hlt.
    destruct (monte_carlo_row_active M index); cbn [andb]; ring.
Qed.

Lemma monte_carlo_termination_solution_correct :
  forall M : nat,
    while_solution (monte_carlo_region_count M)
      monte_carlo_termination_solution
      (monte_carlo_transitions M) (monte_carlo_termination_exits M).
Proof.
  intros M index Hindex.
  unfold monte_carlo_termination_solution.
  split; [|lra].
  destruct (monte_carlo_row_active M index) eqn:Hactive.
  - destruct (Nat.le_gt_cases
      (monte_carlo_region_remaining M index) 1%nat) as [Hrsmall | Hrmore].
    + rewrite monte_carlo_transition_sum_zero by (right; exact Hrsmall).
      unfold monte_carlo_termination_exits.
      rewrite Hactive.
      assert (Hrpositive :
        (1 <= monte_carlo_region_remaining M index)%nat) by
        (pose proof (monte_carlo_region_bounded_decode M index Hindex);
         lia).
      assert (Hreq :
        (monte_carlo_region_remaining M index =? 1)%nat = true) by
        (apply Nat.eqb_eq; lia).
      rewrite Hreq; lra.
    + rewrite monte_carlo_transition_sum_eval
        by (try exact Hindex; try exact Hactive; lia).
      unfold monte_carlo_termination_exits.
      rewrite Hactive.
      assert (Hreq :
        (monte_carlo_region_remaining M index =? 1)%nat = false) by
        (apply Nat.eqb_neq; lia).
      rewrite Hreq.
      pose proof monte_carlo_hit_probability_bounds.
      lra.
  - rewrite monte_carlo_transition_sum_zero by (left; exact Hactive).
    unfold monte_carlo_termination_exits.
    rewrite Hactive; lra.
Qed.

Lemma monte_carlo_hit_destination_decode :
  forall M index : nat,
    (index < monte_carlo_region_count M)%nat ->
    monte_carlo_row_active M index = true ->
    (1 < monte_carlo_region_remaining M index)%nat ->
    monte_carlo_region_remaining M (monte_carlo_hit_destination M index) =
      (monte_carlo_region_remaining M index - 1)%nat /\
    monte_carlo_region_slot M (monte_carlo_hit_destination M index) =
      monte_carlo_hit_destination_slot M index.
Proof.
  intros M index Hindex Hactive Hrmore.
  pose proof (monte_carlo_region_bounded_decode M index Hindex)
    as [Hr Hs].
  pose proof (monte_carlo_destination_slots_bounded M index Hindex Hactive)
    as [Hhit Hmiss].
  unfold monte_carlo_hit_destination.
  apply monte_carlo_region_decode_index; lia.
Qed.

Lemma monte_carlo_miss_destination_decode :
  forall M index : nat,
    (index < monte_carlo_region_count M)%nat ->
    monte_carlo_row_active M index = true ->
    (1 < monte_carlo_region_remaining M index)%nat ->
    monte_carlo_region_remaining M (monte_carlo_miss_destination M index) =
      (monte_carlo_region_remaining M index - 1)%nat /\
    monte_carlo_region_slot M (monte_carlo_miss_destination M index) =
      monte_carlo_miss_destination_slot M index.
Proof.
  intros M index Hindex Hactive Hrmore.
  pose proof (monte_carlo_region_bounded_decode M index Hindex)
    as [Hr Hs].
  pose proof (monte_carlo_destination_slots_bounded M index Hindex Hactive)
    as [Hhit Hmiss].
  unfold monte_carlo_miss_destination.
  apply monte_carlo_region_decode_index; lia.
Qed.

Lemma monte_carlo_complement_solution_hit_exact :
  forall M index : nat,
    (index < monte_carlo_region_count M)%nat ->
    monte_carlo_row_active M index = true ->
    (1 < monte_carlo_region_remaining M index)%nat ->
    (monte_carlo_region_slot M index <=
      monte_carlo_region_remaining M index)%nat ->
    monte_carlo_complement_solution M
      (monte_carlo_hit_destination M index) =
    match monte_carlo_region_slot M index with
    | O => 1%R
    | S s =>
        (1 - monte_carlo_bernoulli_mass
          (monte_carlo_region_remaining M index - 1) s)%R
    end.
Proof.
  intros M index Hindex Hactive Hrmore Hsr.
  pose proof (monte_carlo_region_bounded_decode M index Hindex)
    as [Hr Hs].
  pose proof (monte_carlo_hit_destination_decode
    M index Hindex Hactive Hrmore) as [Hremain Hslot].
  unfold monte_carlo_complement_solution.
  rewrite Hremain, Hslot.
  unfold monte_carlo_hit_destination_slot.
  assert (Hnot_other :
    (monte_carlo_region_slot M index =? S M)%nat = false).
  {
    apply Nat.eqb_neq.
    unfold monte_carlo_block_width in Hs.
    lia.
  }
  rewrite Hnot_other.
  destruct (monte_carlo_region_slot M index) as [|s].
  - assert (Hcatch :
      (S M <=? monte_carlo_region_remaining M index - 1)%nat = false) by
      (apply Nat.leb_gt; lia).
    rewrite Hcatch; reflexivity.
  - assert (Hexact :
      (s <=? monte_carlo_region_remaining M index - 1)%nat = true) by
      (apply Nat.leb_le; lia).
    rewrite Hexact; reflexivity.
Qed.

Lemma monte_carlo_complement_solution_miss_exact :
  forall M index : nat,
    (index < monte_carlo_region_count M)%nat ->
    monte_carlo_row_active M index = true ->
    (1 < monte_carlo_region_remaining M index)%nat ->
    (monte_carlo_region_slot M index <=
      monte_carlo_region_remaining M index)%nat ->
    monte_carlo_complement_solution M
      (monte_carlo_miss_destination M index) =
    if (monte_carlo_region_slot M index =?
        monte_carlo_region_remaining M index)%nat
    then 1%R
    else (1 - monte_carlo_bernoulli_mass
      (monte_carlo_region_remaining M index - 1)
      (monte_carlo_region_slot M index))%R.
Proof.
  intros M index Hindex Hactive Hrmore Hsr.
  pose proof (monte_carlo_region_bounded_decode M index Hindex)
    as [Hr Hs].
  pose proof (monte_carlo_miss_destination_decode
    M index Hindex Hactive Hrmore) as [Hremain Hslot].
  unfold monte_carlo_complement_solution.
  rewrite Hremain, Hslot.
  unfold monte_carlo_miss_destination_slot.
  assert (Hnot_other :
    (monte_carlo_region_slot M index =? S M)%nat = false).
  {
    apply Nat.eqb_neq.
    unfold monte_carlo_block_width in Hs.
    lia.
  }
  rewrite Hnot_other.
  destruct (monte_carlo_region_slot M index =?
    monte_carlo_region_remaining M index)%nat eqn:Hsame.
  - assert (Hcatch :
      (S M <=? monte_carlo_region_remaining M index - 1)%nat = false) by
      (apply Nat.leb_gt; lia).
    rewrite Hcatch; reflexivity.
  - apply Nat.eqb_neq in Hsame.
    assert (Hexact :
      (monte_carlo_region_slot M index <=?
        monte_carlo_region_remaining M index - 1)%nat = true) by
      (apply Nat.leb_le; lia).
    rewrite Hexact; reflexivity.
Qed.

Lemma monte_carlo_complement_solution_other_destinations :
  forall M index : nat,
    (index < monte_carlo_region_count M)%nat ->
    monte_carlo_row_active M index = true ->
    (1 < monte_carlo_region_remaining M index)%nat ->
    monte_carlo_region_slot M index = S M ->
    monte_carlo_complement_solution M
      (monte_carlo_hit_destination M index) = 1%R /\
    monte_carlo_complement_solution M
      (monte_carlo_miss_destination M index) = 1%R.
Proof.
  intros M index Hindex Hactive Hrmore Hother.
  pose proof (monte_carlo_hit_destination_decode
    M index Hindex Hactive Hrmore) as [Hhit_remain Hhit_slot].
  pose proof (monte_carlo_miss_destination_decode
    M index Hindex Hactive Hrmore) as [Hmiss_remain Hmiss_slot].
  assert (Hhit_definition :
    monte_carlo_hit_destination_slot M index = S M).
  {
    unfold monte_carlo_hit_destination_slot.
    rewrite Hother, Nat.eqb_refl; reflexivity.
  }
  assert (Hmiss_definition :
    monte_carlo_miss_destination_slot M index = S M).
  {
    unfold monte_carlo_miss_destination_slot.
    rewrite Hother, Nat.eqb_refl; reflexivity.
  }
  split; unfold monte_carlo_complement_solution.
  - rewrite Hhit_remain, Hhit_slot, Hhit_definition.
    assert (Hfalse :
      (S M <=? monte_carlo_region_remaining M index - 1)%nat = false) by
      (apply Nat.leb_gt;
       pose proof (monte_carlo_region_bounded_decode M index Hindex);
       lia).
    rewrite Hfalse; reflexivity.
  - rewrite Hmiss_remain, Hmiss_slot, Hmiss_definition.
    assert (Hfalse :
      (S M <=? monte_carlo_region_remaining M index - 1)%nat = false) by
      (apply Nat.leb_gt;
       pose proof (monte_carlo_region_bounded_decode M index Hindex);
       lia).
    rewrite Hfalse; reflexivity.
Qed.

Lemma monte_carlo_complement_solution_correct :
  forall M : nat,
    while_solution (monte_carlo_region_count M)
      (monte_carlo_complement_solution M)
      (monte_carlo_transitions M) (monte_carlo_complement_exits M).
Proof.
  intros M index Hindex.
  split.
  - destruct (monte_carlo_row_active M index) eqn:Hactive.
    + apply monte_carlo_row_active_spec in Hactive as Hactive_spec.
      destruct (Nat.le_gt_cases
        (monte_carlo_region_remaining M index) 1%nat)
        as [Hrsmall | Hrmore].
      * pose proof (monte_carlo_region_bounded_decode M index Hindex)
          as [Hr Hs].
        assert (Hr_one : monte_carlo_region_remaining M index = 1%nat)
          by lia.
        rewrite monte_carlo_transition_sum_zero by (right; exact Hrsmall).
        unfold monte_carlo_complement_exits.
        assert (Hactive_eq : monte_carlo_row_active M index = true).
        { apply (proj2 (monte_carlo_row_active_spec M index));
          exact Hactive_spec. }
        rewrite Hactive_eq.
        assert (Hreq :
          (monte_carlo_region_remaining M index =? 1)%nat = true) by
          (apply Nat.eqb_eq; exact Hr_one).
        rewrite Hreq.
        destruct Hactive_spec as [Hsr | Hother].
        -- unfold monte_carlo_complement_solution.
           assert (Hslot_le :
             (monte_carlo_region_slot M index <=?
               monte_carlo_region_remaining M index)%nat = true) by
             (apply Nat.leb_le; exact Hsr).
           rewrite Hslot_le.
           rewrite Hr_one.
           assert (Hnot_other :
             (monte_carlo_region_slot M index =? S M)%nat = false).
           {
             apply Nat.eqb_neq.
             unfold monte_carlo_block_width in Hs.
             lia.
           }
           rewrite Hnot_other.
           destruct (monte_carlo_region_slot M index) as [|s].
           ++ cbn [monte_carlo_bernoulli_mass].
              rewrite Nat.eqb_refl; ring.
           ++ assert (s = 0)%nat by lia; subst s.
              assert (Hone_not_zero : (1 =? 0)%nat = false) by
                (apply Nat.eqb_neq; lia).
              rewrite Hone_not_zero.
              cbn [monte_carlo_bernoulli_mass].
              ring.
        -- unfold monte_carlo_complement_solution.
           assert (Hslot_not_le :
             (monte_carlo_region_slot M index <=?
               monte_carlo_region_remaining M index)%nat = false) by
             (apply Nat.leb_gt; unfold monte_carlo_block_width in Hs; lia).
           rewrite Hslot_not_le.
           rewrite Hother, Nat.eqb_refl; lra.
      * assert (Hactive_eq : monte_carlo_row_active M index = true).
        { apply (proj2 (monte_carlo_row_active_spec M index));
          exact Hactive_spec. }
        rewrite monte_carlo_transition_sum_eval
          by (exact Hindex || exact Hactive_eq || exact Hrmore).
        unfold monte_carlo_complement_exits.
        rewrite Hactive_eq.
        assert (Hreq :
          (monte_carlo_region_remaining M index =? 1)%nat = false) by
          (apply Nat.eqb_neq; lia).
        rewrite Hreq.
        destruct Hactive_spec as [Hsr | Hother].
        -- unfold monte_carlo_complement_solution at 1.
           assert (Hslot_le :
             (monte_carlo_region_slot M index <=?
               monte_carlo_region_remaining M index)%nat = true) by
             (apply Nat.leb_le; exact Hsr).
           rewrite Hslot_le.
           rewrite (monte_carlo_complement_solution_hit_exact
             M index Hindex Hactive_eq Hrmore Hsr).
           rewrite (monte_carlo_complement_solution_miss_exact
             M index Hindex Hactive_eq Hrmore Hsr).
           destruct (monte_carlo_region_slot M index) as [|s] eqn:Hslot.
           ++ assert (Hsame :
                (0 =? monte_carlo_region_remaining M index)%nat = false) by
                (apply Nat.eqb_neq; lia).
              rewrite Hsame.
              replace (monte_carlo_region_remaining M index) with
                (S (monte_carlo_region_remaining M index - 1)) at 1 by lia.
              cbn [monte_carlo_bernoulli_mass].
              ring.
           ++ destruct (Nat.eq_dec (S s)
                (monte_carlo_region_remaining M index))
                as [Hsame | Hdifferent].
              ** assert (Hsameb :
                   (S s =? monte_carlo_region_remaining M index)%nat = true)
                   by (apply Nat.eqb_eq; exact Hsame).
                 rewrite Hsameb.
                 assert (Houtside :
                   monte_carlo_bernoulli_mass
                     (monte_carlo_region_remaining M index - 1) (S s) =
                     0%R).
                 { apply monte_carlo_bernoulli_mass_outside; lia. }
                 replace (monte_carlo_region_remaining M index) with
                   (S (monte_carlo_region_remaining M index - 1)) at 1 by lia.
                 cbn [monte_carlo_bernoulli_mass].
                 rewrite Houtside.
                 ring.
              ** assert (Hsameb :
                   (S s =? monte_carlo_region_remaining M index)%nat = false)
                   by (apply Nat.eqb_neq; exact Hdifferent).
                 rewrite Hsameb.
                 replace (monte_carlo_region_remaining M index) with
                   (S (monte_carlo_region_remaining M index - 1)) at 1 by lia.
                 cbn [monte_carlo_bernoulli_mass].
                 ring.
        -- unfold monte_carlo_complement_solution at 1.
           assert (Hslot_not_le :
             (monte_carlo_region_slot M index <=?
               monte_carlo_region_remaining M index)%nat = false).
           {
             apply Nat.leb_gt.
             pose proof (monte_carlo_region_bounded_decode M index Hindex)
               as [Hr Hs].
             unfold monte_carlo_block_width in Hs.
             lia.
           }
           rewrite Hslot_not_le.
           pose proof (monte_carlo_complement_solution_other_destinations
             M index Hindex Hactive_eq Hrmore Hother) as [Hhit Hmiss].
           rewrite Hhit, Hmiss.
           pose proof monte_carlo_hit_probability_bounds; lra.
    + apply monte_carlo_row_inactive_spec in Hactive as [Hsr Hnot_other].
      unfold monte_carlo_complement_solution.
      assert (Hslot_not_le :
        (monte_carlo_region_slot M index <=?
          monte_carlo_region_remaining M index)%nat = false) by
        (apply Nat.leb_gt; exact Hsr).
      rewrite Hslot_not_le.
      rewrite monte_carlo_transition_sum_zero by
        (left; apply (proj2 (monte_carlo_row_inactive_spec M index));
         split; assumption).
      unfold monte_carlo_complement_exits.
      assert (Hactive_eq : monte_carlo_row_active M index = false).
      { apply (proj2 (monte_carlo_row_inactive_spec M index));
        split; assumption. }
      rewrite Hactive_eq; lra.
  - unfold monte_carlo_complement_solution.
    destruct (monte_carlo_region_slot M index <=?
      monte_carlo_region_remaining M index)%nat eqn:Hslot.
    + pose proof (monte_carlo_bernoulli_mass_bounds
        (monte_carlo_region_remaining M index)
        (monte_carlo_region_slot M index)).
      lra.
    + lra.
Qed.

(** Analytical support for body weakest preconditions. *)
Definition monte_carlo_sample_invariant (gamma : CFormula) : Prop :=
  forall (v : state) (x y : R),
    satisfies
      (update_real (update_real v monte_carlo_X x) monte_carlo_Y y)
      gamma <-> satisfies v gamma.

Lemma monte_carlo_variables_distinct :
  monte_carlo_X <> monte_carlo_Y /\
  monte_carlo_X <> monte_carlo_i /\
  monte_carlo_X <> monte_carlo_H /\
  monte_carlo_Y <> monte_carlo_i /\
  monte_carlo_Y <> monte_carlo_H /\
  monte_carlo_i <> monte_carlo_H.
Proof.
  unfold monte_carlo_X, monte_carlo_Y, monte_carlo_i, monte_carlo_H.
  repeat split; congruence.
Qed.

Lemma monte_carlo_update_real_commute :
  forall (v : state) (x y : RealProgramVar) (a b : R),
    x <> y ->
    update_real (update_real v x a) y b =
      update_real (update_real v y b) x a.
Proof.
  intros [rp bp rl bl] x y a b Hxy.
  assert (Hvalues :
    update_real_values (update_real_values rp x a) y b =
      update_real_values (update_real_values rp y b) x a).
  {
    unfold update_real_values.
    apply functional_extensionality; intro z.
    destruct (real_program_var_eq_dec z y) as [-> | Hzy].
    - destruct (real_program_var_eq_dec y x) as [Hyx | Hyx].
      + exfalso; apply Hxy; symmetry; exact Hyx.
      + destruct (real_program_var_eq_dec y y); [reflexivity | contradiction].
    - destruct (real_program_var_eq_dec z x) as [-> | Hzx].
      + destruct (real_program_var_eq_dec x x); [|contradiction].
        destruct (real_program_var_eq_dec x y); [congruence | reflexivity].
      + destruct (real_program_var_eq_dec z x); [contradiction |].
        destruct (real_program_var_eq_dec z y); [contradiction | reflexivity].
  }
  unfold update_real; cbn.
  rewrite Hvalues; reflexivity.
Qed.

Lemma monte_carlo_subst_real_term_spec :
  forall (v : state) (x : RealProgramVar) (replacement t : Term),
    term_eval (subst_real_term x replacement t) v =
      term_eval t (update_real v x (term_eval replacement v)).
Proof.
  intros v x replacement t.
  induction t as [z | z | c | t1 IH1 t2 IH2 | t1 IH1 t2 IH2];
    cbn [subst_real_term term_eval update_real
    update_real_values] in *.
  - destruct (real_program_var_eq_dec z x); subst; cbn.
    + unfold update_real_values.
      destruct (real_program_var_eq_dec x x); [reflexivity | contradiction].
    + unfold update_real_values.
      destruct (real_program_var_eq_dec z x); [contradiction | reflexivity].
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2; reflexivity.
  - rewrite IH1, IH2; reflexivity.
Qed.

Lemma monte_carlo_subst_real_cformula_spec :
  forall (v : state) (x : RealProgramVar) (replacement : Term)
    (gamma : CFormula),
    satisfies v (subst_real_cformula x replacement gamma) <->
      satisfies (update_real v x (term_eval replacement v)) gamma.
Proof.
  intros v x replacement gamma.
  induction gamma; cbn [subst_real_cformula satisfies].
  - reflexivity.
  - reflexivity.
  - rewrite !monte_carlo_subst_real_term_spec; reflexivity.
  - reflexivity.
  - rewrite IHgamma1, IHgamma2; reflexivity.
Qed.

Lemma monte_carlo_time_band_sample_invariant :
  forall M r : nat,
    monte_carlo_sample_invariant (monte_carlo_time_band M r).
Proof.
  intros M r v x y.
  rewrite !monte_carlo_time_band_spec.
  cbn [update_real update_real_values].
  pose proof monte_carlo_variables_distinct as Hdistinct.
  destruct Hdistinct as [HXY Hdistinct].
  destruct Hdistinct as [HXi Hdistinct].
  destruct Hdistinct as [HXH Hdistinct].
  destruct Hdistinct as [HYi Hdistinct].
  destruct Hdistinct as [HYH HiH].
  destruct (real_program_var_eq_dec monte_carlo_i monte_carlo_Y);
    [congruence |].
  destruct (real_program_var_eq_dec monte_carlo_i monte_carlo_X);
    [congruence |].
  reflexivity.
Qed.

Lemma monte_carlo_exact_region_sample_invariant :
  forall M k r s : nat,
    monte_carlo_sample_invariant (monte_carlo_exact_region M k r s).
Proof.
  intros M k r s v x y.
  rewrite !monte_carlo_exact_region_spec.
  rewrite (monte_carlo_time_band_sample_invariant M r v x y).
  cbn [update_real update_real_values].
  pose proof monte_carlo_variables_distinct as Hdistinct.
  destruct Hdistinct as [HXY Hdistinct].
  destruct Hdistinct as [HXi Hdistinct].
  destruct Hdistinct as [HXH Hdistinct].
  destruct Hdistinct as [HYi Hdistinct].
  destruct Hdistinct as [HYH HiH].
  destruct (real_program_var_eq_dec monte_carlo_H monte_carlo_Y);
    [congruence |].
  destruct (real_program_var_eq_dec monte_carlo_H monte_carlo_X);
    [congruence |].
  reflexivity.
Qed.

Lemma monte_carlo_exact_regions_sample_invariant :
  forall M k r : nat,
    monte_carlo_sample_invariant (monte_carlo_exact_regions M k r).
Proof.
  intros M k r v x y.
  unfold monte_carlo_exact_regions.
  rewrite !monte_carlo_finite_c_or_spec.
  split.
  - intros [s Hs].
    destruct Hs as [Hsr Hregion].
    exists s; split; [exact Hsr |].
    apply (proj1 (monte_carlo_exact_region_sample_invariant M k r s v x y));
      exact Hregion.
  - intros [s Hs].
    destruct Hs as [Hsr Hregion].
    exists s; split; [exact Hsr |].
    apply (proj2 (monte_carlo_exact_region_sample_invariant M k r s v x y));
      exact Hregion.
Qed.

Lemma monte_carlo_other_region_sample_invariant :
  forall M k r : nat,
    monte_carlo_sample_invariant (monte_carlo_other_region M k r).
Proof.
  intros M k r v x y.
  unfold monte_carlo_other_region.
  rewrite !monte_carlo_c_and_spec.
  cbn [c_not satisfies].
  pose proof (monte_carlo_time_band_sample_invariant M r v x y) as Hband.
  pose proof (monte_carlo_exact_regions_sample_invariant M k r v x y)
    as Hexact.
  tauto.
Qed.

Lemma monte_carlo_region_sample_invariant :
  forall M k index : nat,
    monte_carlo_sample_invariant (monte_carlo_region M k index).
Proof.
  intros M k index.
  unfold monte_carlo_region.
  destruct (monte_carlo_region_remaining M index <=? M)%nat;
    [|intros v x y; reflexivity].
  destruct (monte_carlo_region_slot M index <=?
    monte_carlo_region_remaining M index)%nat.
  - apply monte_carlo_exact_region_sample_invariant.
  - destruct (monte_carlo_region_slot M index =? S M)%nat.
    + apply monte_carlo_other_region_sample_invariant.
    + intros v x y; reflexivity.
Qed.

Lemma monte_carlo_after_i_sample_invariant :
  forall gamma : CFormula,
    monte_carlo_sample_invariant gamma ->
    monte_carlo_sample_invariant (monte_carlo_after_i gamma).
Proof.
  intros gamma Hgamma v x y.
  unfold monte_carlo_after_i.
  rewrite !monte_carlo_subst_real_cformula_spec.
  pose proof monte_carlo_variables_distinct as Hdistinct.
  destruct Hdistinct as [HXY Hdistinct].
  destruct Hdistinct as [HXi Hdistinct].
  destruct Hdistinct as [HXH Hdistinct].
  destruct Hdistinct as [HYi Hdistinct].
  destruct Hdistinct as [HYH HiH].
  assert (Hvalue :
    term_eval <{ monte_carlo_i + 1 }>
      (update_real (update_real v monte_carlo_X x) monte_carlo_Y y) =
    term_eval <{ monte_carlo_i + 1 }> v).
  {
    cbn [term_eval update_real update_real_values].
    destruct (real_program_var_eq_dec monte_carlo_i monte_carlo_Y);
      [congruence |].
    destruct (real_program_var_eq_dec monte_carlo_i monte_carlo_X);
      [congruence |].
    reflexivity.
  }
  rewrite Hvalue.
  assert (Hcommute :
    update_real
      (update_real (update_real v monte_carlo_X x) monte_carlo_Y y)
      monte_carlo_i (term_eval <{ monte_carlo_i + 1 }> v) =
    update_real
      (update_real
        (update_real v monte_carlo_i
          (term_eval <{ monte_carlo_i + 1 }> v))
        monte_carlo_X x) monte_carlo_Y y).
  {
    rewrite (monte_carlo_update_real_commute
      (update_real v monte_carlo_X x) monte_carlo_Y monte_carlo_i)
      by congruence.
    rewrite (monte_carlo_update_real_commute v monte_carlo_X monte_carlo_i)
      by congruence.
    reflexivity.
  }
  rewrite Hcommute.
  apply Hgamma.
Qed.

Lemma monte_carlo_after_hit_sample_invariant :
  forall gamma : CFormula,
    monte_carlo_sample_invariant gamma ->
    monte_carlo_sample_invariant (monte_carlo_after_hit gamma).
Proof.
  intros gamma Hgamma.
  unfold monte_carlo_after_hit.
  apply (monte_carlo_after_i_sample_invariant gamma) in Hgamma as Hafter_i.
  intros v x y.
  rewrite !monte_carlo_subst_real_cformula_spec.
  pose proof monte_carlo_variables_distinct as Hdistinct.
  destruct Hdistinct as [HXY Hdistinct].
  destruct Hdistinct as [HXi Hdistinct].
  destruct Hdistinct as [HXH Hdistinct].
  destruct Hdistinct as [HYi Hdistinct].
  destruct Hdistinct as [HYH HiH].
  assert (Hvalue :
    term_eval <{ monte_carlo_H + 1 }>
      (update_real (update_real v monte_carlo_X x) monte_carlo_Y y) =
    term_eval <{ monte_carlo_H + 1 }> v).
  {
    cbn [term_eval update_real update_real_values].
    destruct (real_program_var_eq_dec monte_carlo_H monte_carlo_Y);
      [congruence |].
    destruct (real_program_var_eq_dec monte_carlo_H monte_carlo_X);
      [congruence |].
    reflexivity.
  }
  rewrite Hvalue.
  assert (Hcommute :
    update_real
      (update_real (update_real v monte_carlo_X x) monte_carlo_Y y)
      monte_carlo_H (term_eval <{ monte_carlo_H + 1 }> v) =
    update_real
      (update_real
        (update_real v monte_carlo_H
          (term_eval <{ monte_carlo_H + 1 }> v))
        monte_carlo_X x) monte_carlo_Y y).
  {
    rewrite (monte_carlo_update_real_commute
      (update_real v monte_carlo_X x) monte_carlo_Y monte_carlo_H)
      by congruence.
    rewrite (monte_carlo_update_real_commute v monte_carlo_X monte_carlo_H)
      by congruence.
    reflexivity.
  }
  rewrite Hcommute.
  apply Hafter_i.
Qed.

Lemma monte_carlo_hit_pre_construct_eval :
  forall (gamma : CFormula),
    monte_carlo_sample_invariant (monte_carlo_after_hit gamma) ->
    forall v : state,
      q_eval (monte_carlo_hit_pre_construct gamma) v =
        (monte_carlo_hit_probability *
          real_indicator (satisfies v (monte_carlo_after_hit gamma)))%R.
Proof.
  intros gamma Hinvariant v.
  destruct (excluded_middle_informative
    (satisfies v (monte_carlo_after_hit gamma))) as [Htrue | Hfalse].
  - rewrite (real_indicator_true _ Htrue), Rmult_1_r.
    transitivity (q_eval monte_carlo_hit_construct v).
    + unfold monte_carlo_hit_pre_construct, monte_carlo_hit_construct.
      cbn [q_eval].
      apply real_integral_extensional; intro x.
      apply f_equal2 with (f := Rmult); [reflexivity |].
      apply real_integral_extensional; intro y.
      apply f_equal2 with (f := Rmult); [reflexivity |].
      apply real_indicator_extensional.
      rewrite monte_carlo_c_and_spec.
      pose proof (Hinvariant v x y) as HA.
      tauto.
    + apply monte_carlo_hit_construct_eval.
  - rewrite (real_indicator_false _ Hfalse), Rmult_0_r.
    unfold monte_carlo_hit_pre_construct.
    cbn [q_eval].
    transitivity (real_integral (fun _ : R => 0%R)).
    + apply real_integral_extensional; intro x.
      transitivity
        (distribution_density <{ uniform ( 0, 1 ) }> v x * 0)%R.
      * apply f_equal2 with (f := Rmult); [reflexivity |].
        transitivity (real_integral (fun _ : R => 0%R)).
        -- apply real_integral_extensional; intro y.
           transitivity
             (distribution_density <{ uniform ( 0, 1 ) }>
                (update_real v monte_carlo_X x) y * 0)%R.
           ++ apply f_equal2 with (f := Rmult); [reflexivity |].
              apply real_indicator_false.
              intro Hboth.
              apply monte_carlo_c_and_spec in Hboth.
              pose proof (Hinvariant v x y) as HA.
              apply Hfalse; apply HA; exact (proj1 Hboth).
           ++ ring.
        -- apply real_integral_zero.
      * ring.
    + apply real_integral_zero.
Qed.

Lemma monte_carlo_miss_pre_construct_eval :
  forall (gamma : CFormula),
    monte_carlo_sample_invariant (monte_carlo_after_i gamma) ->
    forall v : state,
      q_eval (monte_carlo_miss_pre_construct gamma) v =
        ((1 - monte_carlo_hit_probability) *
          real_indicator (satisfies v (monte_carlo_after_i gamma)))%R.
Proof.
  intros gamma Hinvariant v.
  destruct (excluded_middle_informative
    (satisfies v (monte_carlo_after_i gamma))) as [Htrue | Hfalse].
  - rewrite (real_indicator_true _ Htrue), Rmult_1_r.
    transitivity (q_eval monte_carlo_miss_construct v).
    + unfold monte_carlo_miss_pre_construct, monte_carlo_miss_construct.
      cbn [q_eval].
      apply real_integral_extensional; intro x.
      apply f_equal2 with (f := Rmult); [reflexivity |].
      apply real_integral_extensional; intro y.
      apply f_equal2 with (f := Rmult); [reflexivity |].
      apply real_indicator_extensional.
      rewrite monte_carlo_c_and_spec.
      pose proof (Hinvariant v x y) as HA.
      tauto.
    + apply monte_carlo_miss_construct_eval.
  - rewrite (real_indicator_false _ Hfalse), Rmult_0_r.
    unfold monte_carlo_miss_pre_construct.
    cbn [q_eval].
    transitivity (real_integral (fun _ : R => 0%R)).
    + apply real_integral_extensional; intro x.
      transitivity
        (distribution_density <{ uniform ( 0, 1 ) }> v x * 0)%R.
      * apply f_equal2 with (f := Rmult); [reflexivity |].
        transitivity (real_integral (fun _ : R => 0%R)).
        -- apply real_integral_extensional; intro y.
           transitivity
             (distribution_density <{ uniform ( 0, 1 ) }>
                (update_real v monte_carlo_X x) y * 0)%R.
           ++ apply f_equal2 with (f := Rmult); [reflexivity |].
              apply real_indicator_false.
              intro Hboth.
              apply monte_carlo_c_and_spec in Hboth.
              pose proof (Hinvariant v x y) as HA.
              apply Hfalse; apply HA; exact (proj1 Hboth).
           ++ ring.
        -- apply real_integral_zero.
      * ring.
    + apply real_integral_zero.
Qed.

Lemma monte_carlo_p_and_spec :
  forall (ps : Pstate) (eta theta : PFormula),
    psatisfies ps (p_and eta theta) <->
      psatisfies ps eta /\ psatisfies ps theta.
Proof.
  intros ps eta theta.
  unfold p_and, p_not; cbn [psatisfies]; tauto.
Qed.

Lemma monte_carlo_p_eq_spec :
  forall (ps : Pstate) (p q : Pterm),
    psatisfies ps (p_eq p q) <-> pterm_eval p ps = pterm_eval q ps.
Proof.
  intros ps p q.
  unfold p_eq.
  rewrite monte_carlo_p_and_spec.
  cbn [psatisfies]; lra.
Qed.

Lemma monte_carlo_measure_monotone :
  forall (mu : Measure) (A B : Assertion),
    (forall v : state, A v -> B v) ->
    (measure_of mu A <= measure_of mu B)%R.
Proof.
  intros mu A B Hsubset.
  set (C := fun v : state => B v /\ ~ A v).
  assert (Hpartition :
    measure_of mu B = (measure_of mu A + measure_of mu C)%R).
  {
    transitivity (measure_of mu (fun v => A v \/ C v)).
    - apply measure_extensional; intro v; unfold C.
      split.
      + intro HB.
        destruct (classic (A v)); tauto.
      + intro Hor; destruct Hor as [HA | HC].
        * apply Hsubset; exact HA.
        * destruct HC as [HB HnotA]; exact HB.
    - apply measure_additive.
      intro v; unfold C; tauto.
  }
  pose proof (measure_nonnegative mu C).
  lra.
Qed.

Lemma monte_carlo_concentrated_unit_values :
  forall (ps : Pstate) (rho : CFormula),
    psatisfies ps (p_concentrated_mass rho (PConst 1%R)) ->
    measure_of (pstate_measure ps) (formula_assertion rho) = 1%R /\
    measure_of (pstate_measure ps) (fun _ : state => True) = 1%R.
Proof.
  intros ps rho Hconcentrated.
  unfold p_concentrated_mass in Hconcentrated.
  apply monte_carlo_p_and_spec in Hconcentrated.
  destruct Hconcentrated as [Hrho Htotal].
  apply monte_carlo_p_eq_spec in Hrho.
  apply monte_carlo_p_eq_spec in Htotal.
  cbn [pterm_eval] in Hrho, Htotal.
  rewrite expectation_indicator in Hrho.
  rewrite expectation_indicator in Hrho.
  rewrite expectation_indicator in Htotal.
  assert (Htrue :
    measure_of (pstate_measure ps) (formula_assertion c_true) =
      measure_of (pstate_measure ps) (fun _ : state => True)).
  {
    apply measure_extensional.
    intro v; unfold formula_assertion, c_true.
    cbn [satisfies]; tauto.
  }
  split; lra.
Qed.

Lemma monte_carlo_concentrated_event_full :
  forall (ps : Pstate) (rho gamma : CFormula),
    psatisfies ps (p_concentrated_mass rho (PConst 1%R)) ->
    cformula_valid <{ $(rho) -> $(gamma) }> ->
    measure_of (pstate_measure ps) (formula_assertion gamma) = 1%R.
Proof.
  intros ps rho gamma Hconcentrated Hsubset.
  pose proof (monte_carlo_concentrated_unit_values ps rho Hconcentrated)
    as [Hrho Htotal].
  pose proof (monte_carlo_measure_monotone (pstate_measure ps)
    (formula_assertion rho) (formula_assertion gamma)) as Hlower.
  specialize (Hlower (fun v Hrho_v => Hsubset v Hrho_v)).
  pose proof (monte_carlo_measure_monotone (pstate_measure ps)
    (formula_assertion gamma) (fun _ : state => True)) as Hupper.
  specialize (Hupper (fun _ _ => I)).
  lra.
Qed.

Lemma monte_carlo_concentrated_event_zero :
  forall (ps : Pstate) (rho gamma : CFormula),
    psatisfies ps (p_concentrated_mass rho (PConst 1%R)) ->
    cformula_valid <{ ~ ($(rho) /\ $(gamma)) }> ->
    measure_of (pstate_measure ps) (formula_assertion gamma) = 0%R.
Proof.
  intros ps rho gamma Hconcentrated Hdisjoint.
  pose proof (monte_carlo_concentrated_unit_values ps rho Hconcentrated)
    as [Hrho Htotal].
  set (outside := fun v : state => ~ formula_assertion rho v).
  assert (Houtside : measure_of (pstate_measure ps) outside = 0%R).
  {
    assert (Hpartition :
      measure_of (pstate_measure ps) (fun _ : state => True) =
        (measure_of (pstate_measure ps) (formula_assertion rho) +
         measure_of (pstate_measure ps) outside)%R).
    {
      transitivity
        (measure_of (pstate_measure ps)
          (fun v => formula_assertion rho v \/ outside v)).
      - apply measure_extensional; intro v; unfold outside; tauto.
      - apply measure_additive; intro v; unfold outside; tauto.
    }
    lra.
  }
  pose proof (monte_carlo_measure_monotone (pstate_measure ps)
    (formula_assertion gamma) outside) as Hupper.
  specialize (Hupper (fun v Hgamma_v =>
    fun Hrho_v => Hdisjoint v
      ((proj2 (monte_carlo_c_and_spec v rho gamma))
        (conj Hrho_v Hgamma_v)))).
  pose proof (measure_nonnegative (pstate_measure ps)
    (formula_assertion gamma)).
  lra.
Qed.

Definition monte_carlo_miss_state (v : state) : state :=
  update_real v monte_carlo_i
    (real_program_values v monte_carlo_i + 1).

Definition monte_carlo_hit_state (v : state) : state :=
  update_real
    (update_real v monte_carlo_H
      (real_program_values v monte_carlo_H + 1))
    monte_carlo_i (real_program_values v monte_carlo_i + 1).

Lemma monte_carlo_after_i_spec :
  forall (v : state) (gamma : CFormula),
    satisfies v (monte_carlo_after_i gamma) <->
      satisfies (monte_carlo_miss_state v) gamma.
Proof.
  intros v gamma.
  unfold monte_carlo_after_i, monte_carlo_miss_state.
  rewrite monte_carlo_subst_real_cformula_spec.
  cbn [term_eval].
  reflexivity.
Qed.

Lemma monte_carlo_after_hit_spec :
  forall (v : state) (gamma : CFormula),
    satisfies v (monte_carlo_after_hit gamma) <->
      satisfies (monte_carlo_hit_state v) gamma.
Proof.
  intros v gamma.
  unfold monte_carlo_after_hit.
  rewrite monte_carlo_subst_real_cformula_spec.
  rewrite monte_carlo_after_i_spec.
  unfold monte_carlo_hit_state, monte_carlo_miss_state.
  cbn [term_eval update_real update_real_values].
  pose proof monte_carlo_variables_distinct as Hdistinct.
  destruct Hdistinct as [HXY Hdistinct].
  destruct Hdistinct as [HXi Hdistinct].
  destruct Hdistinct as [HXH Hdistinct].
  destruct Hdistinct as [HYi Hdistinct].
  destruct Hdistinct as [HYH HiH].
  destruct (real_program_var_eq_dec monte_carlo_i monte_carlo_H);
    [congruence | reflexivity].
Qed.

Lemma monte_carlo_time_band_after_step :
  forall (M r : nat) (v : state),
    (1 < r <= M)%nat ->
    satisfies v (monte_carlo_time_band M r) ->
    satisfies (monte_carlo_miss_state v)
      (monte_carlo_time_band M (r - 1)).
Proof.
  intros M r v Hr Hband.
  apply monte_carlo_time_band_spec in Hband.
  apply monte_carlo_time_band_spec.
  unfold monte_carlo_miss_state.
  cbn [update_real update_real_values].
  destruct (real_program_var_eq_dec monte_carlo_i monte_carlo_i);
    [|contradiction].
  assert (Hstart : (M - (r - 1) = M - r + 1)%nat) by lia.
  assert (Hend : (M - (r - 1) + 1 = M - r + 2)%nat) by lia.
  rewrite Hend, Hstart.
  rewrite !plus_INR.
  rewrite plus_INR in Hband.
  cbn [INR].
  cbn [INR] in Hband.
  change
    (INR (M - r) + 1 <=
      update_real_values (real_program_values v) monte_carlo_i
        (real_program_values v monte_carlo_i + 1) monte_carlo_i <
      INR (M - r) + (1 + 1))%R.
  unfold update_real_values.
  destruct (real_program_var_eq_dec monte_carlo_i monte_carlo_i);
    [lra | contradiction].
Qed.

Lemma monte_carlo_time_band_after_hit_step :
  forall (M r : nat) (v : state),
    (1 < r <= M)%nat ->
    satisfies v (monte_carlo_time_band M r) ->
    satisfies (monte_carlo_hit_state v)
      (monte_carlo_time_band M (r - 1)).
Proof.
  intros M r v Hr Hband.
  unfold monte_carlo_hit_state.
  assert (Hsame_i :
    real_program_values
      (update_real v monte_carlo_H
        (real_program_values v monte_carlo_H + 1)) monte_carlo_i =
      real_program_values v monte_carlo_i).
  {
    cbn [update_real update_real_values].
    pose proof monte_carlo_variables_distinct as Hdistinct.
    destruct Hdistinct as [HXY Hdistinct].
    destruct Hdistinct as [HXi Hdistinct].
    destruct Hdistinct as [HXH Hdistinct].
    destruct Hdistinct as [HYi Hdistinct].
    destruct Hdistinct as [HYH HiH].
    destruct (real_program_var_eq_dec monte_carlo_i monte_carlo_H);
      [congruence | reflexivity].
  }
  replace (real_program_values v monte_carlo_i + 1)%R with
    (real_program_values
      (update_real v monte_carlo_H
        (real_program_values v monte_carlo_H + 1)) monte_carlo_i + 1)%R
    by (rewrite Hsame_i; reflexivity).
  fold (monte_carlo_miss_state
    (update_real v monte_carlo_H
      (real_program_values v monte_carlo_H + 1))).
  apply monte_carlo_time_band_after_step; [exact Hr |].
  apply monte_carlo_time_band_spec.
  apply monte_carlo_time_band_spec in Hband.
  cbn [update_real update_real_values].
  pose proof monte_carlo_variables_distinct as Hdistinct.
  destruct Hdistinct as [HXY Hdistinct].
  destruct Hdistinct as [HXi Hdistinct].
  destruct Hdistinct as [HXH Hdistinct].
  destruct Hdistinct as [HYi Hdistinct].
  destruct Hdistinct as [HYH HiH].
  destruct (real_program_var_eq_dec monte_carlo_i monte_carlo_H);
    [congruence | exact Hband].
Qed.

Lemma monte_carlo_miss_state_H :
  forall v : state,
    real_program_values (monte_carlo_miss_state v) monte_carlo_H =
      real_program_values v monte_carlo_H.
Proof.
  intro v.
  unfold monte_carlo_miss_state.
  cbn [update_real update_real_values].
  pose proof monte_carlo_variables_distinct as Hdistinct.
  destruct Hdistinct as [HXY Hdistinct].
  destruct Hdistinct as [HXi Hdistinct].
  destruct Hdistinct as [HXH Hdistinct].
  destruct Hdistinct as [HYi Hdistinct].
  destruct Hdistinct as [HYH HiH].
  destruct (real_program_var_eq_dec monte_carlo_H monte_carlo_i);
    [congruence | reflexivity].
Qed.

Lemma monte_carlo_hit_state_H :
  forall v : state,
    real_program_values (monte_carlo_hit_state v) monte_carlo_H =
      (real_program_values v monte_carlo_H + 1)%R.
Proof.
  intro v.
  unfold monte_carlo_hit_state.
  cbn [update_real update_real_values].
  pose proof monte_carlo_variables_distinct as Hdistinct.
  destruct Hdistinct as [HXY Hdistinct].
  destruct Hdistinct as [HXi Hdistinct].
  destruct Hdistinct as [HXH Hdistinct].
  destruct Hdistinct as [HYi Hdistinct].
  destruct Hdistinct as [HYH HiH].
  destruct (real_program_var_eq_dec monte_carlo_H monte_carlo_i);
    [congruence |].
  destruct (real_program_var_eq_dec monte_carlo_H monte_carlo_H);
    [reflexivity | contradiction].
Qed.

Lemma monte_carlo_miss_state_i :
  forall v : state,
    real_program_values (monte_carlo_miss_state v) monte_carlo_i =
      (real_program_values v monte_carlo_i + 1)%R.
Proof.
  intro v.
  unfold monte_carlo_miss_state.
  cbn [update_real update_real_values].
  destruct (real_program_var_eq_dec monte_carlo_i monte_carlo_i);
    [reflexivity | contradiction].
Qed.

Lemma monte_carlo_hit_state_i :
  forall v : state,
    real_program_values (monte_carlo_hit_state v) monte_carlo_i =
      (real_program_values v monte_carlo_i + 1)%R.
Proof.
  intro v.
  unfold monte_carlo_hit_state.
  cbn [update_real update_real_values].
  pose proof monte_carlo_variables_distinct as Hdistinct.
  destruct Hdistinct as [HXY Hdistinct].
  destruct Hdistinct as [HXi Hdistinct].
  destruct Hdistinct as [HXH Hdistinct].
  destruct Hdistinct as [HYi Hdistinct].
  destruct Hdistinct as [HYH HiH].
  destruct (real_program_var_eq_dec monte_carlo_i monte_carlo_i);
    [|contradiction].
  destruct (real_program_var_eq_dec monte_carlo_i monte_carlo_H);
    [congruence | reflexivity].
Qed.

Lemma monte_carlo_hit_maps_to_destination :
  forall M k index : nat,
    (index < monte_carlo_region_count M)%nat ->
    monte_carlo_row_active M index = true ->
    (1 < monte_carlo_region_remaining M index)%nat ->
    cformula_valid
      <{ $(monte_carlo_region M k index) ->
         $(monte_carlo_after_hit
           (monte_carlo_region M k
             (monte_carlo_hit_destination M index))) }>.
Proof.
  intros M k index Hindex Hactive Hrmore v Hsource.
  pose proof (monte_carlo_region_bounded_decode M index Hindex)
    as [Hr Hs].
  pose proof (monte_carlo_region_bounded_shape M k index Hindex)
    as Hshape.
  destruct Hshape as [Hexact_case | Hrest].
  - destruct Hexact_case as [Hsr Hregion].
    rewrite Hregion in Hsource.
    apply monte_carlo_exact_region_spec in Hsource.
    destruct Hsource as [Hband HH].
    unfold monte_carlo_hit_destination.
    unfold monte_carlo_hit_destination_slot.
    assert (Hnot_other :
      (monte_carlo_region_slot M index =? S M)%nat = false) by
      (apply Nat.eqb_neq; unfold monte_carlo_block_width in Hs; lia).
    rewrite Hnot_other.
    destruct (monte_carlo_region_slot M index) as [|s] eqn:Hslot.
    + rewrite monte_carlo_region_index_other by lia.
      apply monte_carlo_after_hit_spec.
      unfold monte_carlo_other_region.
      apply monte_carlo_c_and_spec.
      split.
      * apply monte_carlo_time_band_after_hit_step; [lia | exact Hband].
      * unfold c_not; cbn [satisfies].
        intro Hsome.
        apply monte_carlo_finite_c_or_spec in Hsome.
        destruct Hsome as [t Hsome].
        destruct Hsome as [Htr Htarget].
        apply monte_carlo_exact_region_spec in Htarget.
        destruct Htarget as [Htarget_band Htarget_H].
        rewrite monte_carlo_hit_state_H in Htarget_H.
        pose proof (le_INR 0 t (Nat.le_0_l _)).
        cbn [INR] in H.
        cbn [INR] in HH.
        lra.
    + rewrite monte_carlo_region_index_exact by lia.
      apply monte_carlo_after_hit_spec.
      apply monte_carlo_exact_region_spec.
      split.
      * apply monte_carlo_time_band_after_hit_step; [lia | exact Hband].
      * rewrite monte_carlo_hit_state_H.
        rewrite S_INR in HH.
        lra.
  - destruct Hrest as [Hother_case | Hfalse].
    + destruct Hother_case as [Hslot Hregion].
      rewrite Hregion in Hsource.
      unfold monte_carlo_other_region in Hsource.
      apply monte_carlo_c_and_spec in Hsource.
      destruct Hsource as [Hband Hnot_exact].
      unfold c_not in Hnot_exact; cbn [satisfies] in Hnot_exact.
      unfold monte_carlo_hit_destination,
        monte_carlo_hit_destination_slot.
      rewrite Hslot, Nat.eqb_refl.
      rewrite monte_carlo_region_index_other by lia.
      apply monte_carlo_after_hit_spec.
      unfold monte_carlo_other_region.
      apply monte_carlo_c_and_spec.
      split.
      * apply monte_carlo_time_band_after_hit_step; [lia | exact Hband].
      * unfold c_not; cbn [satisfies].
        intro Hsome.
        apply monte_carlo_finite_c_or_spec in Hsome.
        destruct Hsome as [t Hsome].
        destruct Hsome as [Htr Htarget].
        apply monte_carlo_exact_region_spec in Htarget.
        destruct Htarget as [Htarget_band Htarget_H].
        rewrite monte_carlo_hit_state_H in Htarget_H.
        apply Hnot_exact.
        apply monte_carlo_finite_c_or_spec.
        exists (S t); split; [lia |].
        apply monte_carlo_exact_region_spec.
        split; [exact Hband |].
        rewrite S_INR; lra.
    + rewrite Hfalse in Hsource.
      cbn [satisfies] in Hsource; contradiction.
Qed.

Lemma monte_carlo_miss_maps_to_destination :
  forall M k index : nat,
    (index < monte_carlo_region_count M)%nat ->
    monte_carlo_row_active M index = true ->
    (1 < monte_carlo_region_remaining M index)%nat ->
    cformula_valid
      <{ $(monte_carlo_region M k index) ->
         $(monte_carlo_after_i
           (monte_carlo_region M k
             (monte_carlo_miss_destination M index))) }>.
Proof.
  intros M k index Hindex Hactive Hrmore v Hsource.
  pose proof (monte_carlo_region_bounded_decode M index Hindex)
    as [Hr Hs].
  pose proof (monte_carlo_region_bounded_shape M k index Hindex)
    as Hshape.
  destruct Hshape as [Hexact_case | Hrest].
  - destruct Hexact_case as [Hsr Hregion].
    rewrite Hregion in Hsource.
    apply monte_carlo_exact_region_spec in Hsource.
    destruct Hsource as [Hband HH].
    unfold monte_carlo_miss_destination,
      monte_carlo_miss_destination_slot.
    assert (Hnot_other :
      (monte_carlo_region_slot M index =? S M)%nat = false) by
      (apply Nat.eqb_neq; unfold monte_carlo_block_width in Hs; lia).
    rewrite Hnot_other.
    destruct (monte_carlo_region_slot M index =?
      monte_carlo_region_remaining M index)%nat eqn:Hsame.
    + apply Nat.eqb_eq in Hsame.
      rewrite monte_carlo_region_index_other by lia.
      apply monte_carlo_after_i_spec.
      unfold monte_carlo_other_region.
      apply monte_carlo_c_and_spec.
      split.
      * apply monte_carlo_time_band_after_step; [lia | exact Hband].
      * unfold c_not; cbn [satisfies].
        intro Hsome.
        apply monte_carlo_finite_c_or_spec in Hsome.
        destruct Hsome as [t Hsome].
        destruct Hsome as [Htr Htarget].
        apply monte_carlo_exact_region_spec in Htarget.
        destruct Htarget as [Htarget_band Htarget_H].
        rewrite monte_carlo_miss_state_H in Htarget_H.
        assert (Htneq : INR (monte_carlo_region_remaining M index) <>
          INR t) by
          (intro Heq; apply INR_eq in Heq; lia).
        rewrite Hsame in HH.
        apply Htneq; lra.
    + apply Nat.eqb_neq in Hsame.
      rewrite monte_carlo_region_index_exact by lia.
      apply monte_carlo_after_i_spec.
      apply monte_carlo_exact_region_spec.
      split.
      * apply monte_carlo_time_band_after_step; [lia | exact Hband].
      * rewrite monte_carlo_miss_state_H; exact HH.
  - destruct Hrest as [Hother_case | Hfalse].
    + destruct Hother_case as [Hslot Hregion].
      rewrite Hregion in Hsource.
      unfold monte_carlo_other_region in Hsource.
      apply monte_carlo_c_and_spec in Hsource.
      destruct Hsource as [Hband Hnot_exact].
      unfold c_not in Hnot_exact; cbn [satisfies] in Hnot_exact.
      unfold monte_carlo_miss_destination,
        monte_carlo_miss_destination_slot.
      rewrite Hslot, Nat.eqb_refl.
      rewrite monte_carlo_region_index_other by lia.
      apply monte_carlo_after_i_spec.
      unfold monte_carlo_other_region.
      apply monte_carlo_c_and_spec.
      split.
      * apply monte_carlo_time_band_after_step; [lia | exact Hband].
      * unfold c_not; cbn [satisfies].
        intro Hsome.
        apply monte_carlo_finite_c_or_spec in Hsome.
        destruct Hsome as [t Hsome].
        destruct Hsome as [Htr Htarget].
        apply monte_carlo_exact_region_spec in Htarget.
        destruct Htarget as [Htarget_band Htarget_H].
        rewrite monte_carlo_miss_state_H in Htarget_H.
        apply Hnot_exact.
        apply monte_carlo_finite_c_or_spec.
        exists t; split; [lia |].
        apply monte_carlo_exact_region_spec.
        split; [exact Hband | exact Htarget_H].
    + rewrite Hfalse in Hsource.
      cbn [satisfies] in Hsource; contradiction.
Qed.

Lemma monte_carlo_regions_pairwise_disjoint :
  forall M k left right : nat,
    (left < monte_carlo_region_count M)%nat ->
    (right < monte_carlo_region_count M)%nat ->
    left <> right ->
    cformula_valid
      <{ ~ ($(monte_carlo_region M k left) /\
             $(monte_carlo_region M k right)) }>.
Proof.
  intros M k left right Hleft Hright Hneq.
  destruct (Nat.lt_ge_cases right left) as [Hrl | Hlr].
  - exact (monte_carlo_regions_disjoint M k left right Hleft Hrl).
  - intros v Hboth.
    apply monte_carlo_c_and_spec in Hboth.
    eapply (monte_carlo_regions_disjoint M k right left Hright);
      [lia |].
    apply monte_carlo_c_and_spec.
    split; [exact (proj2 Hboth) | exact (proj1 Hboth)].
Qed.

Lemma monte_carlo_hit_non_destination_disjoint :
  forall M k index destination : nat,
    (index < monte_carlo_region_count M)%nat ->
    (destination < monte_carlo_region_count M)%nat ->
    monte_carlo_row_active M index = true ->
    (1 < monte_carlo_region_remaining M index)%nat ->
    destination <> monte_carlo_hit_destination M index ->
    cformula_valid
      <{ ~ ($(monte_carlo_region M k index) /\
             $(monte_carlo_after_hit
               (monte_carlo_region M k destination))) }>.
Proof.
  intros M k index destination Hindex Hdestination Hactive Hrmore Hneq
    v Hboth.
  apply monte_carlo_c_and_spec in Hboth.
  destruct Hboth as [Hsource Htarget].
  pose proof (monte_carlo_hit_maps_to_destination
    M k index Hindex Hactive Hrmore v Hsource) as Hmapped.
  apply monte_carlo_after_hit_spec in Hmapped.
  apply monte_carlo_after_hit_spec in Htarget.
  pose proof (proj1 (monte_carlo_destinations_bound
    M index Hindex Hactive Hrmore)) as Hhit_bound.
  assert (Hdifferent :
    monte_carlo_hit_destination M index <> destination) by congruence.
  pose proof (monte_carlo_regions_pairwise_disjoint M k
    (monte_carlo_hit_destination M index) destination
    Hhit_bound Hdestination Hdifferent (monte_carlo_hit_state v)) as Hdisjoint.
  apply Hdisjoint.
  apply monte_carlo_c_and_spec; split;
    [exact Hmapped | exact Htarget].
Qed.

Lemma monte_carlo_miss_non_destination_disjoint :
  forall M k index destination : nat,
    (index < monte_carlo_region_count M)%nat ->
    (destination < monte_carlo_region_count M)%nat ->
    monte_carlo_row_active M index = true ->
    (1 < monte_carlo_region_remaining M index)%nat ->
    destination <> monte_carlo_miss_destination M index ->
    cformula_valid
      <{ ~ ($(monte_carlo_region M k index) /\
             $(monte_carlo_after_i
               (monte_carlo_region M k destination))) }>.
Proof.
  intros M k index destination Hindex Hdestination Hactive Hrmore Hneq
    v Hboth.
  apply monte_carlo_c_and_spec in Hboth.
  destruct Hboth as [Hsource Htarget].
  pose proof (monte_carlo_miss_maps_to_destination
    M k index Hindex Hactive Hrmore v Hsource) as Hmapped.
  apply monte_carlo_after_i_spec in Hmapped.
  apply monte_carlo_after_i_spec in Htarget.
  pose proof (proj2 (monte_carlo_destinations_bound
    M index Hindex Hactive Hrmore)) as Hmiss_bound.
  assert (Hdifferent :
    monte_carlo_miss_destination M index <> destination) by congruence.
  pose proof (monte_carlo_regions_pairwise_disjoint M k
    (monte_carlo_miss_destination M index) destination
    Hmiss_bound Hdestination Hdifferent (monte_carlo_miss_state v)) as Hdisjoint.
  apply Hdisjoint.
  apply monte_carlo_c_and_spec; split;
    [exact Hmapped | exact Htarget].
Qed.

Lemma monte_carlo_final_source_time_band :
  forall M k index v,
    (index < monte_carlo_region_count M)%nat ->
    monte_carlo_row_active M index = true ->
    monte_carlo_region_remaining M index = 1%nat ->
    satisfies v (monte_carlo_region M k index) ->
    satisfies v (monte_carlo_time_band M 1).
Proof.
  intros M k index v Hindex Hactive Hr_one Hsource.
  pose proof (monte_carlo_region_bounded_shape M k index Hindex)
    as Hshape.
  destruct Hshape as [Hexact | Hrest].
  - destruct Hexact as [Hsr Hregion].
    rewrite Hregion in Hsource.
    apply monte_carlo_exact_region_spec in Hsource.
    rewrite Hr_one in Hsource; exact (proj1 Hsource).
  - destruct Hrest as [Hother | Hfalse].
    + destruct Hother as [Hslot Hregion].
      rewrite Hregion in Hsource.
      unfold monte_carlo_other_region in Hsource.
      apply monte_carlo_c_and_spec in Hsource.
      rewrite Hr_one in Hsource; exact (proj1 Hsource).
    + rewrite Hfalse in Hsource.
      cbn [satisfies] in Hsource; contradiction.
Qed.

Lemma monte_carlo_final_step_not_guard_miss :
  forall M k index : nat,
    (index < monte_carlo_region_count M)%nat ->
    monte_carlo_row_active M index = true ->
    monte_carlo_region_remaining M index = 1%nat ->
    cformula_valid
      <{ $(monte_carlo_region M k index) ->
         $(monte_carlo_after_i <{ ~ $(monte_carlo_guard M) }>) }>.
Proof.
  intros M k index Hindex Hactive Hr_one v Hsource.
  apply monte_carlo_after_i_spec.
  unfold c_not; cbn [satisfies].
  intro Hguard.
  unfold monte_carlo_guard in Hguard.
  apply monte_carlo_c_and_spec in Hguard.
  cbn [satisfies c_lt c_not term_eval] in Hguard.
  destruct Hguard as [Hnonnegative Hnotle].
  apply Rnot_le_lt in Hnotle.
  rename Hnotle into Hguard'.
  pose proof (monte_carlo_final_source_time_band
    M k index v Hindex Hactive Hr_one Hsource) as Hband.
  apply monte_carlo_time_band_spec in Hband.
  rewrite monte_carlo_miss_state_i in Hguard'.
  assert (HMpositive : (1 <= M)%nat) by
    (pose proof (monte_carlo_region_bounded_decode M index Hindex); lia).
  rewrite (minus_INR M 1 HMpositive) in Hband.
  cbn [INR] in Hband.
  lra.
Qed.

Lemma monte_carlo_final_step_not_guard_hit :
  forall M k index : nat,
    (index < monte_carlo_region_count M)%nat ->
    monte_carlo_row_active M index = true ->
    monte_carlo_region_remaining M index = 1%nat ->
    cformula_valid
      <{ $(monte_carlo_region M k index) ->
         $(monte_carlo_after_hit <{ ~ $(monte_carlo_guard M) }>) }>.
Proof.
  intros M k index Hindex Hactive Hr_one v Hsource.
  apply monte_carlo_after_hit_spec.
  unfold c_not; cbn [satisfies].
  intro Hguard.
  unfold monte_carlo_guard in Hguard.
  apply monte_carlo_c_and_spec in Hguard.
  cbn [satisfies c_lt c_not term_eval] in Hguard.
  destruct Hguard as [Hnonnegative Hnotle].
  apply Rnot_le_lt in Hnotle.
  rename Hnotle into Hguard'.
  pose proof (monte_carlo_final_source_time_band
    M k index v Hindex Hactive Hr_one Hsource) as Hband.
  apply monte_carlo_time_band_spec in Hband.
  rewrite monte_carlo_hit_state_i in Hguard'.
  assert (HMpositive : (1 <= M)%nat) by
    (pose proof (monte_carlo_region_bounded_decode M index Hindex); lia).
  rewrite (minus_INR M 1 HMpositive) in Hband.
  cbn [INR] in Hband.
  lra.
Qed.

Lemma monte_carlo_final_hit_region_disjoint :
  forall M k index destination : nat,
    (index < monte_carlo_region_count M)%nat ->
    (destination < monte_carlo_region_count M)%nat ->
    monte_carlo_row_active M index = true ->
    monte_carlo_region_remaining M index = 1%nat ->
    cformula_valid
      <{ ~ ($(monte_carlo_region M k index) /\
             $(monte_carlo_after_hit
               (monte_carlo_region M k destination))) }>.
Proof.
  intros M k index destination Hindex Hdestination Hactive Hr_one v Hboth.
  apply monte_carlo_c_and_spec in Hboth.
  destruct Hboth as [Hsource Htarget].
  pose proof (monte_carlo_final_step_not_guard_hit
    M k index Hindex Hactive Hr_one v Hsource) as Hnot_guard.
  apply monte_carlo_after_hit_spec in Hnot_guard.
  apply monte_carlo_after_hit_spec in Htarget.
  apply Hnot_guard.
  eapply monte_carlo_regions_in_guard;
    [exact Hdestination | exact Htarget].
Qed.

Lemma monte_carlo_final_miss_region_disjoint :
  forall M k index destination : nat,
    (index < monte_carlo_region_count M)%nat ->
    (destination < monte_carlo_region_count M)%nat ->
    monte_carlo_row_active M index = true ->
    monte_carlo_region_remaining M index = 1%nat ->
    cformula_valid
      <{ ~ ($(monte_carlo_region M k index) /\
             $(monte_carlo_after_i
               (monte_carlo_region M k destination))) }>.
Proof.
  intros M k index destination Hindex Hdestination Hactive Hr_one v Hboth.
  apply monte_carlo_c_and_spec in Hboth.
  destruct Hboth as [Hsource Htarget].
  pose proof (monte_carlo_final_step_not_guard_miss
    M k index Hindex Hactive Hr_one v Hsource) as Hnot_guard.
  apply monte_carlo_after_i_spec in Hnot_guard.
  apply monte_carlo_after_i_spec in Htarget.
  apply Hnot_guard.
  eapply monte_carlo_regions_in_guard;
    [exact Hdestination | exact Htarget].
Qed.

Lemma monte_carlo_scaled_construct_full :
  forall (ps : Pstate) (rho gamma : CFormula) (q : PConstruct) (c : R),
    psatisfies ps (p_concentrated_mass rho (PConst 1%R)) ->
    (forall v : state,
      q_eval q v = (c * real_indicator (satisfies v gamma))%R) ->
    cformula_valid <{ $(rho) -> $(gamma) }> ->
    expectation (pstate_measure ps) (q_eval q) = c.
Proof.
  intros ps rho gamma q c Hconcentrated Hq Hsubset.
  transitivity
    (expectation (pstate_measure ps)
      (fun v => c * q_eval (QIndicator gamma) v)).
  - apply expectation_extensional; intro v.
    rewrite Hq; reflexivity.
  - rewrite expectation_scale, expectation_indicator.
    rewrite (monte_carlo_concentrated_event_full
      ps rho gamma Hconcentrated Hsubset).
    ring.
Qed.

Lemma monte_carlo_scaled_construct_zero :
  forall (ps : Pstate) (rho gamma : CFormula) (q : PConstruct) (c : R),
    psatisfies ps (p_concentrated_mass rho (PConst 1%R)) ->
    (forall v : state,
      q_eval q v = (c * real_indicator (satisfies v gamma))%R) ->
    cformula_valid <{ ~ ($(rho) /\ $(gamma)) }> ->
    expectation (pstate_measure ps) (q_eval q) = 0%R.
Proof.
  intros ps rho gamma q c Hconcentrated Hq Hdisjoint.
  transitivity
    (expectation (pstate_measure ps)
      (fun v => c * q_eval (QIndicator gamma) v)).
  - apply expectation_extensional; intro v.
    rewrite Hq; reflexivity.
  - rewrite expectation_scale, expectation_indicator.
    rewrite (monte_carlo_concentrated_event_zero
      ps rho gamma Hconcentrated Hdisjoint).
    ring.
Qed.

Lemma monte_carlo_body_event_from_mapping :
  forall (rho gamma : CFormula) (rhit rmiss : R),
    monte_carlo_sample_invariant (monte_carlo_after_hit gamma) ->
    monte_carlo_sample_invariant (monte_carlo_after_i gamma) ->
    ((rhit = monte_carlo_hit_probability /\
       cformula_valid <{ $(rho) -> $(monte_carlo_after_hit gamma) }>) \/
     (rhit = 0%R /\
       cformula_valid
         <{ ~ ($(rho) /\ $(monte_carlo_after_hit gamma)) }>)) ->
    ((rmiss = (1 - monte_carlo_hit_probability)%R /\
       cformula_valid <{ $(rho) -> $(monte_carlo_after_i gamma) }>) \/
     (rmiss = 0%R /\
       cformula_valid
         <{ ~ ($(rho) /\ $(monte_carlo_after_i gamma)) }>)) ->
    {{ $(p_concentrated_mass rho [[ 1 ]]) }}
      $(monte_carlo_body)
    {{ $(monte_carlo_event_probability (rhit + rmiss) gamma) }}.
Proof.
  intros rho gamma rhit rmiss Hhit_invariant Hmiss_invariant
    Hhit_case Hmiss_case.
  eapply HConseq with
    (eta1 := monte_carlo_body_wp gamma rhit rmiss)
    (eta2 := monte_carlo_event_probability (rhit + rmiss) gamma).
  - rewrite monte_carlo_body_wp_shape.
    intros ps Hconcentrated.
    apply (proj2 (monte_carlo_p_and_spec _ _ _)).
    split.
    + apply (proj2 (monte_carlo_p_eq_spec _ _ _)).
      cbn [pterm_eval].
      destruct Hhit_case as [Hfull | Hzero].
      * destruct Hfull as [Heq Hsubset].
        subst rhit; symmetry.
        eapply monte_carlo_scaled_construct_full;
          [exact Hconcentrated | | exact Hsubset].
        apply monte_carlo_hit_pre_construct_eval; exact Hhit_invariant.
      * destruct Hzero as [Heq Hdisjoint].
        subst rhit; symmetry.
        eapply monte_carlo_scaled_construct_zero;
          [exact Hconcentrated | | exact Hdisjoint].
        apply monte_carlo_hit_pre_construct_eval; exact Hhit_invariant.
    + apply (proj2 (monte_carlo_p_eq_spec _ _ _)).
      cbn [pterm_eval].
      destruct Hmiss_case as [Hfull | Hzero].
      * destruct Hfull as [Heq Hsubset].
        subst rmiss; symmetry.
        eapply monte_carlo_scaled_construct_full;
          [exact Hconcentrated | | exact Hsubset].
        apply monte_carlo_miss_pre_construct_eval; exact Hmiss_invariant.
      * destruct Hzero as [Heq Hdisjoint].
        subst rmiss; symmetry.
        eapply monte_carlo_scaled_construct_zero;
          [exact Hconcentrated | | exact Hdisjoint].
        apply monte_carlo_miss_pre_construct_eval; exact Hmiss_invariant.
  - apply monte_carlo_body_event_derivable.
  - intros ps Hpost; exact Hpost.
Qed.

Lemma monte_carlo_false_concentration_valid :
  forall eta : PFormula,
    pformula_valid
      (PFImpl (p_concentrated_mass FFalse (PConst 1%R)) eta).
Proof.
  intros eta ps Hfalse.
  unfold p_concentrated_mass in Hfalse.
  apply monte_carlo_p_and_spec in Hfalse.
  destruct Hfalse as [Hconcentrated Hmass].
  apply monte_carlo_p_eq_spec in Hconcentrated.
  apply monte_carlo_p_eq_spec in Hmass.
  cbn [pterm_eval] in Hconcentrated, Hmass.
  rewrite expectation_indicator in Hconcentrated.
  rewrite expectation_indicator in Hconcentrated.
  rewrite expectation_indicator in Hmass.
  rewrite measure_empty in Hconcentrated.
  assert (Htrue :
    measure_of (pstate_measure ps) (formula_assertion c_true) =
      measure_of (pstate_measure ps) (fun _ : state => True)).
  {
    apply measure_extensional; intro v.
    unfold formula_assertion, c_true; cbn [satisfies]; tauto.
  }
  lra.
Qed.

Lemma monte_carlo_body_from_false_region :
  forall eta : PFormula,
    {{ $(p_concentrated_mass FFalse [[ 1 ]]) }}
      $(monte_carlo_body)
    {{ $(eta) }}.
Proof.
  intro eta.
  eapply HConseq with (eta1 := PFFalse) (eta2 := PFFalse).
  - apply monte_carlo_false_concentration_valid.
  - apply HFree.
    cbn [pformula_analytical]; exact I.
  - intros ps Hfalse.
    cbn [psatisfies] in Hfalse; contradiction.
Qed.

Lemma monte_carlo_inactive_region_false :
  forall M k index : nat,
    (index < monte_carlo_region_count M)%nat ->
    monte_carlo_row_active M index = false ->
    monte_carlo_region M k index = FFalse.
Proof.
  intros M k index Hindex Hinactive.
  apply monte_carlo_row_inactive_spec in Hinactive.
  destruct Hinactive as [Hslot Hnot_other].
  pose proof (monte_carlo_region_bounded_shape M k index Hindex)
    as Hshape.
  destruct Hshape as [Hexact | Hrest].
  - destruct Hexact as [Hle Heq]; lia.
  - destruct Hrest as [Hother | Hfalse].
    + destruct Hother as [Heq Hregion]; contradiction.
    + exact Hfalse.
Qed.

Lemma monte_carlo_body_region_event :
  forall M k index destination : nat,
    (index < monte_carlo_region_count M)%nat ->
    (destination < monte_carlo_region_count M)%nat ->
    {{ $(p_concentrated_mass (monte_carlo_region M k index) [[ 1 ]]) }}
      $(monte_carlo_body)
    {{ $(monte_carlo_event_probability
      (monte_carlo_transitions M index destination)
      (monte_carlo_region M k destination)) }}.
Proof.
  intros M k index destination Hindex Hdestination.
  destruct (monte_carlo_row_active M index) eqn:Hactive.
  - destruct (Nat.le_gt_cases
      (monte_carlo_region_remaining M index) 1%nat)
      as [Hrsmall | Hrmore].
    + assert (Hr_one : monte_carlo_region_remaining M index = 1%nat) by
        (pose proof (monte_carlo_region_bounded_decode M index Hindex); lia).
      assert (Htriple :
        {{ $(p_concentrated_mass (monte_carlo_region M k index) [[ 1 ]]) }}
          $(monte_carlo_body)
        {{ $(monte_carlo_event_probability (0 + 0)
          (monte_carlo_region M k destination)) }}).
      {
        apply monte_carlo_body_event_from_mapping.
        - apply monte_carlo_after_hit_sample_invariant.
          apply monte_carlo_region_sample_invariant.
        - apply monte_carlo_after_i_sample_invariant.
          apply monte_carlo_region_sample_invariant.
        - right; split; [reflexivity |].
          apply monte_carlo_final_hit_region_disjoint; assumption.
        - right; split; [reflexivity |].
          apply monte_carlo_final_miss_region_disjoint; assumption.
      }
      eapply HConseq with
        (eta1 := p_concentrated_mass (monte_carlo_region M k index)
          (PConst 1%R))
        (eta2 := monte_carlo_event_probability 0
          (monte_carlo_region M k destination)).
      * intros ps Hpre; exact Hpre.
      * eapply HConseq with
          (eta1 := p_concentrated_mass (monte_carlo_region M k index)
            (PConst 1%R))
          (eta2 := monte_carlo_event_probability (0 + 0)
            (monte_carlo_region M k destination));
          [intros ps Hpre; exact Hpre | exact Htriple |].
        unfold pformula_valid, monte_carlo_event_probability.
        intro ps; cbn [p_eq p_and p_not psatisfies pterm_eval]; lra.
      * unfold pformula_valid, monte_carlo_event_probability,
          monte_carlo_transitions.
        rewrite Hactive.
        assert (Hlt :
          (1 <? monte_carlo_region_remaining M index)%nat = false) by
          (apply Nat.ltb_ge; exact Hrsmall).
        rewrite Hlt; cbn [andb].
        intro ps; cbn [p_eq p_and p_not psatisfies pterm_eval]; lra.
    + set (rhit :=
        if (destination =? monte_carlo_hit_destination M index)%nat
        then monte_carlo_hit_probability else 0%R).
      set (rmiss :=
        if (destination =? monte_carlo_miss_destination M index)%nat
        then (1 - monte_carlo_hit_probability)%R else 0%R).
      assert (Htriple :
        {{ $(p_concentrated_mass (monte_carlo_region M k index) [[ 1 ]]) }}
          $(monte_carlo_body)
        {{ $(monte_carlo_event_probability (rhit + rmiss)
          (monte_carlo_region M k destination)) }}).
      {
        apply monte_carlo_body_event_from_mapping.
        - apply monte_carlo_after_hit_sample_invariant.
          apply monte_carlo_region_sample_invariant.
        - apply monte_carlo_after_i_sample_invariant.
          apply monte_carlo_region_sample_invariant.
        - unfold rhit.
          destruct (destination =? monte_carlo_hit_destination M index)%nat
            eqn:Heq.
          + left; split; [reflexivity |].
            apply Nat.eqb_eq in Heq; subst destination.
            apply monte_carlo_hit_maps_to_destination; assumption.
          + right; split; [reflexivity |].
            apply Nat.eqb_neq in Heq.
            apply monte_carlo_hit_non_destination_disjoint; assumption.
        - unfold rmiss.
          destruct (destination =? monte_carlo_miss_destination M index)%nat
            eqn:Heq.
          + left; split; [reflexivity |].
            apply Nat.eqb_eq in Heq; subst destination.
            apply monte_carlo_miss_maps_to_destination; assumption.
          + right; split; [reflexivity |].
            apply Nat.eqb_neq in Heq.
            apply monte_carlo_miss_non_destination_disjoint; assumption.
      }
      assert (Hlt :
        (1 <? monte_carlo_region_remaining M index)%nat = true) by
        (apply Nat.ltb_lt; exact Hrmore).
      assert (Hcoefficient :
        monte_carlo_transitions M index destination = (rhit + rmiss)%R).
      {
        unfold monte_carlo_transitions, rhit, rmiss.
        rewrite Hactive, Hlt; cbn [andb]; reflexivity.
      }
      rewrite Hcoefficient.
      exact Htriple.
  - rewrite (monte_carlo_inactive_region_false M k index Hindex Hactive).
    apply monte_carlo_body_from_false_region.
Qed.

Lemma monte_carlo_sample_invariant_not :
  forall gamma : CFormula,
    monte_carlo_sample_invariant gamma ->
    monte_carlo_sample_invariant <{ ~ $(gamma) }>.
Proof.
  intros gamma Hgamma v x y.
  unfold c_not; cbn [satisfies].
  pose proof (Hgamma v x y); tauto.
Qed.

Lemma monte_carlo_guard_sample_invariant :
  forall M : nat,
    monte_carlo_sample_invariant (monte_carlo_guard M).
Proof.
  intros M v x y.
  unfold monte_carlo_guard.
  rewrite !monte_carlo_c_and_spec.
  cbn [satisfies c_lt c_not term_eval update_real update_real_values].
  pose proof monte_carlo_variables_distinct as Hdistinct.
  destruct Hdistinct as [HXY Hdistinct].
  destruct Hdistinct as [HXi Hdistinct].
  destruct Hdistinct as [HXH Hdistinct].
  destruct Hdistinct as [HYi Hdistinct].
  destruct Hdistinct as [HYH HiH].
  destruct (real_program_var_eq_dec monte_carlo_i monte_carlo_Y);
    [congruence |].
  destruct (real_program_var_eq_dec monte_carlo_i monte_carlo_X);
    [congruence | reflexivity].
Qed.

Lemma monte_carlo_continuing_hit_not_exit :
  forall M k index : nat,
    (index < monte_carlo_region_count M)%nat ->
    monte_carlo_row_active M index = true ->
    (1 < monte_carlo_region_remaining M index)%nat ->
    cformula_valid
      <{ ~ ($(monte_carlo_region M k index) /\
             $(monte_carlo_after_hit <{ ~ $(monte_carlo_guard M) }>)) }>.
Proof.
  intros M k index Hindex Hactive Hrmore v Hboth.
  apply monte_carlo_c_and_spec in Hboth.
  destruct Hboth as [Hsource Hnotguard].
  pose proof (monte_carlo_hit_maps_to_destination
    M k index Hindex Hactive Hrmore v Hsource) as Hmapped.
  apply monte_carlo_after_hit_spec in Hmapped.
  apply monte_carlo_after_hit_spec in Hnotguard.
  unfold c_not in Hnotguard; cbn [satisfies] in Hnotguard.
  apply Hnotguard.
  pose proof (proj1 (monte_carlo_destinations_bound
    M index Hindex Hactive Hrmore)) as Hbound.
  eapply monte_carlo_regions_in_guard; [exact Hbound | exact Hmapped].
Qed.

Lemma monte_carlo_continuing_miss_not_exit :
  forall M k index : nat,
    (index < monte_carlo_region_count M)%nat ->
    monte_carlo_row_active M index = true ->
    (1 < monte_carlo_region_remaining M index)%nat ->
    cformula_valid
      <{ ~ ($(monte_carlo_region M k index) /\
             $(monte_carlo_after_i <{ ~ $(monte_carlo_guard M) }>)) }>.
Proof.
  intros M k index Hindex Hactive Hrmore v Hboth.
  apply monte_carlo_c_and_spec in Hboth.
  destruct Hboth as [Hsource Hnotguard].
  pose proof (monte_carlo_miss_maps_to_destination
    M k index Hindex Hactive Hrmore v Hsource) as Hmapped.
  apply monte_carlo_after_i_spec in Hmapped.
  apply monte_carlo_after_i_spec in Hnotguard.
  unfold c_not in Hnotguard; cbn [satisfies] in Hnotguard.
  apply Hnotguard.
  pose proof (proj2 (monte_carlo_destinations_bound
    M index Hindex Hactive Hrmore)) as Hbound.
  eapply monte_carlo_regions_in_guard; [exact Hbound | exact Hmapped].
Qed.

Lemma monte_carlo_body_termination_exit_event :
  forall M k index : nat,
    (index < monte_carlo_region_count M)%nat ->
    {{ $(p_concentrated_mass (monte_carlo_region M k index) [[ 1 ]]) }}
      $(monte_carlo_body)
    {{ $(monte_carlo_event_probability
      (monte_carlo_termination_exits M index)
      <{ ~ $(monte_carlo_guard M) }>) }}.
Proof.
  intros M k index Hindex.
  destruct (monte_carlo_row_active M index) eqn:Hactive.
  - destruct (Nat.le_gt_cases
      (monte_carlo_region_remaining M index) 1%nat)
      as [Hrsmall | Hrmore].
    + assert (Hr_one : monte_carlo_region_remaining M index = 1%nat) by
        (pose proof (monte_carlo_region_bounded_decode M index Hindex); lia).
      assert (Htriple :
        {{ $(p_concentrated_mass (monte_carlo_region M k index) [[ 1 ]]) }}
          $(monte_carlo_body)
        {{ $(monte_carlo_event_probability
          (monte_carlo_hit_probability +
            (1 - monte_carlo_hit_probability))
          <{ ~ $(monte_carlo_guard M) }>) }}).
      {
        apply monte_carlo_body_event_from_mapping.
        - apply monte_carlo_after_hit_sample_invariant.
          apply monte_carlo_sample_invariant_not.
          apply monte_carlo_guard_sample_invariant.
        - apply monte_carlo_after_i_sample_invariant.
          apply monte_carlo_sample_invariant_not.
          apply monte_carlo_guard_sample_invariant.
        - left; split; [reflexivity |].
          apply monte_carlo_final_step_not_guard_hit; assumption.
        - left; split; [reflexivity |].
          apply monte_carlo_final_step_not_guard_miss; assumption.
      }
      unfold monte_carlo_termination_exits.
      rewrite Hactive.
      assert (Hreq :
        (monte_carlo_region_remaining M index =? 1)%nat = true) by
        (apply Nat.eqb_eq; exact Hr_one).
      rewrite Hreq.
      eapply HConseq with
        (eta1 := p_concentrated_mass (monte_carlo_region M k index)
          (PConst 1%R))
        (eta2 := monte_carlo_event_probability
          (monte_carlo_hit_probability +
            (1 - monte_carlo_hit_probability))
          <{ ~ $(monte_carlo_guard M) }>).
      * intros ps Hpre; exact Hpre.
      * exact Htriple.
      * unfold pformula_valid, monte_carlo_event_probability.
        intro ps; cbn [p_eq p_and p_not psatisfies pterm_eval]; lra.
    + assert (Htriple :
        {{ $(p_concentrated_mass (monte_carlo_region M k index) [[ 1 ]]) }}
          $(monte_carlo_body)
        {{ $(monte_carlo_event_probability (0 + 0)
          <{ ~ $(monte_carlo_guard M) }>) }}).
      {
        apply monte_carlo_body_event_from_mapping.
        - apply monte_carlo_after_hit_sample_invariant.
          apply monte_carlo_sample_invariant_not.
          apply monte_carlo_guard_sample_invariant.
        - apply monte_carlo_after_i_sample_invariant.
          apply monte_carlo_sample_invariant_not.
          apply monte_carlo_guard_sample_invariant.
        - right; split; [reflexivity |].
          apply monte_carlo_continuing_hit_not_exit; assumption.
        - right; split; [reflexivity |].
          apply monte_carlo_continuing_miss_not_exit; assumption.
      }
      unfold monte_carlo_termination_exits.
      rewrite Hactive.
      assert (Hreq :
        (monte_carlo_region_remaining M index =? 1)%nat = false) by
        (apply Nat.eqb_neq; lia).
      rewrite Hreq.
      eapply HConseq with
        (eta1 := p_concentrated_mass (monte_carlo_region M k index)
          (PConst 1%R))
        (eta2 := monte_carlo_event_probability (0 + 0)
          <{ ~ $(monte_carlo_guard M) }>).
      * intros ps Hpre; exact Hpre.
      * exact Htriple.
      * unfold pformula_valid, monte_carlo_event_probability.
        intro ps; cbn [p_eq p_and p_not psatisfies pterm_eval]; lra.
  - rewrite (monte_carlo_inactive_region_false M k index Hindex Hactive).
    apply monte_carlo_body_from_false_region.
Qed.

Lemma monte_carlo_target_spec :
  forall (k : nat) (v : state),
    satisfies v (monte_carlo_target k) <->
      real_program_values v monte_carlo_H = INR k.
Proof.
  intros k v.
  unfold monte_carlo_target.
  rewrite monte_carlo_c_and_spec.
  cbn [satisfies term_eval].
  split.
  - intros [Hle Hge]; lra.
  - intro Heq; split; lra.
Qed.

Lemma monte_carlo_not_target_spec :
  forall (k : nat) (v : state),
    satisfies v (monte_carlo_not_target k) <->
      real_program_values v monte_carlo_H <> INR k.
Proof.
  intros k v.
  unfold monte_carlo_not_target, c_not.
  cbn [satisfies].
  rewrite monte_carlo_target_spec.
  tauto.
Qed.

Definition monte_carlo_complement_exit_event (M k : nat) : CFormula :=
  <{ $(monte_carlo_not_target k) /\ ~ $(monte_carlo_guard M) }>.

Lemma monte_carlo_sample_invariant_and :
  forall gamma delta : CFormula,
    monte_carlo_sample_invariant gamma ->
    monte_carlo_sample_invariant delta ->
    monte_carlo_sample_invariant <{ $(gamma) /\ $(delta) }>.
Proof.
  intros gamma delta Hgamma Hdelta v x y.
  rewrite !monte_carlo_c_and_spec.
  pose proof (Hgamma v x y).
  pose proof (Hdelta v x y).
  tauto.
Qed.

Lemma monte_carlo_not_target_sample_invariant :
  forall k : nat,
    monte_carlo_sample_invariant (monte_carlo_not_target k).
Proof.
  intros k v x y.
  rewrite !monte_carlo_not_target_spec.
  cbn [update_real update_real_values].
  pose proof monte_carlo_variables_distinct as Hdistinct.
  destruct Hdistinct as [HXY Hdistinct].
  destruct Hdistinct as [HXi Hdistinct].
  destruct Hdistinct as [HXH Hdistinct].
  destruct Hdistinct as [HYi Hdistinct].
  destruct Hdistinct as [HYH HiH].
  destruct (real_program_var_eq_dec monte_carlo_H monte_carlo_Y);
    [congruence |].
  destruct (real_program_var_eq_dec monte_carlo_H monte_carlo_X);
    [congruence | reflexivity].
Qed.

Lemma monte_carlo_complement_exit_sample_invariant :
  forall M k : nat,
    monte_carlo_sample_invariant (monte_carlo_complement_exit_event M k).
Proof.
  intros M k.
  unfold monte_carlo_complement_exit_event.
  apply monte_carlo_sample_invariant_and.
  - apply monte_carlo_not_target_sample_invariant.
  - apply monte_carlo_sample_invariant_not.
    apply monte_carlo_guard_sample_invariant.
Qed.

Lemma monte_carlo_final_hit_complement_full :
  forall M k index : nat,
    (index < monte_carlo_region_count M)%nat ->
    monte_carlo_row_active M index = true ->
    monte_carlo_region_remaining M index = 1%nat ->
    (monte_carlo_region_slot M index = 0%nat \/
      monte_carlo_region_slot M index = S M) ->
    cformula_valid
      <{ $(monte_carlo_region M k index) ->
         $(monte_carlo_after_hit
           (monte_carlo_complement_exit_event M k)) }>.
Proof.
  intros M k index Hindex Hactive Hr_one Hslot_case v Hsource.
  pose proof (monte_carlo_final_step_not_guard_hit
    M k index Hindex Hactive Hr_one v Hsource) as Hnotguard.
  apply monte_carlo_after_hit_spec.
  unfold monte_carlo_complement_exit_event.
  apply monte_carlo_c_and_spec.
  split.
  - apply monte_carlo_not_target_spec.
    rewrite monte_carlo_hit_state_H.
    pose proof (monte_carlo_region_bounded_shape M k index Hindex)
      as Hshape.
    destruct Hslot_case as [Hslot_zero | Hslot_other].
    + destruct Hshape as [Hexact | Hrest].
      * destruct Hexact as [Hsr Hregion].
        rewrite Hregion in Hsource.
        apply monte_carlo_exact_region_spec in Hsource.
        rewrite Hslot_zero in Hsource.
        cbn [INR] in Hsource.
        lra.
      * destruct Hrest as [Hother | Hfalse].
        -- destruct Hother as [Hother_slot Hregion]; lia.
        -- rewrite Hfalse in Hsource; cbn [satisfies] in Hsource; contradiction.
    + destruct Hshape as [Hexact | Hrest].
      * destruct Hexact as [Hsr Hregion].
        pose proof (monte_carlo_region_bounded_decode M index Hindex)
          as [Hr Hs].
        unfold monte_carlo_block_width in *; lia.
      * destruct Hrest as [Hother | Hfalse].
        -- destruct Hother as [Hother_slot Hregion].
           rewrite Hregion in Hsource.
           unfold monte_carlo_other_region in Hsource.
           apply monte_carlo_c_and_spec in Hsource.
           destruct Hsource as [Hband Hnot_exact].
           rewrite Hr_one in Hnot_exact.
           unfold c_not in Hnot_exact; cbn [satisfies] in Hnot_exact.
           intro Heq.
           apply Hnot_exact.
           apply monte_carlo_finite_c_or_spec.
           exists 1%nat; split; [lia |].
           apply monte_carlo_exact_region_spec.
           split; [rewrite Hr_one in Hband; exact Hband |].
           rewrite S_INR; cbn [INR].
           lra.
        -- rewrite Hfalse in Hsource; cbn [satisfies] in Hsource; contradiction.
  - apply monte_carlo_after_hit_spec in Hnotguard; exact Hnotguard.
Qed.

Lemma monte_carlo_final_hit_complement_zero :
  forall M k index : nat,
    (index < monte_carlo_region_count M)%nat ->
    monte_carlo_row_active M index = true ->
    monte_carlo_region_remaining M index = 1%nat ->
    monte_carlo_region_slot M index = 1%nat ->
    cformula_valid
      <{ ~ ($(monte_carlo_region M k index) /\
             $(monte_carlo_after_hit
               (monte_carlo_complement_exit_event M k))) }>.
Proof.
  intros M k index Hindex Hactive Hr_one Hslot v Hboth.
  apply monte_carlo_c_and_spec in Hboth.
  destruct Hboth as [Hsource Hexit].
  apply monte_carlo_after_hit_spec in Hexit.
  unfold monte_carlo_complement_exit_event in Hexit.
  apply monte_carlo_c_and_spec in Hexit.
  destruct Hexit as [Hexit Hexit_guard].
  apply monte_carlo_not_target_spec in Hexit.
  rewrite monte_carlo_hit_state_H in Hexit.
  pose proof (monte_carlo_region_bounded_shape M k index Hindex)
    as Hshape.
  destruct Hshape as [Hexact | Hrest].
  - destruct Hexact as [Hsr Hregion].
    rewrite Hregion in Hsource.
    apply monte_carlo_exact_region_spec in Hsource.
    rewrite Hslot in Hsource.
    rewrite S_INR in Hsource.
    cbn [INR] in Hsource.
    apply Hexit; lra.
  - destruct Hrest as [Hother | Hfalse].
    + destruct Hother as [Hother_slot Hregion].
      pose proof (monte_carlo_region_bounded_decode M index Hindex)
        as [Hr Hs].
      unfold monte_carlo_block_width in *; lia.
    + rewrite Hfalse in Hsource; cbn [satisfies] in Hsource; contradiction.
Qed.

Lemma monte_carlo_final_miss_complement_full :
  forall M k index : nat,
    (index < monte_carlo_region_count M)%nat ->
    monte_carlo_row_active M index = true ->
    monte_carlo_region_remaining M index = 1%nat ->
    (monte_carlo_region_slot M index = 1%nat \/
      monte_carlo_region_slot M index = S M) ->
    cformula_valid
      <{ $(monte_carlo_region M k index) ->
         $(monte_carlo_after_i
           (monte_carlo_complement_exit_event M k)) }>.
Proof.
  intros M k index Hindex Hactive Hr_one Hslot_case v Hsource.
  pose proof (monte_carlo_final_step_not_guard_miss
    M k index Hindex Hactive Hr_one v Hsource) as Hnotguard.
  apply monte_carlo_after_i_spec.
  unfold monte_carlo_complement_exit_event.
  apply monte_carlo_c_and_spec.
  split.
  - apply monte_carlo_not_target_spec.
    rewrite monte_carlo_miss_state_H.
    pose proof (monte_carlo_region_bounded_shape M k index Hindex)
      as Hshape.
    destruct Hslot_case as [Hslot_one | Hslot_other].
    + destruct Hshape as [Hexact | Hrest].
      * destruct Hexact as [Hsr Hregion].
        rewrite Hregion in Hsource.
        apply monte_carlo_exact_region_spec in Hsource.
        rewrite Hslot_one in Hsource.
        rewrite S_INR in Hsource.
        cbn [INR] in Hsource.
        intro Heq; lra.
      * destruct Hrest as [Hother | Hfalse].
        -- destruct Hother as [Hother_slot Hregion].
           pose proof (monte_carlo_region_bounded_decode M index Hindex)
             as [Hr Hs].
           unfold monte_carlo_block_width in *; lia.
        -- rewrite Hfalse in Hsource; cbn [satisfies] in Hsource; contradiction.
    + destruct Hshape as [Hexact | Hrest].
      * destruct Hexact as [Hsr Hregion].
        pose proof (monte_carlo_region_bounded_decode M index Hindex)
          as [Hr Hs].
        unfold monte_carlo_block_width in *; lia.
      * destruct Hrest as [Hother | Hfalse].
        -- destruct Hother as [Hother_slot Hregion].
           rewrite Hregion in Hsource.
           unfold monte_carlo_other_region in Hsource.
           apply monte_carlo_c_and_spec in Hsource.
           destruct Hsource as [Hband Hnot_exact].
           rewrite Hr_one in Hnot_exact.
           unfold c_not in Hnot_exact; cbn [satisfies] in Hnot_exact.
           intro Heq.
           apply Hnot_exact.
           apply monte_carlo_finite_c_or_spec.
           exists 0%nat; split; [lia |].
           apply monte_carlo_exact_region_spec.
           split; [rewrite Hr_one in Hband; exact Hband |].
           cbn [INR]; lra.
        -- rewrite Hfalse in Hsource; cbn [satisfies] in Hsource; contradiction.
  - apply monte_carlo_after_i_spec in Hnotguard; exact Hnotguard.
Qed.

Lemma monte_carlo_final_miss_complement_zero :
  forall M k index : nat,
    (index < monte_carlo_region_count M)%nat ->
    monte_carlo_row_active M index = true ->
    monte_carlo_region_remaining M index = 1%nat ->
    monte_carlo_region_slot M index = 0%nat ->
    cformula_valid
      <{ ~ ($(monte_carlo_region M k index) /\
             $(monte_carlo_after_i
               (monte_carlo_complement_exit_event M k))) }>.
Proof.
  intros M k index Hindex Hactive Hr_one Hslot v Hboth.
  apply monte_carlo_c_and_spec in Hboth.
  destruct Hboth as [Hsource Hexit].
  apply monte_carlo_after_i_spec in Hexit.
  unfold monte_carlo_complement_exit_event in Hexit.
  apply monte_carlo_c_and_spec in Hexit.
  destruct Hexit as [Hexit Hexit_guard].
  apply monte_carlo_not_target_spec in Hexit.
  rewrite monte_carlo_miss_state_H in Hexit.
  pose proof (monte_carlo_region_bounded_shape M k index Hindex)
    as Hshape.
  destruct Hshape as [Hexact | Hrest].
  - destruct Hexact as [Hsr Hregion].
    rewrite Hregion in Hsource.
    apply monte_carlo_exact_region_spec in Hsource.
    rewrite Hslot in Hsource.
    cbn [INR] in Hsource.
    apply Hexit; lra.
  - destruct Hrest as [Hother | Hfalse].
    + destruct Hother as [Hother_slot Hregion]; lia.
    + rewrite Hfalse in Hsource; cbn [satisfies] in Hsource; contradiction.
Qed.

Lemma monte_carlo_continuing_hit_not_complement_exit :
  forall M k index : nat,
    (index < monte_carlo_region_count M)%nat ->
    monte_carlo_row_active M index = true ->
    (1 < monte_carlo_region_remaining M index)%nat ->
    cformula_valid
      <{ ~ ($(monte_carlo_region M k index) /\
             $(monte_carlo_after_hit
               (monte_carlo_complement_exit_event M k))) }>.
Proof.
  intros M k index Hindex Hactive Hrmore v Hboth.
  apply monte_carlo_c_and_spec in Hboth.
  destruct Hboth as [Hsource Hexit].
  eapply (monte_carlo_continuing_hit_not_exit
    M k index Hindex Hactive Hrmore v).
  apply monte_carlo_c_and_spec.
  split; [exact Hsource |].
  apply monte_carlo_after_hit_spec.
  apply monte_carlo_after_hit_spec in Hexit.
  unfold monte_carlo_complement_exit_event in Hexit.
  apply monte_carlo_c_and_spec in Hexit.
  exact (proj2 Hexit).
Qed.

Lemma monte_carlo_continuing_miss_not_complement_exit :
  forall M k index : nat,
    (index < monte_carlo_region_count M)%nat ->
    monte_carlo_row_active M index = true ->
    (1 < monte_carlo_region_remaining M index)%nat ->
    cformula_valid
      <{ ~ ($(monte_carlo_region M k index) /\
             $(monte_carlo_after_i
               (monte_carlo_complement_exit_event M k))) }>.
Proof.
  intros M k index Hindex Hactive Hrmore v Hboth.
  apply monte_carlo_c_and_spec in Hboth.
  destruct Hboth as [Hsource Hexit].
  eapply (monte_carlo_continuing_miss_not_exit
    M k index Hindex Hactive Hrmore v).
  apply monte_carlo_c_and_spec.
  split; [exact Hsource |].
  apply monte_carlo_after_i_spec.
  apply monte_carlo_after_i_spec in Hexit.
  unfold monte_carlo_complement_exit_event in Hexit.
  apply monte_carlo_c_and_spec in Hexit.
  exact (proj2 Hexit).
Qed.

Lemma monte_carlo_body_complement_exit_event :
  forall M k index : nat,
    (index < monte_carlo_region_count M)%nat ->
    {{ $(p_concentrated_mass (monte_carlo_region M k index) [[ 1 ]]) }}
      $(monte_carlo_body)
    {{ $(monte_carlo_event_probability
      (monte_carlo_complement_exits M index)
      (monte_carlo_complement_exit_event M k)) }}.
Proof.
  intros M k index Hindex.
  destruct (monte_carlo_row_active M index) eqn:Hactive.
  - apply monte_carlo_row_active_spec in Hactive as Hactive_spec.
    assert (Hactive_eq : monte_carlo_row_active M index = true) by
      (apply (proj2 (monte_carlo_row_active_spec M index)); exact Hactive_spec).
    destruct (Nat.le_gt_cases
      (monte_carlo_region_remaining M index) 1%nat)
      as [Hrsmall | Hrmore].
    + pose proof (monte_carlo_region_bounded_decode M index Hindex)
        as [Hr Hs].
      assert (Hr_one : monte_carlo_region_remaining M index = 1%nat) by lia.
      destruct Hactive_spec as [Hsr | Hother].
      * destruct (monte_carlo_region_slot M index) as [|s] eqn:Hslot.
        -- assert (Htriple :
             {{ $(p_concentrated_mass
               (monte_carlo_region M k index) [[ 1 ]]) }}
               $(monte_carlo_body)
             {{ $(monte_carlo_event_probability
               (monte_carlo_hit_probability + 0)
               (monte_carlo_complement_exit_event M k)) }}).
           {
             apply monte_carlo_body_event_from_mapping.
             - apply monte_carlo_after_hit_sample_invariant.
               apply monte_carlo_complement_exit_sample_invariant.
             - apply monte_carlo_after_i_sample_invariant.
               apply monte_carlo_complement_exit_sample_invariant.
             - left; split; [reflexivity |].
               apply monte_carlo_final_hit_complement_full;
                 try assumption; left; exact Hslot.
             - right; split; [reflexivity |].
               apply monte_carlo_final_miss_complement_zero;
                 try assumption; exact Hslot.
           }
           unfold monte_carlo_complement_exits.
           rewrite Hactive_eq.
           assert (Hreq :
             (monte_carlo_region_remaining M index =? 1)%nat = true) by
             (apply Nat.eqb_eq; exact Hr_one).
           rewrite Hreq.
           assert (Hnot_other :
             (monte_carlo_region_slot M index =? S M)%nat = false) by
             (apply Nat.eqb_neq; unfold monte_carlo_block_width in Hs; lia).
           rewrite Hnot_other, Hslot, Nat.eqb_refl.
           eapply HConseq with
             (eta1 := p_concentrated_mass (monte_carlo_region M k index)
               (PConst 1%R))
             (eta2 := monte_carlo_event_probability
               (monte_carlo_hit_probability + 0)
               (monte_carlo_complement_exit_event M k));
             [intros ps Hpre; exact Hpre | exact Htriple |].
           unfold pformula_valid, monte_carlo_event_probability.
           intro ps; cbn [p_eq p_and p_not psatisfies pterm_eval]; lra.
        -- assert (s = 0)%nat by lia; subst s.
           assert (Hslot_one : monte_carlo_region_slot M index = 1%nat)
             by exact Hslot.
           assert (Htriple :
             {{ $(p_concentrated_mass
               (monte_carlo_region M k index) [[ 1 ]]) }}
               $(monte_carlo_body)
             {{ $(monte_carlo_event_probability
               (0 + (1 - monte_carlo_hit_probability))
               (monte_carlo_complement_exit_event M k)) }}).
           {
             apply monte_carlo_body_event_from_mapping.
             - apply monte_carlo_after_hit_sample_invariant.
               apply monte_carlo_complement_exit_sample_invariant.
             - apply monte_carlo_after_i_sample_invariant.
               apply monte_carlo_complement_exit_sample_invariant.
             - right; split; [reflexivity |].
               apply monte_carlo_final_hit_complement_zero; assumption.
             - left; split; [reflexivity |].
               apply monte_carlo_final_miss_complement_full;
                 try assumption; left; exact Hslot_one.
           }
           unfold monte_carlo_complement_exits.
           rewrite Hactive_eq.
           assert (Hreq :
             (monte_carlo_region_remaining M index =? 1)%nat = true) by
             (apply Nat.eqb_eq; exact Hr_one).
           rewrite Hreq.
           assert (Hnot_other :
             (monte_carlo_region_slot M index =? S M)%nat = false) by
             (apply Nat.eqb_neq; unfold monte_carlo_block_width in Hs; lia).
           rewrite Hnot_other.
           assert (Hnot_zero :
             (monte_carlo_region_slot M index =? 0)%nat = false) by
             (apply Nat.eqb_neq; lia).
           rewrite Hnot_zero.
           eapply HConseq with
             (eta1 := p_concentrated_mass (monte_carlo_region M k index)
               (PConst 1%R))
             (eta2 := monte_carlo_event_probability
               (0 + (1 - monte_carlo_hit_probability))
               (monte_carlo_complement_exit_event M k));
             [intros ps Hpre; exact Hpre | exact Htriple |].
           unfold pformula_valid, monte_carlo_event_probability.
           intro ps; cbn [p_eq p_and p_not psatisfies pterm_eval]; lra.
      * assert (Htriple :
          {{ $(p_concentrated_mass
            (monte_carlo_region M k index) [[ 1 ]]) }}
            $(monte_carlo_body)
          {{ $(monte_carlo_event_probability
            (monte_carlo_hit_probability +
              (1 - monte_carlo_hit_probability))
            (monte_carlo_complement_exit_event M k)) }}).
        {
          apply monte_carlo_body_event_from_mapping.
          - apply monte_carlo_after_hit_sample_invariant.
            apply monte_carlo_complement_exit_sample_invariant.
          - apply monte_carlo_after_i_sample_invariant.
            apply monte_carlo_complement_exit_sample_invariant.
          - left; split; [reflexivity |].
            apply monte_carlo_final_hit_complement_full;
              try assumption; right; exact Hother.
          - left; split; [reflexivity |].
            apply monte_carlo_final_miss_complement_full;
              try assumption; right; exact Hother.
        }
        unfold monte_carlo_complement_exits.
        rewrite Hactive_eq.
        assert (Hreq :
          (monte_carlo_region_remaining M index =? 1)%nat = true) by
          (apply Nat.eqb_eq; exact Hr_one).
        rewrite Hreq, Hother, Nat.eqb_refl.
        eapply HConseq with
          (eta1 := p_concentrated_mass (monte_carlo_region M k index)
            (PConst 1%R))
          (eta2 := monte_carlo_event_probability
            (monte_carlo_hit_probability +
              (1 - monte_carlo_hit_probability))
            (monte_carlo_complement_exit_event M k));
          [intros ps Hpre; exact Hpre | exact Htriple |].
        unfold pformula_valid, monte_carlo_event_probability.
        intro ps; cbn [p_eq p_and p_not psatisfies pterm_eval]; lra.
    + assert (Htriple :
        {{ $(p_concentrated_mass
          (monte_carlo_region M k index) [[ 1 ]]) }}
          $(monte_carlo_body)
        {{ $(monte_carlo_event_probability (0 + 0)
          (monte_carlo_complement_exit_event M k)) }}).
      {
        apply monte_carlo_body_event_from_mapping.
        - apply monte_carlo_after_hit_sample_invariant.
          apply monte_carlo_complement_exit_sample_invariant.
        - apply monte_carlo_after_i_sample_invariant.
          apply monte_carlo_complement_exit_sample_invariant.
        - right; split; [reflexivity |].
          apply monte_carlo_continuing_hit_not_complement_exit; assumption.
        - right; split; [reflexivity |].
          apply monte_carlo_continuing_miss_not_complement_exit; assumption.
      }
      unfold monte_carlo_complement_exits.
      rewrite Hactive_eq.
      assert (Hreq :
        (monte_carlo_region_remaining M index =? 1)%nat = false) by
        (apply Nat.eqb_neq; lia).
      rewrite Hreq.
      eapply HConseq with
        (eta1 := p_concentrated_mass (monte_carlo_region M k index)
          (PConst 1%R))
        (eta2 := monte_carlo_event_probability (0 + 0)
          (monte_carlo_complement_exit_event M k));
        [intros ps Hpre; exact Hpre | exact Htriple |].
      unfold pformula_valid, monte_carlo_event_probability.
      intro ps; cbn [p_eq p_and p_not psatisfies pterm_eval]; lra.
  - rewrite (monte_carlo_inactive_region_false M k index Hindex Hactive).
    apply monte_carlo_body_from_false_region.
Qed.

Lemma monte_carlo_event_probability_symmetric :
  forall (r : R) (gamma : CFormula),
    pformula_valid
      (PFImpl (monte_carlo_event_probability r gamma)
        (p_eq (PExpect (QIndicator gamma)) (PConst r))).
Proof.
  intros r gamma ps Hprobability.
  unfold monte_carlo_event_probability in Hprobability.
  apply monte_carlo_p_eq_spec in Hprobability.
  apply monte_carlo_p_eq_spec.
  cbn [pterm_eval] in *; lra.
Qed.

Lemma monte_carlo_finite_event_conjunction :
  forall (pre : PFormula) (body : Cmd) (m : nat)
    (regions : nat -> CFormula) (probabilities : nat -> R),
    (forall j : nat,
      (j < m)%nat ->
      {{ $(pre) }} $(body)
      {{ $(monte_carlo_event_probability (probabilities j) (regions j)) }}) ->
    {{ $(pre) }} $(body)
    {{ $(finite_p_and m
      (fun j => p_eq (PExpect (QIndicator (regions j)))
        (PConst (probabilities j)))) }}.
Proof.
  intros pre body m.
  induction m as [|m IH]; intros regions probabilities Hevents.
  - cbn [finite_p_and].
    eapply HConseq with (eta1 := p_true) (eta2 := p_true).
    + intros ps Hpre; cbn [p_true psatisfies]; tauto.
    + apply HFree.
      cbn [p_true pformula_analytical pterm_analytical]; tauto.
    + intros ps Htrue; exact Htrue.
  - cbn [finite_p_and].
    apply HAnd.
    + apply IH.
      intros j Hj; apply Hevents; lia.
    + eapply HConseq with
        (eta1 := pre)
        (eta2 := monte_carlo_event_probability (probabilities m) (regions m)).
      * intros ps Hpre; exact Hpre.
      * apply Hevents; lia.
      * apply monte_carlo_event_probability_symmetric.
Qed.

Lemma monte_carlo_termination_condition_expectation :
  forall (M : nat) (ps : Pstate),
    pterm_eval
      (PExpect (condition_pconstruct (QIndicator c_true)
        <{ ~ $(monte_carlo_guard M) }>)) ps =
    pterm_eval (PExpect (QIndicator <{ ~ $(monte_carlo_guard M) }>)) ps.
Proof.
  intros M ps.
  cbn [pterm_eval condition_pconstruct condition_pconstruct_fuel].
  rewrite !expectation_indicator.
  apply measure_extensional.
  intro v; unfold formula_assertion.
  rewrite monte_carlo_c_and_spec.
  cbn [c_true satisfies].
  tauto.
Qed.

Lemma monte_carlo_complement_condition_shape :
  forall M k : nat,
    condition_pconstruct (QIndicator (monte_carlo_not_target k))
      <{ ~ $(monte_carlo_guard M) }> =
    QIndicator (monte_carlo_complement_exit_event M k).
Proof.
  intros M k.
  unfold monte_carlo_complement_exit_event.
  reflexivity.
Qed.

Lemma monte_carlo_termination_body_post :
  forall M k index : nat,
    (index < monte_carlo_region_count M)%nat ->
    {{ $(p_concentrated_mass (monte_carlo_region M k index) [[ 1 ]]) }}
      $(monte_carlo_body)
    {{ $(while_body_post (monte_carlo_region_count M)
      (monte_carlo_region M k) (monte_carlo_transitions M index)
      (monte_carlo_guard M) (QIndicator c_true)
      (monte_carlo_termination_exits M index)) }}.
Proof.
  intros M k index Hindex.
  unfold while_body_post.
  apply HAnd.
  - apply monte_carlo_finite_event_conjunction.
    intros destination Hdestination.
    apply monte_carlo_body_region_event; assumption.
  - eapply HConseq with
      (eta1 := p_concentrated_mass (monte_carlo_region M k index)
        (PConst 1%R))
      (eta2 := monte_carlo_event_probability
        (monte_carlo_termination_exits M index)
        <{ ~ $(monte_carlo_guard M) }>).
    + intros ps Hpre; exact Hpre.
    + apply monte_carlo_body_termination_exit_event; exact Hindex.
    + intros ps Hprobability.
      apply monte_carlo_p_eq_spec.
      unfold monte_carlo_event_probability in Hprobability.
      apply monte_carlo_p_eq_spec in Hprobability.
      pose proof (monte_carlo_termination_condition_expectation M ps)
        as Hcondition.
      cbn [pterm_eval] in Hprobability |- *.
      cbn [pterm_eval] in Hcondition.
      rewrite Hcondition.
      lra.
Qed.

Lemma monte_carlo_complement_body_post :
  forall M k index : nat,
    (index < monte_carlo_region_count M)%nat ->
    {{ $(p_concentrated_mass (monte_carlo_region M k index) [[ 1 ]]) }}
      $(monte_carlo_body)
    {{ $(while_body_post (monte_carlo_region_count M)
      (monte_carlo_region M k) (monte_carlo_transitions M index)
      (monte_carlo_guard M) (QIndicator (monte_carlo_not_target k))
      (monte_carlo_complement_exits M index)) }}.
Proof.
  intros M k index Hindex.
  unfold while_body_post.
  apply HAnd.
  - apply monte_carlo_finite_event_conjunction.
    intros destination Hdestination.
    apply monte_carlo_body_region_event; assumption.
  - rewrite monte_carlo_complement_condition_shape.
    eapply HConseq with
      (eta1 := p_concentrated_mass (monte_carlo_region M k index)
        (PConst 1%R))
      (eta2 := monte_carlo_event_probability
        (monte_carlo_complement_exits M index)
        (monte_carlo_complement_exit_event M k)).
    + intros ps Hpre; exact Hpre.
    + apply monte_carlo_body_complement_exit_event; exact Hindex.
    + apply monte_carlo_event_probability_symmetric.
Qed.

Definition monte_carlo_initial_region_index (M k : nat) : nat :=
  monte_carlo_region_index M M k.

Lemma monte_carlo_initial_region_bound :
  forall M k : nat,
    (0 < M)%nat -> (k <= M)%nat ->
    (monte_carlo_initial_region_index M k <
      monte_carlo_region_count M)%nat.
Proof.
  intros M k HM Hk.
  unfold monte_carlo_initial_region_index.
  apply monte_carlo_region_index_bound.
  - lia.
  - unfold monte_carlo_block_width; lia.
Qed.

Lemma monte_carlo_initial_region_shape :
  forall M k : nat,
    (0 < M)%nat -> (k <= M)%nat ->
    monte_carlo_region M k (monte_carlo_initial_region_index M k) =
      monte_carlo_exact_region M k M k.
Proof.
  intros M k HM Hk.
  unfold monte_carlo_initial_region_index.
  apply monte_carlo_region_index_exact; lia.
Qed.

Definition monte_carlo_loop_mass : ProbLogicVar :=
  prob_logic_var "mc_loop_mass".

Theorem monte_carlo_positive_termination_loop_raw :
  forall M k : nat,
    (0 < M)%nat -> (k <= M)%nat ->
    {{ $(p_concentrated_mass
      (monte_carlo_region M k (monte_carlo_initial_region_index M k))
      (PVar monte_carlo_loop_mass)) }}
      while $(monte_carlo_guard M) do $(monte_carlo_body) end
    {{
      E[$(condition_pconstruct (QIndicator c_true)
        <{ ~ $(monte_carlo_guard M) }>)] =
      $(monte_carlo_termination_solution
        (monte_carlo_initial_region_index M k)) * monte_carlo_loop_mass
    }}.
Proof.
  intros M k HM Hk.
  eapply HWhile with
    (m := monte_carlo_region_count M)
    (k := monte_carlo_initial_region_index M k)
    (regions := monte_carlo_region M k)
    (solution := monte_carlo_termination_solution)
    (exits := monte_carlo_termination_exits M)
    (transitions := monte_carlo_transitions M).
  - apply monte_carlo_initial_region_bound; assumption.
  - apply monte_carlo_regions_cover.
  - apply monte_carlo_regions_in_guard.
  - apply monte_carlo_regions_disjoint.
  - apply monte_carlo_progress.
  - intros index Hindex.
    apply monte_carlo_termination_body_post; exact Hindex.
  - apply monte_carlo_termination_solution_correct.
Qed.

Theorem monte_carlo_positive_complement_loop_raw :
  forall M k : nat,
    (0 < M)%nat -> (k <= M)%nat ->
    {{ $(p_concentrated_mass
      (monte_carlo_region M k (monte_carlo_initial_region_index M k))
      (PVar monte_carlo_loop_mass)) }}
      while $(monte_carlo_guard M) do $(monte_carlo_body) end
    {{
      E[$(condition_pconstruct (QIndicator (monte_carlo_not_target k))
        <{ ~ $(monte_carlo_guard M) }>)] =
      $(monte_carlo_complement_solution M
        (monte_carlo_initial_region_index M k)) * monte_carlo_loop_mass
    }}.
Proof.
  intros M k HM Hk.
  eapply HWhile with
    (m := monte_carlo_region_count M)
    (k := monte_carlo_initial_region_index M k)
    (regions := monte_carlo_region M k)
    (solution := monte_carlo_complement_solution M)
    (exits := monte_carlo_complement_exits M)
    (transitions := monte_carlo_transitions M).
  - apply monte_carlo_initial_region_bound; assumption.
  - apply monte_carlo_regions_cover.
  - apply monte_carlo_regions_in_guard.
  - apply monte_carlo_regions_disjoint.
  - apply monte_carlo_complement_progress.
  - intros index Hindex.
    apply monte_carlo_complement_body_post; exact Hindex.
  - apply monte_carlo_complement_solution_correct.
Qed.

Lemma monte_carlo_eliminate_unit_mass :
  forall (gamma : CFormula) (command : Cmd) (q : PConstruct) (c : R),
    {{ $(p_concentrated_mass gamma (PVar monte_carlo_loop_mass)) }}
      $(command)
    {{ E[$(q)] = $(c) * monte_carlo_loop_mass }} ->
    {{ $(p_concentrated_mass gamma [[ 1 ]]) }}
      $(command)
    {{ E[$(q)] = $(c) }}.
Proof.
  intros gamma command q c Hderivation.
  set (eta := p_concentrated_mass gamma (PVar monte_carlo_loop_mass)).
  set (rigid := [[ monte_carlo_loop_mass = 1 ]]).
  set (desired := [[ E[$(q)] = $(c) ]]).
  assert (Hevent :
    {{ $(eta) /\ $(rigid) }} $(command)
    {{ E[$(q)] = $(c) * monte_carlo_loop_mass }}).
  {
    eapply HConseq with (eta1 := eta)
      (eta2 := [[ E[$(q)] = $(c) * monte_carlo_loop_mass ]]).
    - intros ps Hpre.
      apply monte_carlo_p_and_spec in Hpre; exact (proj1 Hpre).
    - exact Hderivation.
    - intros ps Hpost; exact Hpost.
  }
  assert (Hrigid :
    {{ $(eta) /\ $(rigid) }} $(command) {{ $(rigid) }}).
  {
    eapply HConseq with (eta1 := rigid) (eta2 := rigid).
    - intros ps Hpre.
      apply monte_carlo_p_and_spec in Hpre; exact (proj2 Hpre).
    - apply HFree.
      unfold rigid.
      cbn [p_eq p_and p_not pformula_analytical pterm_analytical]; tauto.
    - intros ps Hpost; exact Hpost.
  }
  assert (Hdesired :
    {{ $(eta) /\ $(rigid) }} $(command) {{ $(desired) }}).
  {
    eapply HConseq with
      (eta1 := [[ $(eta) /\ $(rigid) ]])
      (eta2 := [[
        (E[$(q)] = $(c) * monte_carlo_loop_mass) /\ $(rigid)
      ]]).
    - intros ps Hpre; exact Hpre.
    - apply HAnd; assumption.
    - unfold desired, rigid.
      intros ps Hpost.
      apply monte_carlo_p_and_spec in Hpost.
      destruct Hpost as [Hvalue Hmass].
      apply monte_carlo_p_eq_spec.
      apply monte_carlo_p_eq_spec in Hvalue.
      apply monte_carlo_p_eq_spec in Hmass.
      cbn [pterm_eval] in *; nra.
  }
  eapply HElimv with (eta1 := eta)
    (y := monte_carlo_loop_mass) (p := PConst 1%R).
  - change
      ({{ $(eta) /\ $(rigid) }} $(command) {{ $(desired) }}).
    exact Hdesired.
  - cbn [prob_logic_var_occurs_pterm]; tauto.
  - unfold desired.
    cbn [p_eq p_and p_not prob_logic_var_occurs_pformula
      prob_logic_var_occurs_pterm]; tauto.
Qed.

Lemma monte_carlo_initial_complement_solution :
  forall M k : nat,
    (0 < M)%nat -> (k <= M)%nat ->
    monte_carlo_complement_solution M
      (monte_carlo_initial_region_index M k) =
      (1 - monte_carlo_bernoulli_mass M k)%R.
Proof.
  intros M k HM Hk.
  unfold monte_carlo_complement_solution, monte_carlo_initial_region_index.
  pose proof (monte_carlo_region_decode_index M M k)
    as Hdecode.
  specialize (Hdecode ltac:(lia) ltac:(unfold monte_carlo_block_width; lia)).
  destruct Hdecode as [Hremaining Hslot].
  rewrite Hremaining, Hslot.
  assert (Hleb : (k <=? M)%nat = true) by
    (apply Nat.leb_le; exact Hk).
  rewrite Hleb; reflexivity.
Qed.

Theorem monte_carlo_positive_termination_loop :
  forall M k : nat,
    (0 < M)%nat -> (k <= M)%nat ->
    {{ $(p_concentrated_mass
      (monte_carlo_region M k (monte_carlo_initial_region_index M k))
      [[ 1 ]]) }}
      while $(monte_carlo_guard M) do $(monte_carlo_body) end
    {{ Pr[~ $(monte_carlo_guard M)] = 1 }}.
Proof.
  intros M k HM Hk.
  assert (Hraw := monte_carlo_positive_termination_loop_raw M k HM Hk).
  unfold monte_carlo_termination_solution in Hraw.
  pose proof (monte_carlo_eliminate_unit_mass
    (monte_carlo_region M k (monte_carlo_initial_region_index M k))
    <{ while $(monte_carlo_guard M) do $(monte_carlo_body) end }>
    (condition_pconstruct (QIndicator c_true)
      <{ ~ $(monte_carlo_guard M) }>) 1 Hraw) as Hunit.
  eapply HConseq with
    (eta1 := p_concentrated_mass
      (monte_carlo_region M k (monte_carlo_initial_region_index M k))
      (PConst 1%R))
    (eta2 := [[
      E[$(condition_pconstruct (QIndicator c_true)
        <{ ~ $(monte_carlo_guard M) }>)] = 1
    ]]).
  - intros ps Hpre; exact Hpre.
  - exact Hunit.
  - intros ps Hpost.
    apply monte_carlo_p_eq_spec in Hpost.
    apply monte_carlo_p_eq_spec.
    cbn [pterm_eval] in Hpost |- *.
    pose proof (monte_carlo_termination_condition_expectation M ps)
      as Hcondition.
    cbn [pterm_eval] in Hcondition.
    lra.
Qed.

Theorem monte_carlo_positive_complement_loop :
  forall M k : nat,
    (0 < M)%nat -> (k <= M)%nat ->
    {{ $(p_concentrated_mass
      (monte_carlo_region M k (monte_carlo_initial_region_index M k))
      [[ 1 ]]) }}
      while $(monte_carlo_guard M) do $(monte_carlo_body) end
    {{
      Pr[$(monte_carlo_complement_exit_event M k)] =
        $(1 - monte_carlo_bernoulli_mass M k)
    }}.
Proof.
  intros M k HM Hk.
  assert (Hraw := monte_carlo_positive_complement_loop_raw M k HM Hk).
  rewrite monte_carlo_initial_complement_solution in Hraw by assumption.
  pose proof (monte_carlo_eliminate_unit_mass
    (monte_carlo_region M k (monte_carlo_initial_region_index M k))
    <{ while $(monte_carlo_guard M) do $(monte_carlo_body) end }>
    (condition_pconstruct (QIndicator (monte_carlo_not_target k))
      <{ ~ $(monte_carlo_guard M) }>)
    (1 - monte_carlo_bernoulli_mass M k) Hraw) as Hunit.
  rewrite monte_carlo_complement_condition_shape in Hunit.
  exact Hunit.
Qed.

Lemma monte_carlo_remove_exit_conditioning :
  forall M k : nat,
    pformula_valid
      (PFImpl
        [[
          (Pr[~ $(monte_carlo_guard M)] = 1) /\
          (Pr[$(monte_carlo_complement_exit_event M k)] =
            $(1 - monte_carlo_bernoulli_mass M k))
        ]]
        [[
          Pr[$(monte_carlo_target k)] =
            $(monte_carlo_bernoulli_mass M k)
        ]]).
Proof.
  intros M k ps Hpost.
  apply monte_carlo_p_and_spec in Hpost.
  destruct Hpost as [Htermination Hcomplement].
  apply monte_carlo_p_eq_spec in Htermination.
  apply monte_carlo_p_eq_spec in Hcomplement.
  cbn [pterm_eval] in Htermination, Hcomplement.
  rewrite expectation_indicator in Htermination, Hcomplement.
  set (mu := pstate_measure ps).
  set (Guard := formula_assertion (monte_carlo_guard M)).
  set (NotGuard := formula_assertion <{ ~ $(monte_carlo_guard M) }>).
  set (Target := formula_assertion (monte_carlo_target k)).
  set (NotTarget := formula_assertion (monte_carlo_not_target k)).
  set (Complement := formula_assertion
    (monte_carlo_complement_exit_event M k)).
  assert (Hnotguard : measure_of mu NotGuard = 1%R).
  { unfold mu, NotGuard; exact Htermination. }
  assert (Htotal : measure_of mu (fun _ : state => True) = 1%R).
  {
    pose proof (monte_carlo_measure_monotone mu NotGuard
      (fun _ : state => True) (fun _ _ => I)) as Hlower.
    pose proof (measure_subprobability mu) as Hupper.
    lra.
  }
  assert (Hguard : measure_of mu Guard = 0%R).
  {
    assert (Hpartition :
      measure_of mu (fun _ : state => True) =
        (measure_of mu Guard + measure_of mu NotGuard)%R).
    {
      transitivity (measure_of mu (fun v => Guard v \/ NotGuard v)).
      - apply measure_extensional; intro v.
        unfold Guard, NotGuard, formula_assertion, c_not.
        cbn [satisfies].
        tauto.
      - apply measure_additive.
        intro v.
        unfold Guard, NotGuard, formula_assertion, c_not.
        cbn [satisfies].
        tauto.
    }
    lra.
  }
  set (InsideComplement := fun v : state => NotTarget v /\ Guard v).
  assert (Hinside_zero : measure_of mu InsideComplement = 0%R).
  {
    pose proof (monte_carlo_measure_monotone mu InsideComplement Guard)
      as Hupper.
    specialize (Hupper (fun v Hinside => proj2 Hinside)).
    pose proof (measure_nonnegative mu InsideComplement).
    lra.
  }
  assert (Hnot_target :
    measure_of mu NotTarget = measure_of mu Complement).
  {
    assert (Hpartition :
      measure_of mu NotTarget =
        (measure_of mu Complement + measure_of mu InsideComplement)%R).
    {
      transitivity
        (measure_of mu (fun v => Complement v \/ InsideComplement v)).
      - apply measure_extensional; intro v.
        unfold Complement, InsideComplement, NotTarget, NotGuard,
          Guard, formula_assertion, monte_carlo_complement_exit_event,
          c_not.
        rewrite monte_carlo_c_and_spec.
        cbn [satisfies].
        tauto.
      - apply measure_additive.
        intro v.
        unfold Complement, InsideComplement, NotTarget, NotGuard,
          Guard, formula_assertion, monte_carlo_complement_exit_event,
          c_not.
        rewrite monte_carlo_c_and_spec.
        cbn [satisfies].
        tauto.
    }
    lra.
  }
  assert (Htarget_partition :
    measure_of mu (fun _ : state => True) =
      (measure_of mu Target + measure_of mu NotTarget)%R).
  {
    transitivity (measure_of mu (fun v => Target v \/ NotTarget v)).
    - apply measure_extensional; intro v.
      unfold Target, NotTarget, formula_assertion,
        monte_carlo_not_target, c_not.
      cbn [satisfies].
      tauto.
    - apply measure_additive.
      intro v.
      unfold Target, NotTarget, formula_assertion,
        monte_carlo_not_target, c_not.
      cbn [satisfies].
      tauto.
  }
  apply monte_carlo_p_eq_spec.
  cbn [pterm_eval].
  rewrite expectation_indicator.
  unfold Target in Htarget_partition.
  unfold Complement, mu in Hcomplement, Hnot_target.
  unfold mu in Htotal, Htarget_partition.
  lra.
Qed.

Theorem monte_carlo_positive_loop_probability :
  forall M k : nat,
    (0 < M)%nat -> (k <= M)%nat ->
    {{ $(p_concentrated_mass
      (monte_carlo_region M k (monte_carlo_initial_region_index M k))
      [[ 1 ]]) }}
      while $(monte_carlo_guard M) do $(monte_carlo_body) end
    {{
      Pr[$(monte_carlo_target k)] =
        $(monte_carlo_bernoulli_mass M k)
    }}.
Proof.
  intros M k HM Hk.
  eapply HConseq with
    (eta1 := p_concentrated_mass
      (monte_carlo_region M k (monte_carlo_initial_region_index M k))
      (PConst 1%R))
    (eta2 := [[
      (Pr[~ $(monte_carlo_guard M)] = 1) /\
      (Pr[$(monte_carlo_complement_exit_event M k)] =
        $(1 - monte_carlo_bernoulli_mass M k))
    ]]).
  - intros ps Hpre; exact Hpre.
  - apply HAnd.
    + apply monte_carlo_positive_termination_loop; assumption.
    + apply monte_carlo_positive_complement_loop; assumption.
  - apply monte_carlo_remove_exit_conditioning.
Qed.

Definition monte_carlo_initialized_region (M k : nat) : CFormula :=
  subst_real_cformula monte_carlo_i <{ 0 }>
    (subst_real_cformula monte_carlo_H <{ 0 }>
      (monte_carlo_region M k (monte_carlo_initial_region_index M k))).

Lemma monte_carlo_initialized_region_valid :
  forall M k : nat,
    (0 < M)%nat -> (k <= M)%nat ->
    cformula_valid (monte_carlo_initialized_region M k).
Proof.
  intros M k HM Hk v.
  unfold monte_carlo_initialized_region.
  rewrite monte_carlo_subst_real_cformula_spec.
  rewrite monte_carlo_subst_real_cformula_spec.
  cbn [term_eval].
  rewrite monte_carlo_initial_region_shape by assumption.
  apply monte_carlo_exact_region_spec.
  split.
  - apply monte_carlo_time_band_spec.
    replace (M - M)%nat with 0%nat by lia.
    replace (M - M + 1)%nat with 1%nat by lia.
    change
      (0 <= update_real_values
        (update_real_values (real_program_values v) monte_carlo_i 0)
        monte_carlo_H 0 monte_carlo_i < INR 1)%R.
    unfold update_real_values.
    destruct (real_program_var_eq_dec monte_carlo_i monte_carlo_H);
      [pose proof monte_carlo_variables_distinct; tauto |].
    destruct (real_program_var_eq_dec monte_carlo_i monte_carlo_i);
      [cbn [INR]; lra | contradiction].
  - cbn [update_real update_real_values].
    destruct (real_program_var_eq_dec monte_carlo_H monte_carlo_H);
      [|contradiction].
    rewrite Rminus_diag; reflexivity.
Qed.

Lemma monte_carlo_initial_assignments_wp_shape :
  forall M k : nat,
    subst_real_pformula monte_carlo_i <{ 0 }>
      (subst_real_pformula monte_carlo_H <{ 0 }>
        (p_concentrated_mass
          (monte_carlo_region M k (monte_carlo_initial_region_index M k))
          (PConst 1%R))) =
    p_concentrated_mass (monte_carlo_initialized_region M k) (PConst 1%R).
Proof.
  intros M k.
  unfold p_concentrated_mass, monte_carlo_initialized_region.
  cbn [subst_real_pformula subst_real_pterm subst_real_pconstruct
    subst_real_pconstruct_fuel].
  reflexivity.
Qed.

Lemma monte_carlo_normalized_initializes_positive_region :
  forall M k : nat,
    (0 < M)%nat -> (k <= M)%nat ->
    pformula_valid
      (PFImpl monte_carlo_normalized
        (subst_real_pformula monte_carlo_i <{ 0 }>
          (subst_real_pformula monte_carlo_H <{ 0 }>
            (p_concentrated_mass
              (monte_carlo_region M k
                (monte_carlo_initial_region_index M k))
              (PConst 1%R))))).
Proof.
  intros M k HM Hk.
  rewrite monte_carlo_initial_assignments_wp_shape.
  intros ps Hnormalized.
  unfold monte_carlo_normalized in Hnormalized.
  apply monte_carlo_p_eq_spec in Hnormalized.
  apply (proj2 (monte_carlo_p_and_spec _ _ _)).
  split.
  - apply (proj2 (monte_carlo_p_eq_spec _ _ _)).
    cbn [pterm_eval].
    rewrite !expectation_indicator.
    apply measure_extensional.
    intro v; unfold formula_assertion.
    split; intros _.
    + unfold c_true; cbn [satisfies]; tauto.
    + apply monte_carlo_initialized_region_valid; assumption.
  - apply (proj2 (monte_carlo_p_eq_spec _ _ _)).
    exact Hnormalized.
Qed.

Theorem monte_carlo_positive_probability :
  forall M k : nat,
    (0 < M)%nat -> (k <= M)%nat ->
    {{ $(monte_carlo_normalized) }}
      $(monte_carlo_estimator M)
    {{
      Pr[$(monte_carlo_target k)] =
        $(monte_carlo_binomial_mass M k)
    }}.
Proof.
  intros M k HM Hk.
  unfold monte_carlo_estimator.
  eapply HConseq with
    (eta1 := subst_real_pformula monte_carlo_i <{ 0 }>
      (subst_real_pformula monte_carlo_H <{ 0 }>
        (p_concentrated_mass
          (monte_carlo_region M k (monte_carlo_initial_region_index M k))
          (PConst 1%R))))
    (eta2 := [[
      Pr[$(monte_carlo_target k)] =
        $(monte_carlo_bernoulli_mass M k)
    ]]).
  - apply monte_carlo_normalized_initializes_positive_region; assumption.
  - eapply HSeq with
      (eta2 := subst_real_pformula monte_carlo_H <{ 0 }>
        (p_concentrated_mass
          (monte_carlo_region M k (monte_carlo_initial_region_index M k))
          (PConst 1%R))).
    + apply HRealAssign.
    + eapply HSeq with
        (eta2 := p_concentrated_mass
          (monte_carlo_region M k (monte_carlo_initial_region_index M k))
          (PConst 1%R)).
      * apply HRealAssign.
      * apply monte_carlo_positive_loop_probability; assumption.
  - intros ps Hprobability.
    apply monte_carlo_p_eq_spec in Hprobability.
    apply monte_carlo_p_eq_spec.
    cbn [pterm_eval] in *.
    rewrite (monte_carlo_bernoulli_mass_is_binomial M k Hk) in Hprobability.
    exact Hprobability.
Qed.

Definition monte_carlo_zero_state : CFormula :=
  <{ monte_carlo_i = 0 /\ monte_carlo_H = 0 }>.

Definition monte_carlo_initialized_zero_state : CFormula :=
  subst_real_cformula monte_carlo_i <{ 0 }>
    (subst_real_cformula monte_carlo_H <{ 0 }> monte_carlo_zero_state).

Lemma monte_carlo_initialized_zero_state_valid :
  cformula_valid monte_carlo_initialized_zero_state.
Proof.
  intro v.
  unfold monte_carlo_initialized_zero_state.
  rewrite monte_carlo_subst_real_cformula_spec.
  rewrite monte_carlo_subst_real_cformula_spec.
  cbn [term_eval].
  set (initialized :=
    update_real (update_real v monte_carlo_i 0) monte_carlo_H 0).
  change (satisfies initialized monte_carlo_zero_state).
  assert (Hi : real_program_values initialized monte_carlo_i = 0%R).
  {
    unfold initialized, update_real; cbn.
    unfold update_real_values.
    destruct (real_program_var_eq_dec monte_carlo_i monte_carlo_H);
      [pose proof monte_carlo_variables_distinct; tauto |].
    destruct (real_program_var_eq_dec monte_carlo_i monte_carlo_i);
      [reflexivity | contradiction].
  }
  assert (HH : real_program_values initialized monte_carlo_H = 0%R).
  {
    unfold initialized, update_real; cbn.
    unfold update_real_values.
    destruct (real_program_var_eq_dec monte_carlo_H monte_carlo_H);
      [reflexivity | contradiction].
  }
  unfold monte_carlo_zero_state.
  apply monte_carlo_c_and_spec.
  split; apply monte_carlo_c_and_spec; cbn [satisfies term_eval];
    split; lra.
Qed.

Lemma monte_carlo_zero_initial_assignments_wp_shape :
  subst_real_pformula monte_carlo_i <{ 0 }>
    (subst_real_pformula monte_carlo_H <{ 0 }>
      (p_concentrated_mass monte_carlo_zero_state (PConst 1%R))) =
  p_concentrated_mass monte_carlo_initialized_zero_state (PConst 1%R).
Proof.
  unfold p_concentrated_mass, monte_carlo_initialized_zero_state.
  cbn [subst_real_pformula subst_real_pterm subst_real_pconstruct
    subst_real_pconstruct_fuel].
  reflexivity.
Qed.

Lemma monte_carlo_normalized_initializes_zero_state :
  pformula_valid
    (PFImpl monte_carlo_normalized
      (subst_real_pformula monte_carlo_i <{ 0 }>
        (subst_real_pformula monte_carlo_H <{ 0 }>
          (p_concentrated_mass monte_carlo_zero_state (PConst 1%R))))).
Proof.
  rewrite monte_carlo_zero_initial_assignments_wp_shape.
  intros ps Hnormalized.
  unfold monte_carlo_normalized in Hnormalized.
  apply monte_carlo_p_eq_spec in Hnormalized.
  apply (proj2 (monte_carlo_p_and_spec _ _ _)).
  split.
  - apply (proj2 (monte_carlo_p_eq_spec _ _ _)).
    cbn [pterm_eval].
    rewrite !expectation_indicator.
    apply measure_extensional.
    intro v; unfold formula_assertion.
    split; intros _.
    + unfold c_true; cbn [satisfies]; tauto.
    + apply monte_carlo_initialized_zero_state_valid.
  - apply (proj2 (monte_carlo_p_eq_spec _ _ _)).
    exact Hnormalized.
Qed.

Lemma monte_carlo_zero_state_guard_false :
  cformula_valid
    <{ $(monte_carlo_zero_state) -> ~ $(monte_carlo_guard 0) }>.
Proof.
  intros v Hzero Hguard.
  unfold monte_carlo_guard in Hguard.
  apply monte_carlo_c_and_spec in Hguard.
  cbn [satisfies c_lt c_not term_eval INR] in Hguard.
  destruct Hguard as [Hnonnegative Hnegative].
  apply Hnegative; lra.
Qed.

Lemma monte_carlo_zero_state_implies_target :
  cformula_valid
    <{ $(monte_carlo_zero_state) -> $(monte_carlo_target 0) }>.
Proof.
  intros v Hzero.
  unfold monte_carlo_zero_state in Hzero.
  apply monte_carlo_c_and_spec in Hzero.
  destruct Hzero as [Hi HH].
  apply monte_carlo_target_spec.
  apply monte_carlo_c_and_spec in HH.
  cbn [satisfies term_eval INR] in HH |- *.
  lra.
Qed.

Theorem monte_carlo_zero_horizon_probability :
  {{ $(monte_carlo_normalized) }}
    $(monte_carlo_estimator 0)
  {{
    Pr[$(monte_carlo_target 0)] =
      $(monte_carlo_binomial_mass 0 0)
  }}.
Proof.
  assert (Hloop :
    {{ $(p_concentrated_mass monte_carlo_zero_state [[ 1 ]]) }}
      while $(monte_carlo_guard 0) do $(monte_carlo_body) end
    {{ $(p_concentrated_mass monte_carlo_zero_state [[ 1 ]]) }}).
  {
    apply HWhileNot_unit.
    apply monte_carlo_zero_state_guard_false.
  }
  assert (Hloop_probability :
    {{ $(p_concentrated_mass monte_carlo_zero_state [[ 1 ]]) }}
      while $(monte_carlo_guard 0) do $(monte_carlo_body) end
    {{ Pr[$(monte_carlo_target 0)] = 1 }}).
  {
    eapply HConseq with
      (eta1 := p_concentrated_mass monte_carlo_zero_state (PConst 1%R))
      (eta2 := p_concentrated_mass monte_carlo_zero_state (PConst 1%R)).
    - intros ps Hpre; exact Hpre.
    - exact Hloop.
    - intros ps Hconcentrated.
      apply monte_carlo_p_eq_spec.
      cbn [pterm_eval].
      rewrite expectation_indicator.
      apply monte_carlo_concentrated_event_full with
        (rho := monte_carlo_zero_state).
      * exact Hconcentrated.
      * apply monte_carlo_zero_state_implies_target.
  }
  unfold monte_carlo_estimator.
  eapply HConseq with
    (eta1 := subst_real_pformula monte_carlo_i <{ 0 }>
      (subst_real_pformula monte_carlo_H <{ 0 }>
        (p_concentrated_mass monte_carlo_zero_state (PConst 1%R))))
    (eta2 := [[ Pr[$(monte_carlo_target 0)] = 1 ]]).
  - apply monte_carlo_normalized_initializes_zero_state.
  - eapply HSeq with
      (eta2 := subst_real_pformula monte_carlo_H <{ 0 }>
        (p_concentrated_mass monte_carlo_zero_state (PConst 1%R))).
    + apply HRealAssign.
    + eapply HSeq with
        (eta2 := p_concentrated_mass monte_carlo_zero_state (PConst 1%R)).
      * apply HRealAssign.
      * exact Hloop_probability.
  - intros ps Hprobability.
    apply monte_carlo_p_eq_spec in Hprobability.
    apply monte_carlo_p_eq_spec.
    cbn [pterm_eval] in *.
    unfold monte_carlo_binomial_mass.
    rewrite monte_carlo_binomial_zero.
    cbn [pow].
    ring_simplify.
    exact Hprobability.
Qed.

Theorem monte_carlo_estimator_probability :
  forall M k : nat,
    (k <= M)%nat ->
    {{ $(monte_carlo_normalized) }}
      $(monte_carlo_estimator M)
    {{
      Pr[$(monte_carlo_target k)] =
        $(monte_carlo_binomial_mass M k)
    }}.
Proof.
  intros M k Hk.
  destruct M as [|M].
  - assert (k = 0)%nat by lia; subst k.
    apply monte_carlo_zero_horizon_probability.
  - apply monte_carlo_positive_probability; lia.
Qed.

(** Small concrete checks requested for the development. *)
Corollary monte_carlo_probability_0_0 :
  {{ $(monte_carlo_normalized) }}
    $(monte_carlo_estimator 0)
  {{ Pr[$(monte_carlo_target 0)] = $(monte_carlo_binomial_mass 0 0) }}.
Proof. apply monte_carlo_estimator_probability; lia. Qed.

Corollary monte_carlo_probability_1_0 :
  {{ $(monte_carlo_normalized) }}
    $(monte_carlo_estimator 1)
  {{ Pr[$(monte_carlo_target 0)] = $(monte_carlo_binomial_mass 1 0) }}.
Proof. apply monte_carlo_estimator_probability; lia. Qed.

Corollary monte_carlo_probability_1_1 :
  {{ $(monte_carlo_normalized) }}
    $(monte_carlo_estimator 1)
  {{ Pr[$(monte_carlo_target 1)] = $(monte_carlo_binomial_mass 1 1) }}.
Proof. apply monte_carlo_estimator_probability; lia. Qed.

Corollary monte_carlo_probability_2_1 :
  {{ $(monte_carlo_normalized) }}
    $(monte_carlo_estimator 2)
  {{ Pr[$(monte_carlo_target 1)] = $(monte_carlo_binomial_mass 2 1) }}.
Proof. apply monte_carlo_estimator_probability; lia. Qed.
