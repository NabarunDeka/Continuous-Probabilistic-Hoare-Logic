(**
  PersistentSampleLoop.v

  Program ([t2_prog s]):

      x <- sample(laplace(0, s));
      b <- ff;
      while ~b do
        if 0 <= x then toss(b, 1/2) else toss(b, 1/4)
      end

  Triple ([t2_prog_correct], for 0 < s):

      { E[1_tt] = 1 }  t2_prog s  { E[1_(tt /\ ~~b)] = 1 }

  Triple ([t2_loop_derivable], for k < 2 and any rigid y; [t2_loop] is the
  while loop and region k is [t2_regions k]: ~b /\ 0 <= x for k = 0,
  ~b /\ ~(0 <= x) for k = 1):

      { E[1_(region k)] = E[1_tt] /\ E[1_tt] = y }
          t2_loop
      { E[1_(tt /\ ~~b)] = 1 * y }

  Triple ([t2_sample_splits], for 0 < s):

      { E[1_tt] = 1 }  x <- sample(laplace(0, s))  { E[1_(0 <= x)] = 1/2 }
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import ClassicalDescription.
From Stdlib Require Import Classical.
Require Import CPHL.
Require Import MeasureIntegration.
Require Import CPHLFacts.CalculationFacts CPHLFacts.ExponentialIntegrals.
Require Import SampleBeforeLoop.
Require Import SVT.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** Classical conjunction, which [c_and] encodes through negation. *)
Lemma satisfies_c_and :
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

(** * Measure facts for formula events

    Formula events are measurable, so finite additivity applies to them. *)

Lemma admissible_finite :
  forall ps : Pstate, pstate_admissible ps -> FiniteMeasure (pstate_measure ps).
Proof. intros ps H; exact (ConcreteMeasure.subprob_finite H). Qed.

Lemma expect_indicator_mono :
  forall (mu : Measure) (gamma delta : CFormula),
    FiniteMeasure mu ->
    (forall v : state, satisfies v gamma -> satisfies v delta) ->
    (expectation mu (q_eval (QIndicator gamma))
     <= expectation mu (q_eval (QIndicator delta)))%R.
Proof.
  intros mu gamma delta Hfin Hsub.
  rewrite !expectation_indicator.
  assert (Hsplit :
    measure_of mu (formula_assertion delta) =
    (measure_of mu (formula_assertion gamma) +
     measure_of mu (formula_assertion (c_and delta (c_not gamma))))%R).
  { rewrite <- measure_additive.
    - apply measure_extensional; intro v; unfold formula_assertion.
      rewrite satisfies_c_and; cbn [c_not satisfies].
      split.
      + intro Hd; destruct (classic (satisfies v gamma)); [left | right]; tauto.
      + intros [Hg | Hrest]; [apply Hsub; exact Hg | exact (proj1 Hrest)].
    - exact Hfin.
    - exact (ValuationSpace.measurable_formula_event gamma).
    - exact (ValuationSpace.measurable_formula_event (c_and delta (c_not gamma))).
    - intro v; unfold formula_assertion; rewrite satisfies_c_and;
        cbn [c_not satisfies]; tauto. }
  rewrite Hsplit.
  pose proof (measure_nonnegative mu
    (formula_assertion (c_and delta (c_not gamma)))) as Hpos.
  lra.
Qed.

(** Complementary events split the total mass. *)
Lemma expect_indicator_complement :
  forall (mu : Measure) (gamma : CFormula),
    FiniteMeasure mu ->
    (expectation mu (q_eval (QIndicator gamma)) +
     expectation mu (q_eval (QIndicator (c_not gamma))))%R =
    expectation mu (q_eval (QIndicator c_true)).
Proof.
  intros mu gamma Hfin.
  rewrite !expectation_indicator.
  rewrite <- measure_additive.
  - apply measure_extensional; intro v.
    unfold formula_assertion; cbn [c_true c_not satisfies]; tauto.
  - exact Hfin.
  - exact (ValuationSpace.measurable_formula_event gamma).
  - exact (ValuationSpace.measurable_formula_event (c_not gamma)).
  - intro v; unfold formula_assertion; cbn [c_not satisfies]; tauto.
Qed.

(** * The program *)

Definition t2_x : RealProgramVar := real_program_var "t2_x".
Definition t2_b : BoolProgramVar := bool_program_var "t2_b".
Definition t2_y : ProbLogicVar := prob_logic_var "t2_y".

Definition t2_noise (s : R) : Distribution := <{ laplace(0, s) }>.

(** The sampled value's sign: the branch guard, and what the regions pin. *)
Definition t2_pos : CFormula := <{ 0 <= t2_x }>.

Definition t2_guard : CFormula := <{ ~ t2_b }>.

Definition t2_body : Cmd :=
  <{ if $(t2_pos) then t2_b toss $(1 / 2) else t2_b toss $(1 / 4) end }>.

Definition t2_loop : Cmd := <{ while $(t2_guard) do $(t2_body) end }>.

Definition t2_prog (s : R) : Cmd :=
  <{ t2_x sample $(t2_noise s);
     t2_b b= false;
     $(t2_loop) }>.

(** * Certificate data

    Region 0 is "still looping, sample was non-negative"; region 1 is the
    other side.  The body cannot move mass between them, because [x] is
    never assigned -- so the transition matrix is diagonal. *)

Definition t2_regions (i : nat) : CFormula :=
  if Nat.eqb i 0 then <{ $(t2_guard) /\ $(t2_pos) }>
  else <{ $(t2_guard) /\ (~ $(t2_pos)) }>.

Definition t2_transitions (i j : nat) : R :=
  if Nat.eqb i 0
  then (if Nat.eqb j 0 then 1 / 2 else 0)
  else (if Nat.eqb j 1 then 3 / 4 else 0).

Definition t2_exits (i : nat) : R :=
  if Nat.eqb i 0 then 1 / 2 else 1 / 4.

Definition t2_solution (_ : nat) : R := 1.

Definition t2_q : PConstruct := QIndicator c_true.

(** * From a concentrated region, the branch masses are known

    This is the fact the body premise turns on: if all mass sits on a region
    contained in [gamma], then [gamma] carries the whole mass and its
    complement carries none. *)

Lemma concentrated_superset :
  forall (ps : Pstate) (region gamma : CFormula),
    pstate_admissible ps ->
    psatisfies ps (p_concentrated_mass region (PConst 1)) ->
    (forall v : state, satisfies v region -> satisfies v gamma) ->
    expectation (pstate_measure ps) (q_eval (QIndicator gamma)) = 1%R /\
    expectation (pstate_measure ps)
      (q_eval (QIndicator (c_not gamma))) = 0%R.
Proof.
  intros ps region gamma Hadm Hconc Hsub.
  pose proof (admissible_finite ps Hadm) as Hfin.
  apply psatisfies_p_and in Hconc.
  destruct Hconc as [Hall Hmass].
  apply psatisfies_p_eq in Hall; apply psatisfies_p_eq in Hmass.
  cbn [pterm_eval] in Hall, Hmass.
  assert (Hlow : (1 <= expectation (pstate_measure ps)
                        (q_eval (QIndicator gamma)))%R).
  { rewrite <- Hmass, <- Hall.
    apply expect_indicator_mono; [exact Hfin | exact Hsub]. }
  assert (Hhigh : (expectation (pstate_measure ps)
                     (q_eval (QIndicator gamma)) <= 1)%R).
  { rewrite <- Hmass.
    apply expect_indicator_mono; [exact Hfin |].
    intros v _; cbn [c_true satisfies]; tauto. }
  pose proof (expect_indicator_complement (pstate_measure ps) gamma Hfin) as Hc.
  split; lra.
Qed.

(** * Reducing the conditioned, tossed expectations

    Every implication below has the same shape: four expectations of
    indicators, each of which is either unsatisfiable (value 0) or
    equivalent to [t2_pos] / its negation, whose values the concentrated
    precondition fixes. *)

Lemma expect_indicator_iff :
  forall (mu : Measure) (gamma delta : CFormula),
    (forall v : state, satisfies v gamma <-> satisfies v delta) ->
    expectation mu (q_eval (QIndicator gamma)) =
    expectation mu (q_eval (QIndicator delta)).
Proof.
  intros mu gamma delta H.
  rewrite !expectation_indicator.
  apply measure_extensional; intro v; unfold formula_assertion; apply H.
Qed.

(** [t2_pos] mentions no boolean variable, so boolean substitution is the
    identity on it.  Rewriting with this keeps [t2_pos] folded, which lets
    [tauto] treat it as an atom below. *)
Lemma subst_bool_t2_pos :
  forall (b : BoolProgramVar) (beta : CFormula),
    subst_bool_cformula b beta t2_pos = t2_pos.
Proof. reflexivity. Qed.

Ltac t2_step :=
  match goal with
  | |- context [expectation ?mu (q_eval (QIndicator ?g))] =>
      first
        [ rewrite (expect_indicator_unsat mu g)
            by (intro v; cbn [c_true c_and c_not satisfies]; tauto)
        | rewrite (expect_indicator_iff mu g t2_pos)
            by (intro v; cbn [c_true c_and c_not satisfies]; tauto);
          match goal with
          | H : expectation _ (q_eval (QIndicator t2_pos)) = _ |- _ =>
              rewrite H
          end
        | rewrite (expect_indicator_iff mu g (c_not t2_pos))
            by (intro v; cbn [c_true c_and c_not satisfies]; tauto);
          match goal with
          | H : expectation _ (q_eval (QIndicator (c_not t2_pos))) = _ |- _ =>
              rewrite H
          end ]
  end.

Ltac t2_close := repeat t2_step; lra.

(** Unfold an [if_precondition] down to raw real equations. *)
Ltac t2_expose :=
  unfold if_precondition, t2_regions, t2_guard, svt_event_probability;
  cbn [Nat.eqb];
  apply psatisfies_p_and; split; apply psatisfies_p_eq;
  cbn [condition_pformula condition_pterm condition_pconstruct
       condition_pconstruct_fuel pconstruct_size subst_prob_pformula
       subst_prob_pterm toss_pformula toss_pterm subst_bool_pconstruct
       subst_bool_pconstruct_fuel subst_bool_cformula c_and c_not pterm_eval];
  try rewrite !bpv_eq_dec_refl;
  try rewrite !subst_bool_t2_pos.

(** * One conditional step of the body

    [svt_if_constants] does the work: the two branch triples come straight
    from [HBoolToss], and the rigid variables it introduces are eliminated
    against the constants. *)

Lemma t2_body_event :
  forall (region delta : CFormula) (r1 r2 : R),
    pformula_valid
      (PFImpl (p_concentrated_mass region (PConst 1))
        (subst_prob_pformula svt_y_then (PConst r1)
          (subst_prob_pformula svt_y_else (PConst r2)
            (if_precondition
               (toss_pformula t2_b (1 / 2) (svt_event_probability r1 delta))
               (toss_pformula t2_b (1 / 4) (svt_event_probability r2 delta))
               t2_pos)))) ->
    forall c : R, c = (r1 + r2)%R ->
    hoare_derivable (p_concentrated_mass region (PConst 1)) t2_body
      (p_eq (PExpect (QIndicator delta)) (PConst c)).
Proof.
  intros region delta r1 r2 Himp c Hc.
  subst c.
  eapply HConseq with
    (eta1 :=
       subst_prob_pformula svt_y_then (PConst r1)
         (subst_prob_pformula svt_y_else (PConst r2)
           (if_precondition
              (toss_pformula t2_b (1 / 2) (svt_event_probability r1 delta))
              (toss_pformula t2_b (1 / 4) (svt_event_probability r2 delta))
              t2_pos)))
    (eta2 := svt_event_probability (r1 + r2) delta).
  - exact Himp.
  - unfold t2_body.
    apply svt_if_constants; apply HBoolToss;
      unfold coin_probability_valid; lra.
  - intros ps Hadm.
    cbn [psatisfies].
    intro H.
    apply psatisfies_p_eq in H.
    apply psatisfies_p_eq.
    cbn [pterm_eval] in H |- *.
    lra.
Qed.

(** * The mass on each side of the sample, inside a region *)

Lemma t2_region_values_0 :
  forall ps : Pstate,
    pstate_admissible ps ->
    psatisfies ps (p_concentrated_mass (t2_regions 0) (PConst 1)) ->
    expectation (pstate_measure ps) (q_eval (QIndicator t2_pos)) = 1%R /\
    expectation (pstate_measure ps)
      (q_eval (QIndicator (c_not t2_pos))) = 0%R.
Proof.
  intros ps Hadm Hconc.
  apply (concentrated_superset ps (t2_regions 0) t2_pos Hadm Hconc).
  intros v Hv.
  unfold t2_regions in Hv; cbn [Nat.eqb] in Hv.
  apply satisfies_c_and in Hv; tauto.
Qed.

Lemma t2_region_values_1 :
  forall ps : Pstate,
    pstate_admissible ps ->
    psatisfies ps (p_concentrated_mass (t2_regions 1) (PConst 1)) ->
    expectation (pstate_measure ps) (q_eval (QIndicator t2_pos)) = 0%R /\
    expectation (pstate_measure ps)
      (q_eval (QIndicator (c_not t2_pos))) = 1%R.
Proof.
  intros ps Hadm Hconc.
  assert (Hsup :
    expectation (pstate_measure ps)
      (q_eval (QIndicator (c_not t2_pos))) = 1%R /\
    expectation (pstate_measure ps)
      (q_eval (QIndicator (c_not (c_not t2_pos)))) = 0%R).
  { apply (concentrated_superset ps (t2_regions 1) (c_not t2_pos) Hadm Hconc).
    intros v Hv.
    unfold t2_regions in Hv; cbn [Nat.eqb] in Hv.
    apply satisfies_c_and in Hv; tauto. }
  destruct Hsup as [Hn1 _].
  apply psatisfies_p_and in Hconc.
  destruct Hconc as [_ Hmass].
  apply psatisfies_p_eq in Hmass.
  cbn [pterm_eval] in Hmass.
  pose proof (expect_indicator_complement (pstate_measure ps) t2_pos
    (admissible_finite ps Hadm)) as Hc.
  split; lra.
Qed.

(** * The body premise, for both regions

    Four components: the trivial [p_true], the two transition
    probabilities, and the exit probability.  Each of the last three is one
    application of [t2_body_event]. *)

Definition t2_exit_event : CFormula := <{ true /\ (~ $(t2_guard)) }>.

Ltac t2_event r1 r2 vals :=
  apply (t2_body_event _ _ r1 r2);
  [ intros ps Hadm; cbn [psatisfies]; intro Hconc;
    lazymatch goal with
    | Hc : psatisfies _ (p_concentrated_mass _ _) |- _ =>
        destruct (vals _ Hadm Hc) as [Hpos Hneg]
    end;
    t2_expose; t2_close
  | cbn [t2_transitions t2_exits Nat.eqb]; lra ].

Lemma t2_body_step :
  forall i : nat,
    (i < 2)%nat ->
    hoare_derivable
      (p_concentrated_mass (t2_regions i) (PConst 1))
      t2_body
      (while_body_post 2 t2_regions (t2_transitions i) t2_guard t2_q
         (t2_exits i)).
Proof.
  intros i Hi.
  assert (Hcases : i = 0%nat \/ i = 1%nat) by lia.
  unfold while_body_post, t2_q.
  cbn [finite_p_and condition_pconstruct condition_pconstruct_fuel
       pconstruct_size].
  destruct Hcases as [-> | ->].
  - apply HAnd.
    + apply HAnd.
      * apply HAnd.
        -- eapply HConseq with (eta1 := p_true) (eta2 := p_true);
             [ intros ps Hadm; cbn [psatisfies]; intro Hx; apply psatisfies_p_true
             | apply HFree; cbn [p_true pformula_analytical]; tauto
             | intros ps Hadm; cbn [psatisfies]; tauto ].
        -- t2_event (1/2)%R 0%R t2_region_values_0.
      * t2_event 0%R 0%R t2_region_values_0.
    + t2_event (1/2)%R 0%R t2_region_values_0.
  - apply HAnd.
    + apply HAnd.
      * apply HAnd.
        -- eapply HConseq with (eta1 := p_true) (eta2 := p_true);
             [ intros ps Hadm; cbn [psatisfies]; intro Hx; apply psatisfies_p_true
             | apply HFree; cbn [p_true pformula_analytical]; tauto
             | intros ps Hadm; cbn [psatisfies]; tauto ].
        -- t2_event 0%R 0%R t2_region_values_1.
      * t2_event 0%R (3/4)%R t2_region_values_1.
    + t2_event 0%R (1/4)%R t2_region_values_1.
Qed.

(** * The loop

    Both regions terminate almost surely, by different linear systems:
    [x0 = x0/2 + 1/2] on the non-negative side, [x1 = 3*x1/4 + 1/4] on the
    other.  Both solve to 1. *)

Lemma satisfies_c_or :
  forall (v : state) (g1 g2 : CFormula),
    satisfies v (c_or g1 g2) <-> (satisfies v g1 \/ satisfies v g2).
Proof.
  intros v g1 g2.
  cbn [c_or c_not satisfies].
  split.
  - intro H.
    destruct (classic (satisfies v g1)) as [H1 | H1].
    + left; exact H1.
    + right; apply H; intro H1'; contradiction.
  - intros [H1 | H2] Hn; [exact (match Hn H1 with end) | exact H2].
Qed.

Lemma t2_loop_derivable :
  forall (y : ProbLogicVar) (k : nat),
    (k < 2)%nat ->
    hoare_derivable
      (p_concentrated_mass (t2_regions k) (PVar y))
      t2_loop
      (p_eq (PExpect (condition_pconstruct t2_q (c_not t2_guard)))
         (PMul (PConst (t2_solution k)) (PVar y))).
Proof.
  intros y k Hk.
  eapply HWhile with
    (m := 2%nat) (k := k)
    (regions := t2_regions) (solution := t2_solution)
    (exits := t2_exits) (transitions := t2_transitions).
  - exact Hk.
  - (* the two regions cover the guard *)
    unfold while_regions_cover, cformula_valid.
    intro v; cbn [finite_c_or]; cbn [satisfies].
    intro Hguard.
    apply satisfies_c_or.
    destruct (classic (satisfies v t2_pos)) as [Hp | Hp].
    + left.
      apply satisfies_c_or; right.
      unfold t2_regions; cbn [Nat.eqb].
      apply satisfies_c_and; split; assumption.
    + right.
      unfold t2_regions; cbn [Nat.eqb].
      apply satisfies_c_and; split; [assumption |].
      cbn [c_not satisfies]; exact Hp.
  - (* each region lies inside the guard *)
    unfold while_regions_in_guard, cformula_valid.
    intros i Hi v.
    cbn [satisfies]; intro Hv.
    unfold t2_regions in Hv.
    destruct (Nat.eqb i 0); apply satisfies_c_and in Hv; tauto.
  - (* the regions are disjoint *)
    unfold while_regions_disjoint, cformula_valid.
    intros i j Hi Hj v.
    assert (i = 1%nat /\ j = 0%nat) as [-> ->] by lia.
    unfold t2_regions; cbn [Nat.eqb].
    cbn [c_not satisfies]; intro Hboth.
    apply satisfies_c_and in Hboth.
    destruct Hboth as [H1 H0].
    apply satisfies_c_and in H1; apply satisfies_c_and in H0.
    destruct H1 as [_ Hnp]; destruct H0 as [_ Hp].
    cbn [c_not satisfies] in Hnp.
    exact (Hnp Hp).
  - (* both regions exit with positive probability *)
    unfold while_progress, t2_exits.
    intros i Hi; left.
    destruct (Nat.eqb i 0); lra.
  - exact t2_body_step.
  - unfold while_solution, t2_solution, t2_transitions, t2_exits.
    intros i Hi.
    assert (Hcases : i = 0%nat \/ i = 1%nat) by lia.
    destruct Hcases as [-> | ->]; cbn [finite_r_sum Nat.eqb]; split; lra.
Qed.

(** * The sample splits the mass evenly -- and that is what blocks entry *)

Lemma rpv_eq_dec_refl :
  forall (x : RealProgramVar) (A : Type) (a b : A),
    (if real_program_var_eq_dec x x then a else b) = a.
Proof.
  intros x A a b.
  destruct (real_program_var_eq_dec x x) as [_ | Hne];
    [reflexivity | contradiction].
Qed.

(** A centred Laplace puts exactly half its mass on [0 <= x]: the density
    integral is an exponential tail, evaluated by [real_integral_exp_above_proved]. *)
Lemma t2_half :
  forall (s : R) (v : state),
    (0 < s)%R ->
    q_eval [[ integral t2_x ~ $(t2_noise s), indicator[$(t2_pos)] ]] v = (1 / 2)%R.
Proof.
  intros s v Hs.
  rewrite q_integral_density by (cbn [t2_noise distribution_valid term_eval]; exact Hs).
  transitivity
    (real_integral
       (fun z => (1 / (2 * s)) * (real_indicator (0 <= z)%R * exp ((- / s) * z))))%R.
  - apply real_integral_extensional; intro z.
    unfold t2_noise, t2_pos, update_real, update_real_values.
    cbn [distribution_density term_eval q_eval].
    rewrite formula_indicatorE.
    cbn [satisfies term_eval real_program_values].
    rewrite rpv_eq_dec_refl.
    destruct (Rle_dec 0 z) as [Hz | Hz].
    + rewrite !real_indicator_true by exact Hz.
      rewrite Rminus_0_r, Rabs_right by lra.
      replace (- z / s)%R with (- / s * z)%R by (field; lra).
      ring.
    + rewrite !real_indicator_false by exact Hz; ring.
  - rewrite real_integral_scale
      by (apply real_integrable_exp_above;
          apply Ropp_lt_gt_0_contravar, Rinv_0_lt_compat; exact Hs).
    change (real_integral (fun z => real_indicator (0 <= z)%R * exp (- / s * z)))
      with (real_integral_above 0 (fun z => exp (- / s * z))).
    rewrite real_integral_exp_above_proved
      by (apply Ropp_lt_gt_0_contravar, Rinv_0_lt_compat; exact Hs).
    rewrite Rmult_0_r, exp_0.
    field; lra.
Qed.

(** The sample puts half the mass on each side of zero. *)
Lemma t2_sample_splits :
  forall s : R,
    (0 < s)%R ->
    hoare_derivable
      (p_eq (PExpect (QIndicator c_true)) (PConst 1))
      (CRealSample t2_x (t2_noise s))
      (p_eq (PExpect (QIndicator t2_pos)) (PConst (1 / 2))).
Proof.
  intros s Hs.
  apply HRealSample.
  - intros ps Hadm.
    cbn [psatisfies].
    intro Hpre.
    apply psatisfies_p_eq in Hpre.
    cbn [pterm_eval] in Hpre.
    rewrite sample_pformula_p_eq.
    apply psatisfies_p_eq.
    cbn [sample_pterm pterm_eval].
    transitivity
      (expectation (pstate_measure ps) (fun _ : state => (1 / 2)%R)).
    + apply expectation_extensional; intro v; apply t2_half; exact Hs.
    + rewrite expectation_constant, Hpre; lra.
  - intros ps Hadm _.
    refine (p_almost_sure_of_pointwise _ _ ps Hadm).
    intro v.
    unfold t2_noise.
    cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
    intro Hle; lra.
Qed.

(** * The obstruction, machine-checked

    After the sample the measure has half its mass on each side of zero, so
    it lies in NEITHER region.  [HWhile]'s precondition [p_concentrated_mass]
    demands the whole measure sit in one, so the loop cannot be entered --
    no matter what the postcondition is. *)

Lemma t2_split_blocks_entry :
  forall ps : Pstate,
    pstate_admissible ps ->
    expectation (pstate_measure ps) (q_eval (QIndicator c_true)) = 1%R ->
    expectation (pstate_measure ps) (q_eval (QIndicator t2_pos)) =
      (1 / 2)%R ->
    ~ psatisfies ps (p_concentrated_mass (t2_regions 0) (PVar t2_y)) /\
    ~ psatisfies ps (p_concentrated_mass (t2_regions 1) (PVar t2_y)).
Proof.
  intros ps Hadm Htot Hhalf.
  pose proof (admissible_finite ps Hadm) as Hfin.
  pose proof (expect_indicator_complement (pstate_measure ps) t2_pos Hfin) as Hc.
  split; intro Hconc; apply psatisfies_p_and in Hconc;
    destruct Hconc as [Hall _]; apply psatisfies_p_eq in Hall;
    cbn [pterm_eval] in Hall.
  - assert (Hle :
      (expectation (pstate_measure ps)
         (q_eval (QIndicator (t2_regions 0)))
       <= expectation (pstate_measure ps) (q_eval (QIndicator t2_pos)))%R).
    { apply expect_indicator_mono; [exact Hfin |].
      intros v Hv.
      unfold t2_regions in Hv; cbn [Nat.eqb] in Hv.
      apply satisfies_c_and in Hv; tauto. }
    lra.
  - assert (Hle :
      (expectation (pstate_measure ps)
         (q_eval (QIndicator (t2_regions 1)))
       <= expectation (pstate_measure ps)
            (q_eval (QIndicator (c_not t2_pos))))%R).
    { apply expect_indicator_mono; [exact Hfin |].
      intros v Hv.
      unfold t2_regions in Hv; cbn [Nat.eqb] in Hv.
      apply satisfies_c_and in Hv; tauto. }
    lra.
Qed.

(** * The whole program, through [SUM]

    After the sample, split the measure along [0 <= x] and its negation.
    Each part is concentrated on one loop region, where [HWhile] applies;
    [HSumLe] and [HSumGe] recombine the two exact results, and [HElimv]
    removes the rigid masses [y1], [y2]. *)

Definition t2_y1 : ProbLogicVar := prob_logic_var "t2_y1".
Definition t2_y2 : ProbLogicVar := prob_logic_var "t2_y2".

(** The accepted event of the loop: [tt /\ ~~b]. *)
Definition t2_post_q : PConstruct := condition_pconstruct t2_q (c_not t2_guard).

(** Each half: the guard holds almost surely and the half has mass [y]. *)
Definition t2_eta (y : ProbLogicVar) : PFormula :=
  [[ almost_sure[$(t2_guard)] /\ Pr[true] = y ]].

(** Two almost-sure events hold jointly almost surely. *)
Lemma expect_as_conj :
  forall (mu : Measure) (gamma delta : CFormula),
    FiniteMeasure mu ->
    expectation mu (q_eval (QIndicator gamma)) =
      expectation mu (q_eval (QIndicator c_true)) ->
    expectation mu (q_eval (QIndicator delta)) =
      expectation mu (q_eval (QIndicator c_true)) ->
    expectation mu (q_eval (QIndicator (c_and gamma delta))) =
      expectation mu (q_eval (QIndicator c_true)).
Proof.
  intros mu gamma delta Hfin Hg Hd.
  assert (Hsplit :
    expectation mu (q_eval (QIndicator gamma)) =
    (expectation mu (q_eval (QIndicator (c_and gamma delta))) +
     expectation mu (q_eval (QIndicator (c_and gamma (c_not delta)))))%R).
  { rewrite !expectation_indicator.
    rewrite <- measure_additive.
    - apply measure_extensional; intro v; unfold formula_assertion.
      rewrite !satisfies_c_and; cbn [c_not satisfies].
      split.
      + intro H; destruct (classic (satisfies v delta)); [left | right]; tauto.
      + intros [H | H]; tauto.
    - exact Hfin.
    - exact (ValuationSpace.measurable_formula_event (c_and gamma delta)).
    - exact (ValuationSpace.measurable_formula_event (c_and gamma (c_not delta))).
    - intro v; unfold formula_assertion; rewrite !satisfies_c_and;
        cbn [c_not satisfies]; tauto. }
  assert (Hrest :
    (expectation mu (q_eval (QIndicator (c_and gamma (c_not delta))))
     <= expectation mu (q_eval (QIndicator (c_not delta))))%R).
  { apply expect_indicator_mono; [exact Hfin |].
    intros v Hv; apply satisfies_c_and in Hv; tauto. }
  assert (Hup :
    (expectation mu (q_eval (QIndicator (c_and gamma delta)))
     <= expectation mu (q_eval (QIndicator c_true)))%R).
  { apply expect_indicator_mono; [exact Hfin |].
    intros v _; cbn [c_true satisfies]; tauto. }
  pose proof (expect_indicator_complement mu delta Hfin) as Hc.
  pose proof (measure_nonnegative mu
    (formula_assertion (c_and gamma (c_not delta)))) as Hnn.
  rewrite <- expectation_indicator in Hnn.
  lra.
Qed.

(** One half of the split, as an exact loop result weakened to [<=]/[>=]. *)
Lemma t2_half_pre_concentrated :
  forall (ps : Pstate) (y : ProbLogicVar) (k : nat) (gamma : CFormula),
    pstate_admissible ps ->
    (forall v, satisfies v (t2_regions k) <->
               satisfies v (c_and t2_guard gamma)) ->
    psatisfies ps (p_and (t2_eta y) (p_almost_sure gamma)) ->
    psatisfies ps (p_concentrated_mass (t2_regions k) (PVar y)).
Proof.
  intros ps y k gamma Hadm Hreg H.
  apply psatisfies_p_and in H; destruct H as [Heta Hgamma].
  unfold t2_eta in Heta; apply psatisfies_p_and in Heta.
  destruct Heta as [Hguard Hmass].
  unfold p_almost_sure in Hguard, Hgamma.
  apply psatisfies_p_eq in Hguard, Hgamma, Hmass.
  cbn [pterm_eval] in Hguard, Hgamma, Hmass.
  unfold p_concentrated_mass; apply psatisfies_p_and; split;
    apply psatisfies_p_eq; cbn [pterm_eval]; [| exact Hmass].
  rewrite (expect_indicator_iff _ (t2_regions k) (c_and t2_guard gamma) Hreg).
  apply expect_as_conj; [exact (admissible_finite ps Hadm) | exact Hguard | exact Hgamma].
Qed.

Lemma t2_regions_0_iff :
  forall v, satisfies v (t2_regions 0) <-> satisfies v (c_and t2_guard t2_pos).
Proof. intro v; exact (iff_refl _). Qed.

Lemma t2_regions_1_iff :
  forall v, satisfies v (t2_regions 1) <->
            satisfies v (c_and t2_guard (c_not t2_pos)).
Proof. intro v; exact (iff_refl _). Qed.

Lemma t2_half_le :
  forall (y : ProbLogicVar) (k : nat) (gamma : CFormula),
    (k < 2)%nat ->
    (forall v, satisfies v (t2_regions k) <->
               satisfies v (c_and t2_guard gamma)) ->
    {{ $(p_and (t2_eta y) (p_almost_sure gamma)) }}
      $(t2_loop)
    {{ y <= E[$(t2_post_q)] }}.
Proof.
  intros y k gamma Hk Hreg.
  eapply HConseq;
    [| exact (t2_loop_derivable y k Hk) |].
  - intros ps Hadm; cbn [psatisfies]; intro H.
    exact (t2_half_pre_concentrated ps y k gamma Hadm Hreg H).
  - intros ps Hadm; cbn [psatisfies]; intro H.
    apply psatisfies_p_eq in H; cbn [pterm_eval] in H |- *.
    unfold t2_solution in H; unfold t2_post_q; lra.
Qed.

Lemma t2_half_ge :
  forall (y : ProbLogicVar) (k : nat) (gamma : CFormula),
    (k < 2)%nat ->
    (forall v, satisfies v (t2_regions k) <->
               satisfies v (c_and t2_guard gamma)) ->
    {{ $(p_and (t2_eta y) (p_almost_sure gamma)) }}
      $(t2_loop)
    {{ E[$(t2_post_q)] <= y }}.
Proof.
  intros y k gamma Hk Hreg.
  eapply HConseq;
    [| exact (t2_loop_derivable y k Hk) |].
  - intros ps Hadm; cbn [psatisfies]; intro H.
    exact (t2_half_pre_concentrated ps y k gamma Hadm Hreg H).
  - intros ps Hadm; cbn [psatisfies]; intro H.
    apply psatisfies_p_eq in H; cbn [pterm_eval] in H |- *.
    unfold t2_solution in H; unfold t2_post_q; lra.
Qed.

Definition t2_sum_pre : PFormula :=
  sum_precondition (t2_eta t2_y1) (t2_eta t2_y2) t2_pos (c_not t2_pos).

Lemma t2_split_disjoint : cformula_valid (c_not (c_and t2_pos (c_not t2_pos))).
Proof.
  intro v; cbn [c_not satisfies]; intro H.
  apply satisfies_c_and in H; destruct H as [H1 H2].
  cbn [c_not satisfies] in H2; exact (H2 H1).
Qed.

Lemma t2_loop_sum_le :
  {{ $(t2_sum_pre) }} $(t2_loop) {{ t2_y1 + t2_y2 <= E[$(t2_post_q)] }}.
Proof.
  apply HSumLe.
  - exact t2_split_disjoint.
  - apply (t2_half_le t2_y1 0); [lia | exact t2_regions_0_iff].
  - apply (t2_half_le t2_y2 1); [lia | exact t2_regions_1_iff].
Qed.

Lemma t2_loop_sum_ge :
  {{ $(t2_sum_pre) }} $(t2_loop) {{ E[$(t2_post_q)] <= t2_y1 + t2_y2 }}.
Proof.
  apply HSumGe.
  - exact t2_split_disjoint.
  - apply (t2_half_ge t2_y1 0); [lia | exact t2_regions_0_iff].
  - apply (t2_half_ge t2_y2 1); [lia | exact t2_regions_1_iff].
Qed.

(** The two masses sum to one; this analytical fact survives the loop. *)
Definition t2_kappa : PFormula := [[ t2_y1 + t2_y2 = 1 ]].

Definition t2_loop_pre : PFormula := p_and t2_sum_pre t2_kappa.

Lemma t2_loop_exact :
  {{ $(t2_loop_pre) }} $(t2_loop) {{ E[$(t2_post_q)] = 1 }}.
Proof.
  eapply HConseq with
    (eta1 := t2_loop_pre)
    (eta2 := p_and
               (p_and (PFLe (PAdd (PVar t2_y1) (PVar t2_y2)) (PExpect t2_post_q))
                      (PFLe (PExpect t2_post_q) (PAdd (PVar t2_y1) (PVar t2_y2))))
               t2_kappa).
  - intros ps Hadm; cbn [psatisfies]; tauto.
  - apply HAnd; [apply HAnd |].
    + eapply HConseq; [| exact t2_loop_sum_le |].
      * intros ps Hadm; cbn [psatisfies]; intro H.
        unfold t2_loop_pre in H; apply psatisfies_p_and in H; tauto.
      * intros ps Hadm; cbn [psatisfies]; tauto.
    + eapply HConseq; [| exact t2_loop_sum_ge |].
      * intros ps Hadm; cbn [psatisfies]; intro H.
        unfold t2_loop_pre in H; apply psatisfies_p_and in H; tauto.
      * intros ps Hadm; cbn [psatisfies]; tauto.
    + eapply HConseq with (eta1 := t2_kappa) (eta2 := t2_kappa); [| apply HFree |].
      * intros ps Hadm; cbn [psatisfies]; intro H.
        unfold t2_loop_pre in H; apply psatisfies_p_and in H; tauto.
      * unfold t2_kappa; cbn [p_eq p_and p_not pformula_analytical pterm_analytical].
        tauto.
      * intros ps Hadm; cbn [psatisfies]; tauto.
  - intros ps Hadm; cbn [psatisfies]; intro H.
    apply psatisfies_p_and in H; destruct H as [Hb Hk].
    apply psatisfies_p_and in Hb; destruct Hb as [Hle Hge].
    unfold t2_kappa in Hk; apply psatisfies_p_eq in Hk.
    cbn [psatisfies pterm_eval] in Hle, Hge, Hk.
    apply psatisfies_p_eq; cbn [pterm_eval]; lra.
Qed.

(** The rigid masses are the masses of the two halves of the split. *)
Definition t2_mass1 : Pterm := PExpect (condition_pconstruct (QIndicator c_true) t2_pos).
Definition t2_mass2 : Pterm :=
  PExpect (condition_pconstruct (QIndicator c_true) (c_not t2_pos)).

Definition t2_loop_pre_closed : PFormula :=
  subst_prob_pformula t2_y1 t2_mass1
    (subst_prob_pformula t2_y2 t2_mass2 t2_loop_pre).

Lemma t2_loop_closed :
  {{ $(t2_loop_pre_closed) }} $(t2_loop) {{ E[$(t2_post_q)] = 1 }}.
Proof.
  unfold t2_loop_pre_closed.
  apply (HElimv (subst_prob_pformula t2_y2 t2_mass2 t2_loop_pre)
           (p_eq (PExpect t2_post_q) (PConst 1)) t2_y1 t2_mass1).
  - eapply HConseq with
      (eta1 := subst_prob_pformula t2_y2 t2_mass2 t2_loop_pre)
      (eta2 := p_eq (PExpect t2_post_q) (PConst 1)).
    + intros ps Hadm; cbn [psatisfies]; intro H.
      apply psatisfies_p_and in H; exact (proj1 H).
    + apply (HElimv t2_loop_pre (p_eq (PExpect t2_post_q) (PConst 1))
               t2_y2 t2_mass2).
      * eapply HConseq with
          (eta1 := t2_loop_pre) (eta2 := p_eq (PExpect t2_post_q) (PConst 1)).
        -- intros ps Hadm; cbn [psatisfies]; intro H.
           apply psatisfies_p_and in H; exact (proj1 H).
        -- exact t2_loop_exact.
        -- intros ps Hadm; cbn [psatisfies]; tauto.
      * cbn; tauto.
      * cbn; tauto.
    + intros ps Hadm; cbn [psatisfies]; tauto.
  - cbn; tauto.
  - cbn; tauto.
Qed.

(** Restricting by an almost-sure event does not change a mass. *)
Lemma expect_as_restrict :
  forall (mu : Measure) (gamma delta : CFormula),
    FiniteMeasure mu ->
    expectation mu (q_eval (QIndicator gamma)) =
      expectation mu (q_eval (QIndicator c_true)) ->
    expectation mu (q_eval (QIndicator (c_and gamma delta))) =
      expectation mu (q_eval (QIndicator delta)).
Proof.
  intros mu gamma delta Hfin Hg.
  assert (Hsplit :
    expectation mu (q_eval (QIndicator delta)) =
    (expectation mu (q_eval (QIndicator (c_and gamma delta))) +
     expectation mu (q_eval (QIndicator (c_and (c_not gamma) delta))))%R).
  { rewrite !expectation_indicator.
    rewrite <- measure_additive.
    - apply measure_extensional; intro v; unfold formula_assertion.
      rewrite !satisfies_c_and; cbn [c_not satisfies].
      split.
      + intro H; destruct (classic (satisfies v gamma)); [left | right]; tauto.
      + intros [H | H]; tauto.
    - exact Hfin.
    - exact (ValuationSpace.measurable_formula_event (c_and gamma delta)).
    - exact (ValuationSpace.measurable_formula_event (c_and (c_not gamma) delta)).
    - intro v; unfold formula_assertion; rewrite !satisfies_c_and;
        cbn [c_not satisfies]; tauto. }
  assert (Hrest :
    (expectation mu (q_eval (QIndicator (c_and (c_not gamma) delta)))
     <= expectation mu (q_eval (QIndicator (c_not gamma))))%R).
  { apply expect_indicator_mono; [exact Hfin |].
    intros v Hv; apply satisfies_c_and in Hv; tauto. }
  pose proof (expect_indicator_complement mu gamma Hfin) as Hc.
  pose proof (measure_nonnegative mu
    (formula_assertion (c_and (c_not gamma) delta))) as Hnn.
  rewrite <- expectation_indicator in Hnn.
  lra.
Qed.

Lemma t2_y1_y2_neq :
  forall (A : Type) (a c : A),
    (if prob_logic_var_eq_dec t2_y1 t2_y2 then a else c) = c.
Proof.
  intros A a c.
  destruct (prob_logic_var_eq_dec t2_y1 t2_y2) as [H | _]; [| reflexivity].
  unfold t2_y1, t2_y2 in H; inversion H.
Qed.

Lemma t2_y2_y1_neq :
  forall (A : Type) (a c : A),
    (if prob_logic_var_eq_dec t2_y2 t2_y1 then a else c) = c.
Proof.
  intros A a c.
  destruct (prob_logic_var_eq_dec t2_y2 t2_y1) as [H | _]; [| reflexivity].
  unfold t2_y1, t2_y2 in H; inversion H.
Qed.

Lemma plv_eq_dec_refl :
  forall (y : ProbLogicVar) (A : Type) (a c : A),
    (if prob_logic_var_eq_dec y y then a else c) = a.
Proof.
  intros y A a c.
  destruct (prob_logic_var_eq_dec y y); [reflexivity | contradiction].
Qed.

(** Before the loop: [b] is false almost surely and the total mass is one. *)
Definition t2_ready : PFormula := [[ almost_sure[$(t2_guard)] /\ Pr[true] = 1 ]].

Lemma t2_ready_implies_loop_pre :
  pformula_valid (PFImpl t2_ready t2_loop_pre_closed).
Proof.
  intros ps Hadm; cbn [psatisfies]; intro H.
  pose proof (admissible_finite ps Hadm) as Hfin.
  unfold t2_ready in H; apply psatisfies_p_and in H; destruct H as [Hg Hm].
  unfold p_almost_sure in Hg; apply psatisfies_p_eq in Hg, Hm.
  cbn [pterm_eval] in Hg, Hm.
  set (mu := pstate_measure ps) in *.
  assert (Hpos : expectation mu (q_eval (QIndicator (c_and t2_guard t2_pos))) =
                 expectation mu (q_eval (QIndicator (c_and c_true t2_pos)))).
  { rewrite (expect_as_restrict mu t2_guard t2_pos Hfin Hg).
    apply expect_indicator_iff; intro v; rewrite satisfies_c_and.
    cbn [c_true satisfies]; tauto. }
  assert (Hneg : expectation mu (q_eval (QIndicator (c_and t2_guard (c_not t2_pos)))) =
                 expectation mu (q_eval (QIndicator (c_and c_true (c_not t2_pos))))).
  { rewrite (expect_as_restrict mu t2_guard (c_not t2_pos) Hfin Hg).
    apply expect_indicator_iff; intro v; rewrite satisfies_c_and.
    cbn [c_true satisfies]; tauto. }
  assert (Hcover : expectation mu (q_eval (QIndicator (c_or t2_pos (c_not t2_pos)))) =
                   expectation mu (q_eval (QIndicator c_true))).
  { apply expect_indicator_iff; intro v; cbn [c_or c_not c_true satisfies]; tauto. }
  assert (Hsum : (expectation mu (q_eval (QIndicator (c_and c_true t2_pos))) +
                  expectation mu (q_eval (QIndicator (c_and c_true (c_not t2_pos)))))%R = 1%R).
  { rewrite (expect_indicator_iff mu (c_and c_true t2_pos) t2_pos)
      by (intro v; rewrite satisfies_c_and; cbn [c_true satisfies]; tauto).
    rewrite (expect_indicator_iff mu (c_and c_true (c_not t2_pos)) (c_not t2_pos))
      by (intro v; rewrite satisfies_c_and; cbn [c_true satisfies]; tauto).
    rewrite (expect_indicator_complement mu t2_pos Hfin); exact Hm. }
  unfold t2_loop_pre_closed, t2_loop_pre, t2_sum_pre, sum_precondition,
    t2_kappa, t2_eta, t2_mass1, t2_mass2, p_almost_sure.
  cbn [subst_prob_pformula subst_prob_pterm p_and p_not p_eq
       condition_pformula condition_pterm].
  rewrite ?t2_y1_y2_neq, ?t2_y2_y1_neq, ?plv_eq_dec_refl.
  cbn [subst_prob_pformula subst_prob_pterm].
  rewrite ?t2_y1_y2_neq, ?t2_y2_y1_neq, ?plv_eq_dec_refl.
  cbn [condition_pconstruct condition_pconstruct_fuel pconstruct_size].
  cbn [psatisfies pterm_eval].
  fold mu.
  rewrite Hpos, Hneg, Hcover.
  set (e1 := expectation mu (q_eval (QIndicator (c_and c_true t2_pos)))) in *.
  set (e2 := expectation mu (q_eval (QIndicator (c_and c_true (c_not t2_pos))))) in *.
  set (et := expectation mu (q_eval (QIndicator c_true))) in *.
  pose proof (Rle_refl e1); pose proof (Rle_refl e2); pose proof (Rle_refl et).
  assert (S1 : (e1 + e2 <= 1)%R) by lra.
  assert (S2 : (1 <= e1 + e2)%R) by lra.
  tauto.
Qed.

(** The whole program. *)
Theorem t2_prog_correct :
  forall s : R,
    (0 < s)%R ->
    {{ Pr[true] = 1 }}
      $(t2_prog s)
    {{ E[$(condition_pconstruct t2_q (c_not t2_guard))] = 1 }}.
Proof.
  intros s Hs.
  unfold t2_prog.
  eapply HSeq with (eta2 := subst_bool_pformula t2_b FFalse t2_ready).
  - apply HRealSample.
    + intros ps Hadm; cbn [psatisfies]; intro Hpre.
      apply psatisfies_p_eq in Hpre; cbn [pterm_eval] in Hpre.
      unfold t2_ready, t2_guard, p_almost_sure.
      rewrite subst_bool_pformula_p_and, !subst_bool_pformula_p_eq.
      rewrite sample_pformula_p_and, !sample_pformula_p_eq.
      apply psatisfies_p_and; split; apply psatisfies_p_eq.
      * cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_pconstruct_fuel
             pconstruct_size subst_bool_cformula c_not sample_pterm pterm_eval].
        rewrite !bpv_eq_dec_refl.
        unfold t2_noise.
        rewrite (expect_laplace_integral_valid _ _ _ _ (FImpl FFalse FFalse))
          by (exact Hs || (intro v; cbn [satisfies]; tauto)).
        rewrite (expect_laplace_integral_valid _ _ _ _ c_true)
          by (exact Hs || (intro v; cbn [c_true satisfies]; tauto)).
        reflexivity.
      * cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_pconstruct_fuel
             pconstruct_size subst_bool_cformula sample_pterm pterm_eval].
        unfold t2_noise.
        rewrite (expect_laplace_integral_valid _ _ _ _ c_true)
          by (exact Hs || (intro v; cbn [c_true satisfies]; tauto)).
        exact Hpre.
    + intros ps Hadm _.
      refine (p_almost_sure_of_pointwise _ _ ps Hadm).
      intro v.
      unfold t2_noise.
      cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
      intro Hle; lra.
  - eapply HSeq with (eta2 := t2_ready).
    + apply HBoolAssign.
    + eapply HConseq with (eta1 := t2_loop_pre_closed)
        (eta2 := p_eq (PExpect t2_post_q) (PConst 1)).
      * exact t2_ready_implies_loop_pre.
      * exact t2_loop_closed.
      * intros ps Hadm; cbn [psatisfies]; tauto.
Qed.
