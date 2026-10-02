(**
  PersistentSampleLoop.v -- a loop whose BODY branches on a continuously sampled value.

      x <- sample(Laplace(0, s));
      b <- ff;
      while ~b do
        if (0 <= x) then toss(b, 1/2) else toss(b, 1/4)

  THE TRIPLES.  Proved ([t2_loop_derivable], for [k < 2]):

      { all mass on region k, total y }   t2_loop   { Pr[b] = 1 * y }

  NOT proved, and provably out of reach ([t2_prog_target]):

      { E[1_tt] = 1 }   t2_prog s   { Pr[b] = 1 }

  Still the DiPWhile shape: nothing inside the loop samples, and nothing
  inside assigns a real variable.  But unlike SampleBeforeLoop.v the loop is no longer
  independent of [x] -- the exit rate is 1/2 on one side of the sample and
  1/4 on the other, so the conditional inside the body has to be crossed by
  [HIfEq] within [HWhile]'s body premise.

  WHAT IS PROVED HERE.  The loop triple, for each region: starting with all
  mass on one side of the sample, the loop terminates almost surely.  Both
  sides give solution 1, by different linear systems.

  WHAT IS NOT, AND WHY.  The whole program is NOT derivable, and the
  obstruction is sharp enough to state exactly.  [HWhile]'s precondition is
  [p_concentrated_mass (regions k) y]: the ENTIRE measure must sit in a
  single region.  Two horns, and both are closed:

    - Let the regions mention [x] (as they do below).  Then the body premise
      goes through, because within a region the branch masses are known --
      one branch gets everything, the other gets a null set.  But after
      [sample(Laplace(0,s))] the measure is split evenly across [0 <= x] and
      [x < 0], so it satisfies neither [p_concentrated_mass] and the loop
      cannot be entered.

    - Let the regions ignore [x], so entry is fine.  Then the body premise
      fails: from "all mass on [~b], total 1" the split between the branches
      is unknown, so [HIfEq] cannot name the two branch masses and the
      transition probabilities are not constants.

  The missing rule is [SUM], which splits a measure along disjoint regions,
  proves each part, and recombines.  It is in Fig. 9 of the draft and is not
  encoded in CPHL.v.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import ClassicalDescription.
From Stdlib Require Import Classical.
Require Import CPHL.
Require Import SampleBeforeLoop.
Require Import SVT.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * Measure monotonicity

    Derivable from finite additivity and non-negativity, and needed to turn
    "all mass on [gamma]" into "all mass on any superset of [gamma]". *)

Lemma measure_mono :
  forall (mu : Measure) (A B : Assertion),
    (forall v : state, A v -> B v) ->
    (measure_of mu A <= measure_of mu B)%R.
Proof.
  intros mu A B Hsub.
  assert (Hsplit :
    measure_of mu B =
    (measure_of mu A + measure_of mu (fun v => B v /\ ~ A v))%R).
  { rewrite <- measure_additive.
    - apply measure_extensional; intro v; split.
      + intro Hb; destruct (classic (A v)) as [Ha | Ha]; tauto.
      + intro H; destruct H as [Ha | Hrest].
        * apply Hsub; exact Ha.
        * destruct Hrest as [Hb Hna]; exact Hb.
    - intro v; tauto. }
  rewrite Hsplit.
  pose proof (measure_nonnegative mu (fun v => B v /\ ~ A v)) as Hpos.
  lra.
Qed.

Lemma expect_indicator_mono :
  forall (mu : Measure) (gamma delta : CFormula),
    (forall v : state, satisfies v gamma -> satisfies v delta) ->
    (expectation mu (q_eval (QIndicator gamma))
     <= expectation mu (q_eval (QIndicator delta)))%R.
Proof.
  intros mu gamma delta Hsub.
  rewrite !expectation_indicator.
  apply measure_mono; exact Hsub.
Qed.

(** Complementary events split the total mass. *)
Lemma expect_indicator_complement :
  forall (mu : Measure) (gamma : CFormula),
    (expectation mu (q_eval (QIndicator gamma)) +
     expectation mu (q_eval (QIndicator (c_not gamma))))%R =
    expectation mu (q_eval (QIndicator c_true)).
Proof.
  intros mu gamma.
  rewrite !expectation_indicator.
  rewrite <- measure_additive
    by (intro v; unfold formula_assertion; cbn [c_not satisfies]; tauto).
  apply measure_extensional; intro v.
  unfold formula_assertion; cbn [c_true c_not satisfies]; tauto.
Qed.

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
    psatisfies ps (p_concentrated_mass region (PConst 1)) ->
    (forall v : state, satisfies v region -> satisfies v gamma) ->
    expectation (pstate_measure ps) (q_eval (QIndicator gamma)) = 1%R /\
    expectation (pstate_measure ps)
      (q_eval (QIndicator (c_not gamma))) = 0%R.
Proof.
  intros ps region gamma Hconc Hsub.
  apply psatisfies_p_and in Hconc.
  destruct Hconc as [Hall Hmass].
  apply psatisfies_p_eq in Hall; apply psatisfies_p_eq in Hmass.
  cbn [pterm_eval] in Hall, Hmass.
  assert (Hlow : (1 <= expectation (pstate_measure ps)
                        (q_eval (QIndicator gamma)))%R).
  { rewrite <- Hmass, <- Hall.
    apply expect_indicator_mono; exact Hsub. }
  assert (Hhigh : (expectation (pstate_measure ps)
                     (q_eval (QIndicator gamma)) <= 1)%R).
  { rewrite <- Hmass.
    apply expect_indicator_mono.
    intros v _; cbn [c_true satisfies]; tauto. }
  pose proof (expect_indicator_complement (pstate_measure ps) gamma) as Hc.
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
       subst_bool_cformula c_and c_not pterm_eval];
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
  - intro ps.
  - intro Hadm.
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
    psatisfies ps (p_concentrated_mass (t2_regions 0) (PConst 1)) ->
    expectation (pstate_measure ps) (q_eval (QIndicator t2_pos)) = 1%R /\
    expectation (pstate_measure ps)
      (q_eval (QIndicator (c_not t2_pos))) = 0%R.
Proof.
  intros ps Hconc.
  apply (concentrated_superset ps (t2_regions 0) t2_pos Hconc).
  intros v Hv.
  unfold t2_regions in Hv; cbn [Nat.eqb] in Hv.
  apply satisfies_c_and in Hv; tauto.
Qed.

Lemma t2_region_values_1 :
  forall ps : Pstate,
    psatisfies ps (p_concentrated_mass (t2_regions 1) (PConst 1)) ->
    expectation (pstate_measure ps) (q_eval (QIndicator t2_pos)) = 0%R /\
    expectation (pstate_measure ps)
      (q_eval (QIndicator (c_not t2_pos))) = 1%R.
Proof.
  intros ps Hconc.
  assert (Hsup :
    expectation (pstate_measure ps)
      (q_eval (QIndicator (c_not t2_pos))) = 1%R /\
    expectation (pstate_measure ps)
      (q_eval (QIndicator (c_not (c_not t2_pos)))) = 0%R).
  { apply (concentrated_superset ps (t2_regions 1) (c_not t2_pos) Hconc).
    intros v Hv.
    unfold t2_regions in Hv; cbn [Nat.eqb] in Hv.
    apply satisfies_c_and in Hv; tauto. }
  destruct Hsup as [Hn1 _].
  apply psatisfies_p_and in Hconc.
  destruct Hconc as [_ Hmass].
  apply psatisfies_p_eq in Hmass.
  cbn [pterm_eval] in Hmass.
  pose proof (expect_indicator_complement (pstate_measure ps) t2_pos) as Hc.
  split; lra.
Qed.

(** * The body premise, for both regions

    Four components: the trivial [p_true], the two transition
    probabilities, and the exit probability.  Each of the last three is one
    application of [t2_body_event]. *)

Definition t2_exit_event : CFormula := <{ true /\ (~ $(t2_guard)) }>.

Ltac t2_event r1 r2 vals :=
  apply (t2_body_event _ _ r1 r2);
  [ intro ps; cbn [psatisfies]; intro Hconc;
    lazymatch goal with
    | Hc : psatisfies _ (p_concentrated_mass _ _) |- _ =>
        destruct (vals _ Hc) as [Hpos Hneg]
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
             [ intro ps; cbn [psatisfies]; intro Hx; apply psatisfies_p_true
             | apply HFree; cbn [p_true pformula_analytical]; tauto
             | intro ps; cbn [psatisfies]; tauto ].
        -- t2_event (1/2)%R 0%R t2_region_values_0.
      * t2_event 0%R 0%R t2_region_values_0.
    + t2_event (1/2)%R 0%R t2_region_values_0.
  - apply HAnd.
    + apply HAnd.
      * apply HAnd.
        -- eapply HConseq with (eta1 := p_true) (eta2 := p_true);
             [ intro ps; cbn [psatisfies]; intro Hx; apply psatisfies_p_true
             | apply HFree; cbn [p_true pformula_analytical]; tauto
             | intro ps; cbn [psatisfies]; tauto ].
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
  forall k : nat,
    (k < 2)%nat ->
    hoare_derivable
      (p_concentrated_mass (t2_regions k) (PVar t2_y))
      t2_loop
      (p_eq (PExpect (condition_pconstruct t2_q (c_not t2_guard)))
         (PMul (PConst (t2_solution k)) (PVar t2_y))).
Proof.
  intros k Hk.
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

Lemma laplace_cdf_centre :
  forall s : R, (0 < s)%R -> laplace_cdf 0 s 0 = (1 / 2)%R.
Proof.
  intros s Hs.
  unfold laplace_cdf.
  destruct (Rle_dec 0 0) as [_ | Hno]; [| lra].
  replace ((0 - 0) / s)%R with 0%R by (field; lra).
  rewrite exp_0; ring.
Qed.

(** A centred Laplace puts exactly half its mass on each side of 0. *)
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
  - intro ps.
  - intro Hadm.
    cbn [psatisfies].
    intro Hpre.
    apply psatisfies_p_eq in Hpre.
    cbn [pterm_eval] in Hpre.
    rewrite sample_pformula_p_eq.
    apply psatisfies_p_eq.
    cbn [sample_pterm pterm_eval].
    transitivity
      (expectation (pstate_measure ps) (fun _ : state => (1 / 2)%R)).
    + apply expectation_extensional; intro v.
      cbn [q_eval t2_noise distribution_density term_eval t2_pos].
      rewrite (real_integral_extensional
                 _ (fun z =>
                      ((1 / (2 * s)) * exp (- Rabs (z - 0) / s)) *
                      real_indicator (0 <= z)%R)).
      * rewrite laplace_integral_survival by exact Hs.
        rewrite laplace_cdf_centre by exact Hs; lra.
      * intro z.
        unfold t2_pos, update_real, update_real_values.
        cbn [satisfies term_eval real_program_values].
        rewrite rpv_eq_dec_refl.
        ring.
    + rewrite expectation_constant, Hpre; lra.
  - intros ps _.
    revert ps.
    apply p_almost_sure_of_pointwise.
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
    expectation (pstate_measure ps) (q_eval (QIndicator c_true)) = 1%R ->
    expectation (pstate_measure ps) (q_eval (QIndicator t2_pos)) =
      (1 / 2)%R ->
    ~ psatisfies ps (p_concentrated_mass (t2_regions 0) (PVar t2_y)) /\
    ~ psatisfies ps (p_concentrated_mass (t2_regions 1) (PVar t2_y)).
Proof.
  intros ps Htot Hhalf.
  pose proof (expect_indicator_complement (pstate_measure ps) t2_pos) as Hc.
  split; intro Hconc; apply psatisfies_p_and in Hconc;
    destruct Hconc as [Hall _]; apply psatisfies_p_eq in Hall;
    cbn [pterm_eval] in Hall.
  - assert (Hle :
      (expectation (pstate_measure ps)
         (q_eval (QIndicator (t2_regions 0)))
       <= expectation (pstate_measure ps) (q_eval (QIndicator t2_pos)))%R).
    { apply expect_indicator_mono.
      intros v Hv.
      unfold t2_regions in Hv; cbn [Nat.eqb] in Hv.
      apply satisfies_c_and in Hv; tauto. }
    lra.
  - assert (Hle :
      (expectation (pstate_measure ps)
         (q_eval (QIndicator (t2_regions 1)))
       <= expectation (pstate_measure ps)
            (q_eval (QIndicator (c_not t2_pos))))%R).
    { apply expect_indicator_mono.
      intros v Hv.
      unfold t2_regions in Hv; cbn [Nat.eqb] in Hv.
      apply satisfies_c_and in Hv; tauto. }
    lra.
Qed.

(** The whole-program triple, stated but NOT proved.  By
    [t2_sample_splits] and [t2_split_blocks_entry] the post-sample state
    satisfies neither [p_concentrated_mass], so no instance of [HWhile]
    applies to [t2_loop] in this context.  Closing this needs [SUM]. *)
Definition t2_prog_target (s : R) : Prop :=
  {{ Pr[true] = 1 }}
    $(t2_prog s)
  {{ E[$(condition_pconstruct t2_q (c_not t2_guard))] = 1 }}.
