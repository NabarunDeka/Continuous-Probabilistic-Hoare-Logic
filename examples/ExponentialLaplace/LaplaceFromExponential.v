(**
  LaplaceFromExponential.v

  Program ([lp_prog]):

      s <- toss(1/2);
      if s then z := e else z := (-1) * e

  Triple ([lp_sign_mixture], for all fe, se, t):

      { Pr[e < t] = fe /\ Pr[(-1) * e < t] = se }
        lp_prog
      { Pr[z < t] = (fe + se) / 2 }

  Triple ([lp_laplace_from_exponential], for 0 < b and all t):

      { Pr[e < t] = E[ integral w ~ exponential(1/b), 1_(w < t) ]
        /\ Pr[(-1) * e < t] = E[ integral w ~ exponential(1/b), 1_((-1) * w < t) ] }
        lp_prog
      { Pr[z < t] = E[ integral w ~ laplace(0, b), 1_(w < t) ] }
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import ClassicalDescription.
From Stdlib Require Import Classical.
Require Import CPHL.
Require Import MeasureIntegration.
Require Import SampleBeforeLoop.
Require Import PersistentSampleLoop.
Require Import HalfLaplaceRejection.
Require Import SVT.
Require Import CdfAssertions.
Require Import AltExpLaplaceFacts.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * The program *)

Definition lp_e : RealProgramVar := real_program_var "lp_e".
Definition lp_z : RealProgramVar := real_program_var "lp_z".
Definition lp_s : BoolProgramVar := bool_program_var "lp_s".

(** [Term] has no unary minus; [TMul] against the constant [-1] is how a
    negation is written. *)
Definition lp_minus_one : Term := TConst (-1).
Definition lp_negate : Term := <{ $(lp_minus_one) * lp_e }>.

Definition lp_prog : Cmd :=
  <{ lp_s toss $(1 / 2);
     if lp_s then lp_z := lp_e else lp_z := $(lp_negate) end }>.

(** The output event, and the two source events it is built from. *)
Definition lp_below (t : R) : CFormula := <{ lp_z < t }>.
Definition lp_src_below (t : R) : CFormula := <{ lp_e < t }>.
Definition lp_src_above (t : R) : CFormula := <{ $(lp_negate) < t }>.

(** * Indicator bookkeeping for the coin

    [toss_pformula] duplicates every expectation, substituting [true] into
    one copy and [false] into the other.  Each copy meets the [if]'s guard
    conjunct and collapses. *)

Lemma lp_satisfies_and :
  forall (v : state) (g1 g2 : CFormula),
    satisfies v (c_and g1 g2) <-> (satisfies v g1 /\ satisfies v g2).
Proof. exact satisfies_c_and. Qed.

Lemma lp_expect_and_true :
  forall (mu : Measure) (gamma : CFormula),
    expectation mu (q_eval (QIndicator (c_and gamma c_true))) =
    expectation mu (q_eval (QIndicator gamma)).
Proof.
  intros mu gamma.
  apply expectation_extensional; intro v.
  rewrite !q_eval_indicatorE.
  apply real_indicator_extensional.
  rewrite lp_satisfies_and.
  unfold c_true, c_not.
  cbn [satisfies].
  tauto.
Qed.

Lemma lp_expect_and_false :
  forall (mu : Measure) (gamma : CFormula),
    expectation mu (q_eval (QIndicator (c_and gamma FFalse))) = 0%R.
Proof.
  intros mu gamma.
  apply expect_indicator_unsat; intro v.
  rewrite lp_satisfies_and.
  cbn [satisfies].
  tauto.
Qed.

Lemma lp_expect_and_not_true :
  forall (mu : Measure) (gamma : CFormula),
    expectation mu (q_eval (QIndicator (c_and gamma (c_not c_true)))) = 0%R.
Proof.
  intros mu gamma.
  apply expect_indicator_unsat; intro v.
  rewrite lp_satisfies_and.
  unfold c_true, c_not.
  cbn [satisfies].
  tauto.
Qed.

Lemma lp_expect_and_not_false :
  forall (mu : Measure) (gamma : CFormula),
    expectation mu (q_eval (QIndicator (c_and gamma (c_not FFalse)))) =
    expectation mu (q_eval (QIndicator gamma)).
Proof.
  intros mu gamma.
  apply expectation_extensional; intro v.
  rewrite !q_eval_indicatorE.
  apply real_indicator_extensional.
  rewrite lp_satisfies_and.
  unfold c_not.
  cbn [satisfies].
  tauto.
Qed.

(** These three are definitional: [condition_pformula], [toss_pformula] and
    the [p_and] encoding all commute with the shapes used here, so each is a
    [reflexivity].  Having them as rewrite rules keeps the main proof from
    drowning in [cbn] invocations. *)

Lemma lp_condition_p_eq_const :
  forall (c : R) (gamma guard : CFormula),
    condition_pformula (p_eq (PConst c) (PExpect (QIndicator gamma))) guard =
    p_eq (PConst c) (PExpect (QIndicator (c_and gamma guard))).
Proof. reflexivity. Qed.

Lemma lp_toss_p_and :
  forall (b : BoolProgramVar) (r : R) (eta1 eta2 : PFormula),
    toss_pformula b r (p_and eta1 eta2) =
    p_and (toss_pformula b r eta1) (toss_pformula b r eta2).
Proof. reflexivity. Qed.

Lemma lp_toss_p_eq_const :
  forall (b : BoolProgramVar) (r c : R) (q : PConstruct),
    toss_pformula b r (p_eq (PConst c) (PExpect q)) =
    p_eq (PConst c)
      (PAdd (PMul (PConst r) (PExpect (subst_bool_pconstruct b c_true q)))
         (PMul (PConst (1 - r))
            (PExpect (subst_bool_pconstruct b FFalse q)))).
Proof. reflexivity. Qed.

(** The coin substitutes [true] into one copy of each expectation and
    [false] into the other.  Both variables are concrete, so each resulting
    formula is reached by [reflexivity] -- stating them as rewrite rules
    avoids a [cbn] that would unfold the [c_and]/[c_true] encodings and
    leave nothing for the expectation lemmas above to match. *)

Lemma lp_subst_lo_true :
  forall t : R,
    subst_bool_pconstruct lp_s c_true
      (QIndicator (c_and (lp_src_below t) (FProgBool lp_s))) =
    QIndicator (c_and (lp_src_below t) c_true).
Proof. reflexivity. Qed.

Lemma lp_subst_lo_false :
  forall t : R,
    subst_bool_pconstruct lp_s FFalse
      (QIndicator (c_and (lp_src_below t) (FProgBool lp_s))) =
    QIndicator (c_and (lp_src_below t) FFalse).
Proof. reflexivity. Qed.

Lemma lp_subst_hi_true :
  forall t : R,
    subst_bool_pconstruct lp_s c_true
      (QIndicator (c_and (lp_src_above t) (c_not (FProgBool lp_s)))) =
    QIndicator (c_and (lp_src_above t) (c_not c_true)).
Proof. reflexivity. Qed.

Lemma lp_subst_hi_false :
  forall t : R,
    subst_bool_pconstruct lp_s FFalse
      (QIndicator (c_and (lp_src_above t) (c_not (FProgBool lp_s)))) =
    QIndicator (c_and (lp_src_above t) (c_not FFalse)).
Proof. reflexivity. Qed.

(** * The two branches

    Each is a real assignment, so [HRealAssign] applies once the
    postcondition is written as a substitution instance. *)

Lemma lp_then_branch :
  forall r t : R,
    hoare_derivable
      (svt_event_probability r (lp_src_below t))
      (CRealAssign lp_z (TProgVar lp_e))
      (svt_event_probability r (lp_below t)).
Proof.
  intros r t.
  replace (svt_event_probability r (lp_src_below t))
    with (subst_real_pformula lp_z (TProgVar lp_e)
           (svt_event_probability r (lp_below t))).
  - apply HRealAssign.
  - unfold svt_event_probability, lp_below, lp_src_below, p_eq, c_lt.
    cbn [subst_real_pformula subst_real_pterm subst_real_pconstruct
         subst_real_cformula subst_real_term].
    try rewrite rpv_eq_dec_refl.
    reflexivity.
Qed.

Lemma lp_else_branch :
  forall r t : R,
    hoare_derivable
      (svt_event_probability r (lp_src_above t))
      (CRealAssign lp_z lp_negate)
      (svt_event_probability r (lp_below t)).
Proof.
  intros r t.
  replace (svt_event_probability r (lp_src_above t))
    with (subst_real_pformula lp_z lp_negate
           (svt_event_probability r (lp_below t))).
  - apply HRealAssign.
  - unfold svt_event_probability, lp_below, lp_src_above, p_eq, c_lt.
    cbn [subst_real_pformula subst_real_pterm subst_real_pconstruct
         subst_real_cformula subst_real_term].
    try rewrite rpv_eq_dec_refl.
    reflexivity.
Qed.

(** * The conditional

    [svt_if_constants] is SVT.v's exact conditional rule: rigid variables
    record the two branch masses, [HIfEq] adds them.  Both branch
    preconditions here are constant-valued, so the auxiliary substitutions
    it introduces are identities. *)

Lemma lp_if_step :
  forall r1 r2 t : R,
    hoare_derivable
      (if_precondition
         (svt_event_probability r1 (lp_src_below t))
         (svt_event_probability r2 (lp_src_above t))
         (FProgBool lp_s))
      (CIf (FProgBool lp_s)
         (CRealAssign lp_z (TProgVar lp_e))
         (CRealAssign lp_z lp_negate))
      (svt_event_probability (r1 + r2) (lp_below t)).
Proof.
  intros r1 r2 t.
  pose proof
    (svt_if_constants
       (svt_event_probability r1 (lp_src_below t))
       (svt_event_probability r2 (lp_src_above t))
       (FProgBool lp_s) (lp_below t)
       (CRealAssign lp_z (TProgVar lp_e))
       (CRealAssign lp_z lp_negate)
       r1 r2
       (lp_then_branch r1 t) (lp_else_branch r2 t)) as H.
  cbn [subst_prob_pformula subst_prob_pterm if_precondition
       condition_pformula condition_pterm
       svt_event_probability p_eq p_and p_not] in H.
  exact H.
Qed.

(** * The mixture lemma

    Nothing exponential here: for ANY [fe] and [se], the fair sign averages
    the source's lower tail with the reflected upper tail. *)

Theorem lp_sign_mixture :
  forall fe se t : R,
    {{ (Pr[$(lp_src_below t)] = $(fe)) /\ (Pr[$(lp_src_above t)] = $(se)) }}
      $(lp_prog)
    {{ Pr[$(lp_below t)] = $((fe + se) / 2) }}.
Proof.
  intros fe se t.
  unfold lp_prog.
  set (P :=
    if_precondition
      (svt_event_probability (fe / 2) (lp_src_below t))
      (svt_event_probability (se / 2) (lp_src_above t))
      (FProgBool lp_s)).
  eapply HConseq with
    (eta1 := toss_pformula lp_s (1 / 2) P)
    (eta2 := svt_event_probability (fe / 2 + se / 2) (lp_below t)).
  - (* the precondition entails the tossed formula *)
    intro ps.
    intro Hadm.
    intro Hpre.
    apply psatisfies_p_and in Hpre.
    destruct Hpre as [Hlo Hhi].
    apply psatisfies_p_eq in Hlo.
    apply psatisfies_p_eq in Hhi.
    cbn [pterm_eval] in Hlo, Hhi.
    unfold P, if_precondition, svt_event_probability.
    rewrite !lp_condition_p_eq_const.
    rewrite lp_toss_p_and, !lp_toss_p_eq_const.
    apply psatisfies_p_and; split; apply psatisfies_p_eq;
      cbn [pterm_eval].
    + rewrite lp_subst_lo_true, lp_subst_lo_false.
      rewrite lp_expect_and_true, lp_expect_and_false, Hlo; lra.
    + rewrite lp_subst_hi_true, lp_subst_hi_false.
      rewrite lp_expect_and_not_true, lp_expect_and_not_false, Hhi; lra.
  - eapply HSeq with (eta2 := P).
    + apply HBoolToss.
      unfold coin_probability_valid; lra.
    + apply lp_if_step.
  - (* the summed post is the stated one, with the operands flipped *)
    intro ps.
    intro Hadm.
    unfold svt_event_probability.
    intro Hpost.
    apply psatisfies_p_eq in Hpost.
    cbn [pterm_eval] in Hpost.
    apply psatisfies_p_eq.
    cbn [pterm_eval].
    lra.
Qed.

(** * The exponential source and the Laplace target, as assertion terms

    [lp_w] is the integration variable.  Each construct is the tail
    probability of one distribution, written in the assertion logic. *)

Definition lp_w : RealProgramVar := real_program_var "lp_w".

Definition lp_exp_dist (b : R) : Distribution := Exponential (TConst (/ b)).
Definition lp_lap_dist (b : R) : Distribution := Laplace (TConst 0) (TConst b).

Definition lp_w_below (t : R) : CFormula := <{ lp_w < t }>.
Definition lp_w_reflected (t : R) : CFormula :=
  <{ $(lp_minus_one) * lp_w < t }>.

(** [E[integral w ~ exponential(1/b), 1_(w < t)]]. *)
Definition lp_exp_below (b t : R) : PConstruct :=
  QIntegral lp_w (lp_exp_dist b) (QIndicator (lp_w_below t)).

(** [E[integral w ~ exponential(1/b), 1_((-1) * w < t)]]. *)
Definition lp_exp_reflected (b t : R) : PConstruct :=
  QIntegral lp_w (lp_exp_dist b) (QIndicator (lp_w_reflected t)).

(** [E[integral w ~ laplace(0, b), 1_(w < t)]]. *)
Definition lp_lap_below (b t : R) : PConstruct :=
  QIntegral lp_w (lp_lap_dist b) (QIndicator (lp_w_below t)).

Definition lp_pre (b t : R) : PFormula :=
  p_and
    (p_eq (PExpect (QIndicator (lp_src_below t))) (PExpect (lp_exp_below b t)))
    (p_eq (PExpect (QIndicator (lp_src_above t))) (PExpect (lp_exp_reflected b t))).

Definition lp_post (b t : R) : PFormula :=
  p_eq (PExpect (QIndicator (lp_below t))) (PExpect (lp_lap_below b t)).

(** * Evaluating the three constructs *)

Lemma lp_update_w :
  forall (v : state) (r : R),
    real_program_values (update_real v lp_w r) lp_w = r.
Proof.
  intros v r.
  pose proof (update_real_same v lp_w r) as H.
  cbn [term_eval] in H; exact H.
Qed.

Lemma lp_sat_w_below :
  forall (v : state) (t r : R),
    satisfies (update_real v lp_w r) (lp_w_below t) <-> (r < t)%R.
Proof.
  intros v t r.
  unfold lp_w_below, c_lt, c_not.
  cbn [satisfies term_eval]; rewrite lp_update_w.
  split; [intro H; apply Rnot_le_lt; exact H | intros H H'; lra].
Qed.

Lemma lp_sat_w_reflected :
  forall (v : state) (t r : R),
    satisfies (update_real v lp_w r) (lp_w_reflected t) <-> ~ (t <= -1 * r)%R.
Proof.
  intros v t r.
  unfold lp_w_reflected, lp_minus_one, c_lt, c_not.
  cbn [satisfies term_eval]; rewrite lp_update_w.
  tauto.
Qed.

Lemma lp_exp_pos : forall b : R, (0 < b)%R -> (0 < / b)%R.
Proof. intros b Hb; apply Rinv_0_lt_compat; exact Hb. Qed.

Lemma lp_qeval_exp_below :
  forall (b t : R) (v : state),
    (0 < b)%R -> q_eval (lp_exp_below b t) v = altexp_below b t.
Proof.
  intros b t v Hb.
  apply q_eval_exponential_indicator; [apply lp_exp_pos; exact Hb |].
  intro r; apply lp_sat_w_below.
Qed.

Lemma lp_qeval_exp_reflected :
  forall (b t : R) (v : state),
    (0 < b)%R -> q_eval (lp_exp_reflected b t) v = altexp_reflected b t.
Proof.
  intros b t v Hb.
  apply q_eval_exponential_indicator; [apply lp_exp_pos; exact Hb |].
  intro r; apply lp_sat_w_reflected.
Qed.

Lemma lp_qeval_lap_below :
  forall (b t : R) (v : state),
    (0 < b)%R -> q_eval (lp_lap_below b t) v = lap_below 0 b t.
Proof.
  intros b t v Hb.
  apply q_eval_laplace_indicator; [exact Hb |].
  intro r; apply lp_sat_w_below.
Qed.

(** In every state the two exponential terms add up to twice the Laplace
    term: each is a constant times the total mass. *)
Lemma lp_expect_mixture :
  forall (b t : R) (mu : Measure),
    (0 < b)%R ->
    (expectation mu (q_eval (lp_exp_below b t)) +
     expectation mu (q_eval (lp_exp_reflected b t)) =
     2 * expectation mu (q_eval (lp_lap_below b t)))%R.
Proof.
  intros b t mu Hb.
  rewrite (expect_const_construct mu (lp_exp_below b t) (altexp_below b t))
    by (intro v; apply lp_qeval_exp_below; exact Hb).
  rewrite (expect_const_construct mu (lp_exp_reflected b t) (altexp_reflected b t))
    by (intro v; apply lp_qeval_exp_reflected; exact Hb).
  rewrite (expect_const_construct mu (lp_lap_below b t) (lap_below 0 b t))
    by (intro v; apply lp_qeval_lap_below; exact Hb).
  pose proof (altexp_mixture b Hb t) as Hm.
  replace (lap_below 0 b t) with ((altexp_below b t + altexp_reflected b t) / 2)%R
    by (rewrite Hm; field).
  field.
Qed.

(** The Laplace term, conditioned on a valid or an unsatisfiable formula. *)
Lemma lp_expect_lap_and_valid :
  forall (b t : R) (mu : Measure) (g : CFormula),
    (forall v : state, satisfies v g) ->
    expectation mu
      (q_eval (QIntegral lp_w (lp_lap_dist b) (QIndicator (c_and (lp_w_below t) g)))) =
    expectation mu (q_eval (lp_lap_below b t)).
Proof.
  intros b t mu g Hg.
  apply expectation_extensional; intro v.
  unfold lp_lap_below.
  apply q_integral_indicator_ext; intro w.
  rewrite satisfies_c_and; split; [tauto | intro H; split; [exact H | apply Hg] ].
Qed.

Lemma lp_expect_lap_and_unsat :
  forall (b t : R) (mu : Measure) (g : CFormula),
    (0 < b)%R ->
    (forall v : state, ~ satisfies v g) ->
    expectation mu
      (q_eval (QIntegral lp_w (lp_lap_dist b) (QIndicator (c_and (lp_w_below t) g)))) =
    0%R.
Proof.
  intros b t mu g Hb Hg.
  rewrite (expect_const_construct mu _ 0%R); [ring |].
  intro v; unfold lp_lap_dist.
  rewrite (q_eval_laplace_indicator lp_w 0 b _ (fun _ => False) v Hb).
  - rewrite <- real_integral_zero.
    apply real_integral_extensional; intro r.
    rewrite (real_indicator_false False) by tauto; ring.
  - intro r; rewrite satisfies_c_and; split; [intros [_ H]; exact (Hg _ H) | tauto].
Qed.

(** * The conditional, with rigid variables

    [y1], [y2] record the two branch masses of the event [z < t]; [y3], [y4]
    record the two branch masses of the Laplace term, which no branch
    changes. *)

Definition lp_y1 : ProbLogicVar := prob_logic_var "lp_y1".
Definition lp_y2 : ProbLogicVar := prob_logic_var "lp_y2".
Definition lp_y3 : ProbLogicVar := prob_logic_var "lp_y3".
Definition lp_y4 : ProbLogicVar := prob_logic_var "lp_y4".

Definition lp_rigid (y : ProbLogicVar) (q : PConstruct) : PFormula :=
  p_eq (PVar y) (PExpect q).

Definition lp_if : Cmd :=
  CIf (FProgBool lp_s) (CRealAssign lp_z (TProgVar lp_e))
    (CRealAssign lp_z lp_negate).

Lemma lp_prog_eq : lp_prog = CSeq (CBoolToss lp_s (1 / 2)) lp_if.
Proof. reflexivity. Qed.

Lemma lp_then_event :
  forall (y : ProbLogicVar) (t : R),
    {{ $(lp_rigid y (QIndicator (lp_src_below t))) }}
      $(CRealAssign lp_z (TProgVar lp_e))
    {{ $(lp_rigid y (QIndicator (lp_below t))) }}.
Proof.
  intros y t.
  change (lp_rigid y (QIndicator (lp_src_below t))) with
    (subst_real_pformula lp_z (TProgVar lp_e) (lp_rigid y (QIndicator (lp_below t)))).
  apply HRealAssign.
Qed.

Lemma lp_else_event :
  forall (y : ProbLogicVar) (t : R),
    {{ $(lp_rigid y (QIndicator (lp_src_above t))) }}
      $(CRealAssign lp_z lp_negate)
    {{ $(lp_rigid y (QIndicator (lp_below t))) }}.
Proof.
  intros y t.
  change (lp_rigid y (QIndicator (lp_src_above t))) with
    (subst_real_pformula lp_z lp_negate (lp_rigid y (QIndicator (lp_below t)))).
  apply HRealAssign.
Qed.

Lemma lp_then_lap :
  forall (y : ProbLogicVar) (b t : R),
    {{ $(lp_rigid y (lp_lap_below b t)) }}
      $(CRealAssign lp_z (TProgVar lp_e))
    {{ $(lp_rigid y (lp_lap_below b t)) }}.
Proof.
  intros y b t.
  change (lp_rigid y (lp_lap_below b t)) with
    (subst_real_pformula lp_z (TProgVar lp_e) (lp_rigid y (lp_lap_below b t)))
    at 1.
  apply HRealAssign.
Qed.

Lemma lp_else_lap :
  forall (y : ProbLogicVar) (b t : R),
    {{ $(lp_rigid y (lp_lap_below b t)) }}
      $(CRealAssign lp_z lp_negate)
    {{ $(lp_rigid y (lp_lap_below b t)) }}.
Proof.
  intros y b t.
  change (lp_rigid y (lp_lap_below b t)) with
    (subst_real_pformula lp_z lp_negate (lp_rigid y (lp_lap_below b t)))
    at 1.
  apply HRealAssign.
Qed.

Definition lp_if_pre_event (t : R) : PFormula :=
  if_precondition (lp_rigid lp_y1 (QIndicator (lp_src_below t)))
    (lp_rigid lp_y2 (QIndicator (lp_src_above t))) (FProgBool lp_s).

Definition lp_if_pre_lap (b t : R) : PFormula :=
  if_precondition (lp_rigid lp_y3 (lp_lap_below b t))
    (lp_rigid lp_y4 (lp_lap_below b t)) (FProgBool lp_s).

Definition lp_sum_event (t : R) : PFormula :=
  p_eq (PAdd (PVar lp_y1) (PVar lp_y2)) (PExpect (QIndicator (lp_below t))).

Definition lp_sum_lap (b t : R) : PFormula :=
  p_eq (PAdd (PVar lp_y3) (PVar lp_y4)) (PExpect (lp_lap_below b t)).

Definition lp_rigid_link : PFormula :=
  p_eq (PAdd (PVar lp_y1) (PVar lp_y2)) (PAdd (PVar lp_y3) (PVar lp_y4)).

Definition lp_if_pre (b t : R) : PFormula :=
  p_and (p_and (lp_if_pre_event t) (lp_if_pre_lap b t)) lp_rigid_link.

Definition lp_if_post (b t : R) : PFormula :=
  p_and (p_and (lp_sum_event t) (lp_sum_lap b t)) lp_rigid_link.

Lemma lp_if_step_event :
  forall t : R, {{ $(lp_if_pre_event t) }} $(lp_if) {{ $(lp_sum_event t) }}.
Proof.
  intro t.
  apply HIfEq; [apply lp_then_event | apply lp_else_event].
Qed.

Lemma lp_if_step_lap :
  forall b t : R, {{ $(lp_if_pre_lap b t) }} $(lp_if) {{ $(lp_sum_lap b t) }}.
Proof.
  intros b t.
  apply HIfEq; [apply lp_then_lap | apply lp_else_lap].
Qed.

Lemma lp_if_step_link :
  {{ $(lp_rigid_link) }} $(lp_if) {{ $(lp_rigid_link) }}.
Proof.
  apply HFree.
  unfold lp_rigid_link, p_eq, p_and, p_not.
  cbn [pformula_analytical pterm_analytical]; tauto.
Qed.

Lemma lp_if_step_all :
  forall b t : R, {{ $(lp_if_pre b t) }} $(lp_if) {{ $(lp_if_post b t) }}.
Proof.
  intros b t.
  unfold lp_if_pre, lp_if_post.
  apply HAnd; [apply HAnd |].
  - eapply HConseq with (eta1 := lp_if_pre_event t) (eta2 := lp_sum_event t).
    + intros ps Hadm; cbn [psatisfies]; intro H.
      apply psatisfies_p_and in H; destruct H as [H _].
      apply psatisfies_p_and in H; destruct H as [H _]; exact H.
    + apply lp_if_step_event.
    + intros ps Hadm; cbn [psatisfies]; tauto.
  - eapply HConseq with (eta1 := lp_if_pre_lap b t) (eta2 := lp_sum_lap b t).
    + intros ps Hadm; cbn [psatisfies]; intro H.
      apply psatisfies_p_and in H; destruct H as [H _].
      apply psatisfies_p_and in H; destruct H as [_ H]; exact H.
    + apply lp_if_step_lap.
    + intros ps Hadm; cbn [psatisfies]; tauto.
  - eapply HConseq with (eta1 := lp_rigid_link) (eta2 := lp_rigid_link).
    + intros ps Hadm; cbn [psatisfies]; intro H.
      apply psatisfies_p_and in H; destruct H as [_ H]; exact H.
    + apply lp_if_step_link.
    + intros ps Hadm; cbn [psatisfies]; tauto.
Qed.

(** * The toss *)

Lemma lp_condition_p_eq :
  forall (p1 p2 : Pterm) (g : CFormula),
    condition_pformula (p_eq p1 p2) g =
    p_eq (condition_pterm p1 g) (condition_pterm p2 g).
Proof. reflexivity. Qed.

Lemma lp_toss_p_eq :
  forall (b : BoolProgramVar) (r : R) (p1 p2 : Pterm),
    toss_pformula b r (p_eq p1 p2) = p_eq (toss_pterm b r p1) (toss_pterm b r p2).
Proof. reflexivity. Qed.

Lemma lp_toss_cond_lo_true :
  forall t : R,
    subst_bool_pconstruct lp_s c_true
      (condition_pconstruct (QIndicator (lp_src_below t)) (FProgBool lp_s)) =
    QIndicator (c_and (lp_src_below t) c_true).
Proof. reflexivity. Qed.

Lemma lp_toss_cond_lo_false :
  forall t : R,
    subst_bool_pconstruct lp_s FFalse
      (condition_pconstruct (QIndicator (lp_src_below t)) (FProgBool lp_s)) =
    QIndicator (c_and (lp_src_below t) FFalse).
Proof. reflexivity. Qed.

Lemma lp_toss_cond_hi_true :
  forall t : R,
    subst_bool_pconstruct lp_s c_true
      (condition_pconstruct (QIndicator (lp_src_above t)) (c_not (FProgBool lp_s))) =
    QIndicator (c_and (lp_src_above t) (c_not c_true)).
Proof. reflexivity. Qed.

Lemma lp_toss_cond_hi_false :
  forall t : R,
    subst_bool_pconstruct lp_s FFalse
      (condition_pconstruct (QIndicator (lp_src_above t)) (c_not (FProgBool lp_s))) =
    QIndicator (c_and (lp_src_above t) (c_not FFalse)).
Proof. reflexivity. Qed.

Lemma lp_toss_cond_lap :
  forall (b t : R) (g : CFormula) (beta : CFormula),
    beta = c_true \/ beta = FFalse ->
    g = FProgBool lp_s \/ g = c_not (FProgBool lp_s) ->
    subst_bool_pconstruct lp_s beta (condition_pconstruct (lp_lap_below b t) g) =
    QIntegral lp_w (lp_lap_dist b)
      (QIndicator (c_and (lp_w_below t) (subst_bool_cformula lp_s beta g))).
Proof.
  intros b t g beta Hbeta Hg.
  destruct Hbeta as [-> | ->]; destruct Hg as [-> | ->]; reflexivity.
Qed.

(** The precondition of the whole program after introducing the rigid
    variables: each records half of the corresponding incoming mass. *)
Definition lp_half (q : PConstruct) : Pterm := PMul (PConst (1 / 2)) (PExpect q).

Definition lp_pre_rigid (b t : R) : PFormula :=
  p_and
    (p_and
       (p_and
          (p_and (lp_pre b t)
             (p_eq (PVar lp_y1) (lp_half (QIndicator (lp_src_below t)))))
          (p_eq (PVar lp_y2) (lp_half (QIndicator (lp_src_above t)))))
       (p_eq (PVar lp_y3) (lp_half (lp_lap_below b t))))
    (p_eq (PVar lp_y4) (lp_half (lp_lap_below b t))).

Lemma lp_toss_pre :
  forall b t : R,
    (0 < b)%R ->
    pformula_valid
      (PFImpl (lp_pre_rigid b t) (toss_pformula lp_s (1 / 2) (lp_if_pre b t))).
Proof.
  intros b t Hb ps Hadm.
  cbn [psatisfies]; intro H.
  unfold lp_pre_rigid, lp_pre in H.
  apply psatisfies_p_and in H; destruct H as [H H4].
  apply psatisfies_p_and in H; destruct H as [H H3].
  apply psatisfies_p_and in H; destruct H as [H H2].
  apply psatisfies_p_and in H; destruct H as [H H1].
  apply psatisfies_p_and in H; destruct H as [HA HB].
  apply psatisfies_p_eq in HA, HB, H1, H2, H3, H4.
  unfold lp_half in H1, H2, H3, H4.
  cbn [pterm_eval] in HA, HB, H1, H2, H3, H4.
  pose proof (lp_expect_mixture b t (pstate_measure ps) Hb) as Hmix.
  unfold lp_if_pre, lp_if_pre_event, lp_if_pre_lap, if_precondition, lp_rigid,
    lp_rigid_link.
  rewrite !lp_toss_p_and, !lp_toss_p_eq, !lp_condition_p_eq.
  cbn [condition_pterm toss_pterm].
  apply psatisfies_p_and; split; [apply psatisfies_p_and; split |].
  - apply psatisfies_p_and; split; apply psatisfies_p_eq; cbn [pterm_eval toss_pterm condition_pterm].
    + rewrite lp_toss_cond_lo_true, lp_toss_cond_lo_false.
      rewrite lp_expect_and_true, lp_expect_and_false; lra.
    + rewrite lp_toss_cond_hi_true, lp_toss_cond_hi_false.
      rewrite lp_expect_and_not_true, lp_expect_and_not_false; lra.
  - apply psatisfies_p_and; split; apply psatisfies_p_eq; cbn [pterm_eval toss_pterm condition_pterm].
    + rewrite !lp_toss_cond_lap by tauto.
      cbn [subst_bool_cformula].
      rewrite bpv_eq_dec_refl.
      rewrite (lp_expect_lap_and_valid b t _ c_true)
        by (intro v; cbn [c_true satisfies]; tauto).
      rewrite (lp_expect_lap_and_unsat b t _ FFalse Hb)
        by (intro v; cbn [satisfies]; tauto).
      lra.
    + rewrite !lp_toss_cond_lap by tauto.
      unfold c_not; cbn [subst_bool_cformula].
      rewrite bpv_eq_dec_refl.
      rewrite (lp_expect_lap_and_unsat b t _ (FImpl c_true FFalse) Hb)
        by (intro v; cbn [c_true satisfies]; tauto).
      rewrite (lp_expect_lap_and_valid b t _ (FImpl FFalse FFalse))
        by (intro v; cbn [satisfies]; tauto).
      lra.
  - apply psatisfies_p_eq; cbn [pterm_eval toss_pterm condition_pterm]; lra.
Qed.

(** * The core derivation, with the rigid variables in the precondition *)

Lemma lp_core :
  forall b t : R,
    (0 < b)%R ->
    {{ $(lp_pre_rigid b t) }} $(lp_prog) {{ $(lp_post b t) }}.
Proof.
  intros b t Hb.
  rewrite lp_prog_eq.
  eapply HConseq with
    (eta1 := toss_pformula lp_s (1 / 2) (lp_if_pre b t))
    (eta2 := lp_if_post b t).
  - apply lp_toss_pre; exact Hb.
  - eapply HSeq with (eta2 := lp_if_pre b t).
    + apply HBoolToss; unfold coin_probability_valid; lra.
    + apply lp_if_step_all.
  - intros ps Hadm; cbn [psatisfies]; intro H.
    unfold lp_if_post, lp_sum_event, lp_sum_lap, lp_rigid_link in H.
    apply psatisfies_p_and in H; destruct H as [H Hl].
    apply psatisfies_p_and in H; destruct H as [He Hp].
    apply psatisfies_p_eq in He, Hp, Hl.
    cbn [pterm_eval] in He, Hp, Hl.
    unfold lp_post; apply psatisfies_p_eq; cbn [pterm_eval]; lra.
Qed.

(** * Eliminating the rigid variables *)

Lemma lp_post_no_var :
  forall (y : ProbLogicVar) (b t : R),
    ~ prob_logic_var_occurs_pformula y (lp_post b t).
Proof.
  intros y b t.
  unfold lp_post, p_eq, p_and, p_not.
  cbn [prob_logic_var_occurs_pformula prob_logic_var_occurs_pterm]; tauto.
Qed.

Lemma lp_half_no_var :
  forall (y : ProbLogicVar) (q : PConstruct),
    ~ prob_logic_var_occurs_pterm y (lp_half q).
Proof.
  intros y q; unfold lp_half; cbn [prob_logic_var_occurs_pterm]; tauto.
Qed.

(** * The sampler

    A fair sign on an exponential(1/b) source is Laplace(0, b). *)

Theorem lp_laplace_from_exponential :
  forall b t : R,
    (0 < b)%R ->
    {{ $(lp_pre b t) }} $(lp_prog) {{ $(lp_post b t) }}.
Proof.
  intros b t Hb.
  set (E1 := p_and (lp_pre b t)
               (p_eq (PVar lp_y1) (lp_half (QIndicator (lp_src_below t))))).
  set (E2 := p_and E1 (p_eq (PVar lp_y2) (lp_half (QIndicator (lp_src_above t))))).
  set (E3 := p_and E2 (p_eq (PVar lp_y3) (lp_half (lp_lap_below b t)))).
  assert (D3 : hoare_derivable E3 lp_prog (lp_post b t)).
  { change E3 with (subst_prob_pformula lp_y4 (lp_half (lp_lap_below b t)) E3).
    apply HElimv;
      [exact (lp_core b t Hb) | apply lp_half_no_var | apply lp_post_no_var]. }
  assert (D2 : hoare_derivable E2 lp_prog (lp_post b t)).
  { change E2 with (subst_prob_pformula lp_y3 (lp_half (lp_lap_below b t)) E2).
    apply HElimv; [exact D3 | apply lp_half_no_var | apply lp_post_no_var]. }
  assert (D1 : hoare_derivable E1 lp_prog (lp_post b t)).
  { change E1 with
      (subst_prob_pformula lp_y2 (lp_half (QIndicator (lp_src_above t))) E1).
    apply HElimv; [exact D2 | apply lp_half_no_var | apply lp_post_no_var]. }
  change (lp_pre b t) with
    (subst_prob_pformula lp_y1 (lp_half (QIndicator (lp_src_below t))) (lp_pre b t)).
  apply HElimv; [exact D1 | apply lp_half_no_var | apply lp_post_no_var].
Qed.
