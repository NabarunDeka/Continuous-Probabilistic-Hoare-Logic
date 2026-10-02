(**
  LaplaceFromExponential.v -- attach a fair random sign to a nonnegative
  variate.  With an Exp(1/b) source this produces Laplace(0,b).

      s := toss(1/2);
      if s then z := e else z := (-1) * e end

  THE TRIPLE ([lp_laplace_from_exponential], for [0 < b]):

      { Pr[e < t] = exp_cdf b t  /\  Pr[-e < t] = exp_survival b t }
          lp_prog
      { Pr[z < t] = laplace_cdf 0 b t }

  WHY THE SOURCE IS AN ASSUMPTION.  [Distribution] in CPHL.v offers only
  [Uniform], [Laplace] and [Gaussian] -- there is no [Exponential]
  constructor, and [Term] is a polynomial algebra with no logarithm, so the
  inverse-CDF construction [e := -ln(u)/lambda] is not expressible either.
  The exponential source therefore enters as a HYPOTHESIS on the incoming
  measure rather than as a sampling command.  That is not a dodge: it is
  discharged by ExponentialFromLaplace.v, which builds exactly such an [e].

  WHAT IS ACTUALLY PROVED.  The content is the distribution-agnostic
  mixture lemma [lp_sign_mixture]:

      { Pr[e < t] = fe  /\  Pr[-e < t] = se }  lp_prog  { Pr[z < t] = (fe+se)/2 }

  for ARBITRARY [fe] and [se].  Nothing exponential appears in it.  The
  exponential answer is then one arithmetic instantiation
  ([lp_mixture_is_laplace]), which is where the case split [t < 0] versus
  [0 <= t] lives.  Keeping the two apart is what makes the proof short: the
  program reasoning never sees a case split, and the case split never sees
  the program.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import ClassicalDescription.
From Stdlib Require Import Classical.
Require Import CPHL.
Require Import SampleBeforeLoop.
Require Import PersistentSampleLoop.
Require Import HalfLaplaceRejection.
Require Import SVT.

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
  cbn [q_eval].
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
  cbn [q_eval].
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

(** * Instantiating at the exponential

    [lp_src_above t] is written [-e < t]; on the state that is the event
    [e > -t], so the second hypothesis is the source's SURVIVAL function
    read at [-t].  Spelling that out once keeps the constants below
    honest. *)

Lemma lp_src_above_spec :
  forall (v : state) (t : R),
    satisfies v (lp_src_above t) <->
    (- t < real_program_values v lp_e)%R.
Proof.
  intros v t.
  unfold lp_src_above, lp_negate, lp_minus_one, c_lt, c_not.
  cbn [satisfies term_eval].
  split; intro H.
  - destruct (Rlt_dec (- t) (real_program_values v lp_e)) as [Hd | Hd];
      [exact Hd |].
    exfalso; apply H; lra.
  - intro Hf; lra.
Qed.

(** The Exp(1/b) CDF, and its survival read at [-t]. *)
Definition exp_cdf (b t : R) : R :=
  if Rle_dec t 0 then 0%R else (1 - exp (- t / b))%R.

Definition exp_survival (b t : R) : R :=
  if Rle_dec 0 t then 1%R else exp (t / b).

(** The whole case split lives here, and nowhere else. *)
Lemma lp_mixture_is_laplace :
  forall b t : R,
    (0 < b)%R ->
    ((exp_cdf b t + exp_survival b t) / 2)%R = laplace_cdf 0 b t.
Proof.
  intros b t Hb.
  unfold exp_cdf, exp_survival, laplace_cdf.
  destruct (Rle_dec t 0) as [Hle | Hgt].
  - destruct (Rle_dec 0 t) as [Hge | Hlt].
    + (* t = 0 : both branches meet *)
      assert (Ht : t = 0%R) by lra.
      subst t.
      replace ((0 - 0) / b)%R with 0%R by (field; lra).
      rewrite exp_0; lra.
    + replace ((t - 0) / b)%R with (t / b)%R by (field; lra).
      lra.
  - destruct (Rle_dec 0 t) as [Hge | Hlt]; [| lra].
    replace (- (t - 0) / b)%R with (- t / b)%R by (field; lra).
    lra.
Qed.

(** * The sampler

    A fair sign on an Exp(1/b) source is Laplace(0,b). *)

Theorem lp_laplace_from_exponential :
  forall b t : R,
    (0 < b)%R ->
    {{ (Pr[$(lp_src_below t)] = $(exp_cdf b t))
       /\ (Pr[$(lp_src_above t)] = $(exp_survival b t)) }}
      $(lp_prog)
    {{ Pr[$(lp_below t)] = $(laplace_cdf 0 b t) }}.
Proof.
  intros b t Hb.
  replace (laplace_cdf 0 b t)
    with ((exp_cdf b t + exp_survival b t) / 2)%R
    by (apply lp_mixture_is_laplace; exact Hb).
  apply lp_sign_mixture.
Qed.
