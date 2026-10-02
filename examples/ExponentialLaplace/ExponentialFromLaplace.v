(**
  ExponentialFromLaplace.v -- fold a Laplace draw onto its own absolute
  value.  The folded variable is Exp(1/b).

      x   <- sample(Laplace(0,b));
      neg := (x < 0);
      if neg then e := (-1) * x else e := x end        (* e = |x| *)

  THE TRIPLE ([ef_correct], for [0 <= t] and [0 < b]):

      { Pr[tt] = 1 }
          ef_prog b
      { Pr[e < t]  =  1 - exp(-t/b) }

  which is exactly the Exp(1/b) CDF.  This is the converse of
  LaplaceFromExponential.v.

  HOW MUCH OF THE ROUND TRIP THIS CLOSES.  LaplaceFromExponential.v assumes
  TWO things about its source: the CDF [Pr[e < t]] and the reflected
  survival [Pr[-e < t]].  The theorem below supplies the FIRST, and only for
  [0 <= t].  Two facts are still missing before Laplace -> Exp -> Laplace is
  a closed loop in the logic:

    (a) [Pr[e < t] = 0] for [t < 0]  -- both fold regions are empty there,
        so the same proof shape works with both integrals evaluating to 0;
    (b) [Pr[-e < t] = exp_survival b t], which needs [0 <= e] almost surely
        and is not an instance of anything proved here.

  Neither is deep, but neither is proved, so the round trip is currently a
  claim about the mathematics rather than a Rocq-checked composition.

  WHY A CONDITIONAL AND NOT AN ABSOLUTE VALUE.  [Term] is a polynomial
  algebra -- [TProgVar], [TConst], [TAdd], [TMul] -- with no [Rabs], so
  [e := |x|] cannot be written.  Branching on the sign and negating with
  [TMul (TConst (-1))] is the only route, and it is why this program needs
  [HIfEq] where a language with [Rabs] would need nothing at all.

  WHAT IS NEW HERE -- AN ATOM THAT WILL NOT CANCEL.  Folding sends the two
  halves of the line onto [0,t):

      then-branch:   { -t < x < 0 }      (OPEN at -t)
      else-branch:   { 0 <= x < t }      (half-open)

  The else half is a difference of two strict CDFs and evaluates exactly.
  The then half is not: negation flips [<] into [>], so its left endpoint is
  open, while CPHL's closed forms come in only two shapes --
  [laplace_integral_strict_cdf] for [z < c] and [laplace_integral_survival]
  for [c <= z].  Neither produces an open left endpoint, and the pointwise
  identity one would like,

      1_(-t,0) = 1_{z<0} - 1_{z<-t} - 1_{z=-t},

  is FALSE at [t = 0], [z = 0].  The repair is to move the atom to the other
  side, where it is correct for every [t >= 0]:

      1_(-t,0) + 1_{z=-t} * 1_{z<0}  =  1_{z<0} - 1_{z<-t}

  and then kill it with [real_integral_singleton_zero].  That axiom is
  already in CPHL.v's trusted base (it was added for [Uniform]'s closed
  support), so nothing new is assumed here -- but this is the first place a
  LAPLACE calculation needs it.  A [laplace_integral_closed_cdf] companion
  to the two existing closed forms would remove the detour entirely.
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
Require Import TruncatedLaplaceRejection.
Require Import SVT.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * The program *)

Definition ef_x : RealProgramVar := real_program_var "ef_x".
Definition ef_e : RealProgramVar := real_program_var "ef_e".
Definition ef_neg : BoolProgramVar := bool_program_var "ef_neg".

Definition ef_minus_one : Term := TConst (-1).
Definition ef_negate : Term := <{ $(ef_minus_one) * ef_x }>.

Definition ef_noise (b : R) : Distribution := <{ laplace(0, b) }>.
Definition ef_sign : CFormula := <{ ef_x < 0 }>.

Definition ef_prog (b : R) : Cmd :=
  <{ ef_x   sample $(ef_noise b);
     ef_neg b= $(ef_sign);
     if ef_neg then ef_e := $(ef_negate) else ef_e := ef_x end }>.

(** The output event, and the source events the two branches turn it into. *)
Definition ef_out (t : R) : CFormula := <{ ef_e < t }>.
Definition ef_src_lo (t : R) : CFormula := <{ $(ef_negate) < t }>.
Definition ef_src_hi (t : R) : CFormula := <{ ef_x < t }>.

(** Both halves carry the same mass -- that symmetry is the whole point of
    folding. *)
Definition ef_half (t b : R) : R := ((1 / 2) - (1 / 2) * exp (- t / b))%R.

(** * What the two branch regions are *)

Lemma ef_sat_lo :
  forall (t z : R) (v : state),
    satisfies (update_real v ef_x z) <{ $(ef_src_lo t) /\ $(ef_sign) }> <->
    ((- t < z)%R /\ (z < 0)%R).
Proof.
  intros t z v.
  rewrite satisfies_c_and.
  unfold ef_src_lo, ef_sign, ef_negate, ef_minus_one, c_lt, c_not,
    update_real, update_real_values.
  cbn [satisfies term_eval real_program_values].
  rewrite !rpv_eq_dec_refl.
  split.
  - intro H; destruct H as [Hlo Hhi].
    split.
    + destruct (Rlt_dec (- t) z) as [Hd | Hd]; [exact Hd |].
      exfalso; apply Hlo; lra.
    + destruct (Rlt_dec z 0) as [Hd | Hd]; [exact Hd |].
      exfalso; apply Hhi; lra.
  - intro H; destruct H as [Hlo Hhi].
    split; intro Hf; lra.
Qed.

Lemma ef_sat_hi :
  forall (t z : R) (v : state),
    satisfies (update_real v ef_x z)
      <{ $(ef_src_hi t) /\ (~ $(ef_sign)) }> <->
    ((0 <= z)%R /\ (z < t)%R).
Proof.
  intros t z v.
  rewrite satisfies_c_and.
  unfold ef_src_hi, ef_sign, c_lt, c_not, update_real, update_real_values.
  cbn [satisfies term_eval real_program_values].
  rewrite !rpv_eq_dec_refl.
  split.
  - intro H; destruct H as [Hlt Hge].
    split.
    + destruct (Rle_dec 0 z) as [Hd | Hd]; [exact Hd |].
      exfalso; apply Hge; intro Hf; lra.
    + destruct (Rlt_dec z t) as [Hd | Hd]; [exact Hd |].
      exfalso; apply Hlt; lra.
  - intro H; destruct H as [Hge Hlt].
    split.
    + intro Hf; lra.
    + intro Hf; exact (Hf Hge).
Qed.

(** * The two integrands

    The else half is an exact difference of strict indicators.  The then
    half needs the displaced atom described in the header. *)

Lemma ef_indicator_hi :
  forall (t z : R) (g : R -> R),
    (0 <= t)%R ->
    (g z * real_indicator ((0 <= z)%R /\ (z < t)%R))%R =
    (g z * real_indicator (z < t)%R - g z * real_indicator (z < 0)%R)%R.
Proof.
  intros t z g Ht.
  destruct (Rle_dec 0 z) as [Hge | Hlt].
  - rewrite (real_indicator_false (z < 0)%R) by lra.
    destruct (Rlt_dec z t) as [Hlt | Hge'].
    + rewrite (real_indicator_true _ (conj Hge Hlt)).
      rewrite (real_indicator_true (z < t)%R Hlt); ring.
    + rewrite (real_indicator_false _) by (intro H; destruct H; lra).
      rewrite (real_indicator_false (z < t)%R) by lra; ring.
  - rewrite (real_indicator_true (z < 0)%R) by lra.
    rewrite (real_indicator_false _) by (intro H; destruct H; lra).
    rewrite (real_indicator_true (z < t)%R) by lra; ring.
Qed.

Lemma ef_indicator_lo :
  forall (t z : R) (g : R -> R),
    (0 <= t)%R ->
    (g z * real_indicator ((- t < z)%R /\ (z < 0)%R)
     + real_indicator (z = - t)%R * (g z * real_indicator (z < 0)%R))%R =
    (g z * real_indicator (z < 0)%R - g z * real_indicator (z < - t)%R)%R.
Proof.
  intros t z g Ht.
  destruct (total_order_T z (- t)) as [ [Hlt | Heq] | Hgt].
  - (* z < -t <= 0 : both sides vanish *)
    rewrite (real_indicator_false _) by (intro H; destruct H; lra).
    rewrite (real_indicator_false (z = - t)%R) by lra.
    rewrite (real_indicator_true (z < 0)%R) by lra.
    rewrite (real_indicator_true (z < - t)%R Hlt).
    ring.
  - (* z = -t : the atom carries the difference, whatever 1_{z<0} is *)
    rewrite (real_indicator_false _) by (intro H; destruct H; lra).
    rewrite (real_indicator_true (z = - t)%R Heq).
    rewrite (real_indicator_false (z < - t)%R) by lra.
    ring.
  - (* -t < z : the left constraint is vacuous *)
    rewrite (real_indicator_false (z = - t)%R) by lra.
    rewrite (real_indicator_false (z < - t)%R) by lra.
    rewrite (real_indicator_extensional _ (z < 0)%R)
      by (split; [intro H; destruct H; assumption | intro H; split; lra]).
    ring.
Qed.

(** * Evaluating the two integrals *)

Lemma ef_laplace_cdf_neg :
  forall t b : R,
    (0 <= t)%R -> (0 < b)%R ->
    laplace_cdf 0 b (- t) = ((1 / 2) * exp (- t / b))%R.
Proof.
  intros t b Ht Hb.
  unfold laplace_cdf.
  destruct (Rle_dec (- t) 0) as [H | H]; [| lra].
  replace ((- t - 0) / b)%R with (- t / b)%R by (field; lra).
  reflexivity.
Qed.

Lemma ef_integral_hi :
  forall (t b : R) (v : state),
    (0 <= t)%R -> (0 < b)%R ->
    q_eval
      [[ integral ef_x ~ $(ef_noise b),
         indicator[$(ef_src_hi t) /\ (~ $(ef_sign))] ]] v =
    ef_half t b.
Proof.
  intros t b v Ht Hb.
  cbn [q_eval ef_noise distribution_density term_eval].
  rewrite (real_integral_extensional
             _ (fun z =>
                  ((1 / (2 * b)) * exp (- Rabs (z - 0) / b)) *
                    real_indicator (z < t)%R -
                  ((1 / (2 * b)) * exp (- Rabs (z - 0) / b)) *
                    real_indicator (z < 0)%R)).
  - rewrite real_integral_minus.
    rewrite !laplace_integral_strict_cdf by exact Hb.
    rewrite laplace_cdf_centre by exact Hb.
    pose proof (laplace_tail_centred t b Ht Hb) as Htail.
    unfold ef_half; lra.
  - intro z.
    rewrite (real_indicator_extensional _ _ (ef_sat_hi t z v)).
    exact (ef_indicator_hi t z
             (fun w => (1 / (2 * b) * exp (- Rabs (w - 0) / b))%R) Ht).
Qed.

Lemma ef_integral_lo :
  forall (t b : R) (v : state),
    (0 <= t)%R -> (0 < b)%R ->
    q_eval
      [[ integral ef_x ~ $(ef_noise b),
         indicator[$(ef_src_lo t) /\ $(ef_sign)] ]] v =
    ef_half t b.
Proof.
  intros t b v Ht Hb.
  set (dens := fun z : R => ((1 / (2 * b)) * exp (- Rabs (z - 0) / b))%R).
  set (region :=
    fun z : R => (dens z * real_indicator ((- t < z)%R /\ (z < 0)%R))%R).
  set (atom :=
    fun z : R =>
      (real_indicator (z = - t)%R * (dens z * real_indicator (z < 0)%R))%R).
  (* First put the sample's integral into the [region] shape. *)
  transitivity (real_integral region).
  - cbn [q_eval ef_noise distribution_density term_eval].
    apply real_integral_extensional; intro z.
    unfold region, dens.
    rewrite (real_indicator_extensional _ _ (ef_sat_lo t z v)).
    reflexivity.
  - (* The atom is null, and region-plus-atom is an exact CDF difference. *)
    assert (Hatom : real_integral atom = 0%R).
    { unfold atom; apply real_integral_singleton_zero. }
    assert (Hsum :
      (real_integral region + real_integral atom)%R = ef_half t b).
    { rewrite <- real_integral_add.
      transitivity
        (real_integral
           (fun z => (dens z * real_indicator (z < 0)%R -
                      dens z * real_indicator (z < - t)%R)%R)).
      - apply real_integral_extensional; intro z.
        unfold region, atom.
        exact (ef_indicator_lo t z dens Ht).
      - rewrite real_integral_minus.
        unfold dens.
        rewrite !laplace_integral_strict_cdf by exact Hb.
        rewrite laplace_cdf_centre by exact Hb.
        rewrite ef_laplace_cdf_neg by assumption.
        unfold ef_half; lra. }
    lra.
Qed.

(** * Program reasoning

    From here the shape is the same as LaplaceFromExponential.v: two real
    assignments, [svt_if_constants] to add the branch masses, then the
    boolean assignment and the sample. *)

Lemma ef_then_branch :
  forall r t : R,
    {{ $(svt_event_probability r (ef_src_lo t)) }}
      ef_e := $(ef_negate)
    {{ $(svt_event_probability r (ef_out t)) }}.
Proof.
  intros r t.
  replace (svt_event_probability r (ef_src_lo t))
    with (subst_real_pformula ef_e ef_negate
           (svt_event_probability r (ef_out t))).
  - apply HRealAssign.
  - unfold svt_event_probability, ef_out, ef_src_lo, p_eq, c_lt.
    cbn [subst_real_pformula subst_real_pterm subst_real_pconstruct
         subst_real_cformula subst_real_term].
    try rewrite rpv_eq_dec_refl.
    reflexivity.
Qed.

Lemma ef_else_branch :
  forall r t : R,
    {{ $(svt_event_probability r (ef_src_hi t)) }}
      ef_e := ef_x
    {{ $(svt_event_probability r (ef_out t)) }}.
Proof.
  intros r t.
  replace (svt_event_probability r (ef_src_hi t))
    with (subst_real_pformula ef_e (TProgVar ef_x)
           (svt_event_probability r (ef_out t))).
  - apply HRealAssign.
  - unfold svt_event_probability, ef_out, ef_src_hi, p_eq, c_lt.
    cbn [subst_real_pformula subst_real_pterm subst_real_pconstruct
         subst_real_cformula subst_real_term].
    try rewrite rpv_eq_dec_refl.
    reflexivity.
Qed.

Lemma ef_if_step :
  forall r1 r2 t : R,
    {{ $(if_precondition
           (svt_event_probability r1 (ef_src_lo t))
           (svt_event_probability r2 (ef_src_hi t))
           <{ ef_neg }>) }}
      if ef_neg then ef_e := $(ef_negate) else ef_e := ef_x end
    {{ $(svt_event_probability (r1 + r2) (ef_out t)) }}.
Proof.
  intros r1 r2 t.
  pose proof
    (svt_if_constants
       (svt_event_probability r1 (ef_src_lo t))
       (svt_event_probability r2 (ef_src_hi t))
       (FProgBool ef_neg) (ef_out t)
       (CRealAssign ef_e ef_negate)
       (CRealAssign ef_e (TProgVar ef_x))
       r1 r2
       (ef_then_branch r1 t) (ef_else_branch r2 t)) as H.
  cbn [subst_prob_pformula subst_prob_pterm if_precondition
       condition_pformula condition_pterm
       svt_event_probability p_eq p_and p_not] in H.
  exact H.
Qed.

(** Reshaping lemmas, all definitional. *)

Lemma ef_condition_p_eq_const :
  forall (c : R) (gamma guard : CFormula),
    condition_pformula [[ $(c) = Pr[$(gamma)] ]] guard =
    [[ $(c) = Pr[$(gamma) /\ $(guard)] ]].
Proof. reflexivity. Qed.

Lemma ef_subst_p_and :
  forall (b : BoolProgramVar) (beta : CFormula) (eta1 eta2 : PFormula),
    subst_bool_pformula b beta [[ $(eta1) /\ $(eta2) ]] =
    [[ $(subst_bool_pformula b beta eta1)
       /\ $(subst_bool_pformula b beta eta2) ]].
Proof. reflexivity. Qed.

Lemma ef_subst_p_eq_const :
  forall (b : BoolProgramVar) (beta : CFormula) (c : R) (q : PConstruct),
    subst_bool_pformula b beta [[ $(c) = E[$(q)] ]] =
    [[ $(c) = E[$(subst_bool_pconstruct b beta q)] ]].
Proof. reflexivity. Qed.

Lemma ef_subst_lo :
  forall t : R,
    subst_bool_pconstruct ef_neg ef_sign
      [[ indicator[$(ef_src_lo t) /\ ef_neg] ]] =
    [[ indicator[$(ef_src_lo t) /\ $(ef_sign)] ]].
Proof. reflexivity. Qed.

Lemma ef_subst_hi :
  forall t : R,
    subst_bool_pconstruct ef_neg ef_sign
      [[ indicator[$(ef_src_hi t) /\ (~ ef_neg)] ]] =
    [[ indicator[$(ef_src_hi t) /\ (~ $(ef_sign))] ]].
Proof. reflexivity. Qed.

Lemma ef_sample_p_and :
  forall (x : RealProgramVar) (d : Distribution) (eta1 eta2 : PFormula),
    sample_pformula x d [[ $(eta1) /\ $(eta2) ]] =
    [[ $(sample_pformula x d eta1) /\ $(sample_pformula x d eta2) ]].
Proof. reflexivity. Qed.

Lemma ef_sample_p_eq_const :
  forall (x : RealProgramVar) (d : Distribution) (c : R) (q : PConstruct),
    sample_pformula x d [[ $(c) = E[$(q)] ]] =
    [[ $(c) = E[integral x ~ $(d), $(q)] ]].
Proof. reflexivity. Qed.

Lemma ef_noise_valid_under :
  forall (b : R) (eta : PFormula),
    (0 < b)%R ->
    pformula_valid
      [[ $(eta) -> almost_sure[$(distribution_valid_formula (ef_noise b))] ]].
Proof.
  intros b eta Hb ps Hadm.
  cbn [psatisfies]; intro Hignore.
  clear Hignore; revert ps.
  apply p_almost_sure_of_pointwise.
  intro v.
  unfold ef_noise.
  cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
  intro Hle; lra.
Qed.

(** * The folded sampler *)

Theorem ef_correct :
  forall t b : R,
    (0 <= t)%R -> (0 < b)%R ->
    {{ Pr[true] = 1 }}
      $(ef_prog b)
    {{ Pr[$(ef_out t)] = $(1 - exp (- t / b)) }}.
Proof.
  intros t b Ht Hb.
  unfold ef_prog.
  set (P :=
    if_precondition
      (svt_event_probability (ef_half t b) (ef_src_lo t))
      (svt_event_probability (ef_half t b) (ef_src_hi t))
      (FProgBool ef_neg)).
  set (P2 := subst_bool_pformula ef_neg ef_sign P).
  eapply HConseq with
    (eta1 := sample_pformula ef_x (ef_noise b) P2)
    (eta2 := svt_event_probability (ef_half t b + ef_half t b) (ef_out t)).
  - (* the unit-mass precondition entails the sampled formula *)
    intro ps.
    intro Hadm.
    cbn [psatisfies]; intro Hpre.
    apply psatisfies_p_eq in Hpre.
    cbn [pterm_eval] in Hpre.
    unfold P2, P, if_precondition, svt_event_probability.
    rewrite !ef_condition_p_eq_const.
    rewrite ef_subst_p_and, !ef_subst_p_eq_const, ef_subst_lo, ef_subst_hi.
    rewrite ef_sample_p_and, !ef_sample_p_eq_const.
    apply psatisfies_p_and; split; apply psatisfies_p_eq;
      cbn [pterm_eval].
    + symmetry; apply t3_expect_const; [exact Hpre |].
      intro v; apply ef_integral_lo; assumption.
    + symmetry; apply t3_expect_const; [exact Hpre |].
      intro v; apply ef_integral_hi; assumption.
  - eapply HSeq with (eta2 := P2).
    + apply HRealSample.
      * intro ps; cbn [psatisfies]; intro H; exact H.
      * apply ef_noise_valid_under; exact Hb.
    + eapply HSeq with (eta2 := P).
      * unfold P2; apply HBoolAssign.
      * unfold P; apply ef_if_step.
  - (* both halves carry the same mass, and they sum to the Exp CDF *)
    intro ps.
    intro Hadm.
    unfold svt_event_probability.
    intro Hpost.
    apply psatisfies_p_eq in Hpost.
    cbn [pterm_eval] in Hpost.
    apply psatisfies_p_eq.
    cbn [pterm_eval].
    unfold ef_half in Hpost.
    lra.
Qed.
