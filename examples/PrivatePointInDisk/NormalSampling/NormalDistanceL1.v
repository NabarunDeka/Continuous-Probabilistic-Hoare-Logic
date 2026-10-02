(**
  NormalDistanceL1.v -- the membership test under the L1 (Manhattan)
  distance d(x,y) = SUM |xi - yi|, with normal noise on the distance.

      n      <- sample(Gaussian(0, b));
      ax     := px - cx;   if ax < 0 then ax := -ax else skip end;
      ay     := py - cy;   if ay < 0 then ay := -ay else skip end;
      inside := (ax + ay + n < 1)

  THE TRIPLE ([nl_correct], for [0 < b], writing [L] for the true L1
  distance [|px-cx| + |py-cy|]):

      { Pr[tt] = 1 }
          nl_prog px py cx cy b
      { Pr[inside] = nrm_cdf b (1 - L) }

  [Term] is a polynomial algebra with no absolute value, so [|.|] is
  computed by the branch gadget [nl_abs] -- a genuine [CIf] in the program,
  crossed with CPHL's conditional rule, not folded away at the meta level.

  TWO THINGS THE ENCODING FORCES.

  1. THE SAMPLE MUST COME FIRST.  CPHL's conditional rules ([HIfLe],
     [HIfGe], [HIfEq], and hence [SVT.svt_if_constants]) all conclude with a
     postcondition of the shape [... = E[QIndicator gamma]].  So a [CIf] can
     only be crossed when the assertion after it is an INDICATOR
     probability.  If a [CRealSample] still lay ahead of the branch, the
     weakest precondition there would be a [QIntegral] and no rule would
     apply.  Drawing the noise before computing the distance costs nothing
     -- the noise is independent of the data -- and keeps every branch
     inside the fragment.

  2. THE BRANCHES ARE DEGENERATE.  The coordinates are Rocq reals, so after
     [ax := px - cx] the guard [ax < 0] has the same truth value in every
     state.  One branch therefore carries all the mass and the other none.
     [nl_abs_correct] packages that once: the gadget behaves exactly like
     assigning [Rabs c].  It is proved by [svt_if_constants] with branch
     constants [(r, 0)] or [(0, r)] according to the sign, the zero side
     discharged by [expect_indicator_unsat] and the other by
     [expect_indicator_valid].

  [nrm_cdf] is the centred normal CDF defined in NormalDistance.v -- defined
  as its integral, because [erf] is not elementary.  See that file.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import ClassicalDescription.
From Stdlib Require Import Classical.
Require Import CPHL.
Require Import SampleBeforeLoop.
Require Import HalfLaplaceRejection.
Require Import SVT.
Require Import GaussianDifference.
Require Import NormalDistance.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * The absolute-value gadget *)

Definition nl_minus_one : Term := TConst (-1).

Definition nl_neg (x : RealProgramVar) : CFormula := <{ x < 0 }>.
Definition nl_flip (x : RealProgramVar) : Term := <{ $(nl_minus_one) * x }>.

Definition nl_abs (x : RealProgramVar) : Cmd :=
  <{ if $(nl_neg x) then x := $(nl_flip x) else skip end }>.

(** The two branch triples. *)

Lemma nl_then_branch :
  forall (x : RealProgramVar) (r : R) (gamma : CFormula),
    {{ $(subst_real_pformula x (nl_flip x) (svt_event_probability r gamma)) }}
      x := $(nl_flip x)
    {{ $(svt_event_probability r gamma) }}.
Proof. intros; apply HRealAssign. Qed.

Lemma nl_else_branch :
  forall (r : R) (gamma : CFormula),
    {{ $(svt_event_probability r gamma) }} skip
    {{ $(svt_event_probability r gamma) }}.
Proof. intros; apply HSkip. Qed.

(** The branch step, with the two constants left open. *)
Lemma nl_if_step :
  forall (x : RealProgramVar) (r1 r2 : R) (gamma : CFormula),
    {{ $(if_precondition
           (subst_real_pformula x (nl_flip x) (svt_event_probability r1 gamma))
           (svt_event_probability r2 gamma)
           (nl_neg x)) }}
      $(nl_abs x)
    {{ $(svt_event_probability (r1 + r2) gamma) }}.
Proof.
  intros x r1 r2 gamma.
  pose proof
    (svt_if_constants
       (subst_real_pformula x (nl_flip x) (svt_event_probability r1 gamma))
       (svt_event_probability r2 gamma)
       (nl_neg x) gamma
       (CRealAssign x (nl_flip x)) CSkip
       r1 r2
       (nl_then_branch x r1 gamma) (nl_else_branch r2 gamma)) as H.
  cbn [subst_prob_pformula subst_prob_pterm] in H.
  exact H.
Qed.

(** Two indicator facts, stated on whatever shape [cbn] leaves behind. *)

Lemma nl_expect_iff :
  forall (mu : Measure) (g1 g2 : CFormula),
    (forall v : state, satisfies v g1 <-> satisfies v g2) ->
    expectation mu (q_eval (QIndicator g1)) =
    expectation mu (q_eval (QIndicator g2)).
Proof.
  intros mu g1 g2 H.
  apply expectation_extensional; intro v.
  cbn [q_eval]; apply real_indicator_extensional, H.
Qed.

(** Substitution reductions.  [cbn] alone gets stuck on
    [real_program_var_eq_dec x x] for an abstract [x], so these are named. *)

Lemma nl_subst_and :
  forall (x : RealProgramVar) (t : Term) (A B : CFormula),
    subst_real_cformula x t <{ $(A) /\ $(B) }> =
    <{ $(subst_real_cformula x t A) /\ $(subst_real_cformula x t B) }>.
Proof. intros; reflexivity. Qed.

Lemma nl_subst_not :
  forall (x : RealProgramVar) (t : Term) (A : CFormula),
    subst_real_cformula x t <{ ~ $(A) }> = <{ ~ $(subst_real_cformula x t A) }>.
Proof. intros; reflexivity. Qed.

Lemma nl_subst_neg :
  forall (x : RealProgramVar) (c : R),
    subst_real_cformula x (TConst c) (nl_neg x) = <{ $(c) < 0 }>.
Proof.
  intros x c.
  unfold nl_neg, c_lt, c_not.
  cbn [subst_real_cformula subst_real_term].
  rewrite rpv_eq_dec_refl; reflexivity.
Qed.

Lemma nl_sat_lt :
  forall (v : state) (c : R), satisfies v <{ $(c) < 0 }> <-> (c < 0)%R.
Proof.
  intros v c.
  unfold c_lt, c_not.
  cbn [satisfies term_eval].
  split.
  - intro H; destruct (Rlt_dec c 0) as [Hd | Hd];
      [exact Hd | exfalso; apply H; lra].
  - intros H Hz; lra.
Qed.

Lemma nl_sat_and :
  forall (v : state) (g1 g2 : CFormula),
    satisfies v <{ $(g1) /\ $(g2) }> <-> (satisfies v g1 /\ satisfies v g2).
Proof.
  intros v g1 g2.
  cbn [c_and c_not satisfies].
  split.
  - intro H.
    destruct (classic (satisfies v g1)) as [H1 | H1];
      destruct (classic (satisfies v g2)) as [H2 | H2];
      try (split; assumption);
      exfalso; apply H; intros Ha Hb; contradiction.
  - intros [H1 H2] Hc; exact (Hc H1 H2).
Qed.

(** * The gadget is correct, one lemma per sign

    Stating them per sign, with the precondition written as the NESTED
    substitution the weakest precondition actually produces, avoids needing
    a substitution-composition lemma for [subst_real_cformula] -- CPHL.v has
    none, and [subst o subst] is not definitionally the single substitution
    by the composed term. *)

Lemma nl_abs_neg :
  forall (x : RealProgramVar) (c r : R) (gamma : CFormula),
    (c < 0)%R ->
    {{ $(subst_real_pformula x (TConst c)
           (subst_real_pformula x (nl_flip x)
              (svt_event_probability r gamma))) }}
      x := $(TConst c); $(nl_abs x)
    {{ $(svt_event_probability r gamma) }}.
Proof.
  intros x c r gamma Hc.
  eapply HSeq with
    (eta2 := if_precondition
               (subst_real_pformula x (nl_flip x) (svt_event_probability r gamma))
               (svt_event_probability 0 gamma)
               (nl_neg x)).
  - eapply HConseq with
      (eta1 := subst_real_pformula x (TConst c)
                 (if_precondition
                    (subst_real_pformula x (nl_flip x)
                       (svt_event_probability r gamma))
                    (svt_event_probability 0 gamma)
                    (nl_neg x)))
      (eta2 := if_precondition
                 (subst_real_pformula x (nl_flip x)
                    (svt_event_probability r gamma))
                 (svt_event_probability 0 gamma)
                 (nl_neg x)).
    + intro ps.
    + intro Hadm.
      cbn [psatisfies]; intro Hpre.
      apply psatisfies_p_eq in Hpre.
      cbn [subst_real_pterm pterm_eval] in Hpre.
      apply psatisfies_p_and; split; apply psatisfies_p_eq;
        cbn [subst_real_pterm condition_pterm pterm_eval
             subst_real_pconstruct condition_pconstruct
             condition_pconstruct_fuel pconstruct_size
             subst_real_cformula c_and c_not nl_neg c_lt].
      * rewrite Hpre.
        apply nl_expect_iff; intro v.
        rewrite nl_subst_and, nl_subst_neg, nl_sat_and.
        split.
        -- intro H; split; [exact H | apply nl_sat_lt; exact Hc].
        -- intros [H _]; exact H.
      * symmetry; apply expect_indicator_unsat; intro v.
        rewrite nl_subst_and, nl_subst_not, nl_subst_neg, nl_sat_and.
        intros [_ H]; apply H, nl_sat_lt; exact Hc.
    + apply HRealAssign.
    + intro ps; cbn [psatisfies]; tauto.
  - assert (H := nl_if_step x r 0 gamma).
    replace (r + 0)%R with r in H by ring.
    exact H.
Qed.

Lemma nl_abs_pos :
  forall (x : RealProgramVar) (c r : R) (gamma : CFormula),
    (0 <= c)%R ->
    {{ $(subst_real_pformula x (TConst c) (svt_event_probability r gamma)) }}
      x := $(TConst c); $(nl_abs x)
    {{ $(svt_event_probability r gamma) }}.
Proof.
  intros x c r gamma Hc.
  eapply HSeq with
    (eta2 := if_precondition
               (subst_real_pformula x (nl_flip x) (svt_event_probability 0 gamma))
               (svt_event_probability r gamma)
               (nl_neg x)).
  - eapply HConseq with
      (eta1 := subst_real_pformula x (TConst c)
                 (if_precondition
                    (subst_real_pformula x (nl_flip x)
                       (svt_event_probability 0 gamma))
                    (svt_event_probability r gamma)
                    (nl_neg x)))
      (eta2 := if_precondition
                 (subst_real_pformula x (nl_flip x)
                    (svt_event_probability 0 gamma))
                 (svt_event_probability r gamma)
                 (nl_neg x)).
    + intro ps.
    + intro Hadm.
      cbn [psatisfies]; intro Hpre.
      apply psatisfies_p_eq in Hpre.
      cbn [subst_real_pterm pterm_eval] in Hpre.
      apply psatisfies_p_and; split; apply psatisfies_p_eq;
        cbn [subst_real_pterm condition_pterm pterm_eval
             subst_real_pconstruct condition_pconstruct
             condition_pconstruct_fuel pconstruct_size
             subst_real_cformula c_and c_not nl_neg c_lt].
      * symmetry; apply expect_indicator_unsat; intro v.
        rewrite nl_subst_and, nl_subst_neg, nl_sat_and.
        intros [_ H]; apply nl_sat_lt in H; lra.
      * rewrite Hpre.
        apply nl_expect_iff; intro v.
        rewrite nl_subst_and, nl_subst_not, nl_subst_neg, nl_sat_and.
        split.
        -- intro H; split; [exact H |].
           intro Hk; apply nl_sat_lt in Hk; lra.
        -- intros [H _]; exact H.
  + apply HRealAssign.
  + intro ps; cbn [psatisfies]; tauto.
  - assert (H := nl_if_step x 0 r gamma).
    replace (0 + r)%R with r in H by ring.
    exact H.
Qed.

(** * The program *)

Definition nl_ax : RealProgramVar := real_program_var "nl_ax".
Definition nl_ay : RealProgramVar := real_program_var "nl_ay".
Definition nl_n  : RealProgramVar := real_program_var "nl_n".
Definition nl_inside : BoolProgramVar := bool_program_var "nl_inside".

Definition nl_noise (b : R) : Distribution := <{ gaussian(0, b) }>.

Definition nl_test : CFormula := <{ ((nl_ax + nl_ay) + nl_n) < 1 }>.

Definition nl_block (x : RealProgramVar) (c : R) : Cmd :=
  <{ x := $(TConst c); $(nl_abs x) }>.

Definition nl_prog (px py cx cy b : R) : Cmd :=
  <{ nl_n sample $(nl_noise b);
     $(nl_block nl_ax (px - cx));
     $(nl_block nl_ay (py - cy));
     nl_inside b= $(nl_test) }>.

(** The true L1 distance. *)
Definition nl_L (px py cx cy : R) : R :=
  (Rabs (px - cx) + Rabs (py - cy))%R.

(** * Reducing the substituted guard *)

Lemma nl_dec_neq :
  forall (x y : RealProgramVar) (A : Type) (a c : A),
    x <> y -> (if real_program_var_eq_dec x y then a else c) = c.
Proof.
  intros x y A a c H.
  destruct (real_program_var_eq_dec x y); [contradiction | reflexivity].
Qed.

Lemma nl_ax_neq_ay : nl_ax <> nl_ay.
Proof. unfold nl_ax, nl_ay; intro H; inversion H. Qed.
Lemma nl_n_neq_ay : nl_n <> nl_ay.
Proof. unfold nl_n, nl_ay; intro H; inversion H. Qed.
Lemma nl_n_neq_ax : nl_n <> nl_ax.
Proof. unfold nl_n, nl_ax; intro H; inversion H. Qed.

Ltac nl_dec :=
  unfold nl_ax, nl_ay, nl_n in *;
  repeat match goal with
         | |- context [real_program_var_eq_dec ?a ?b] =>
             destruct (real_program_var_eq_dec a b)
         end;
  try congruence.

Lemma nl_test_subst :
  forall tx ty : Term,
    subst_real_term nl_ax tx ty = ty ->
    subst_real_cformula nl_ax tx (subst_real_cformula nl_ay ty nl_test) =
    <{ (($(tx) + $(ty)) + nl_n) < 1 }>.
Proof.
  intros tx ty Hty.
  unfold nl_test, c_lt, c_not.
  cbn [subst_real_cformula subst_real_term].
  nl_dec.
  rewrite Hty; reflexivity.
Qed.

(** * The integral *)

Lemma nl_integral :
  forall (tx ty : Term) (Lx Ly b : R) (v : state),
    (0 < b)%R ->
    (forall w : state, term_eval tx w = Lx) ->
    (forall w : state, term_eval ty w = Ly) ->
    q_eval
      [[ integral nl_n ~ $(Gaussian (TConst 0) (TConst b)),
         indicator[ (($(tx) + $(ty)) + nl_n) < 1 ] ]] v =
    nrm_cdf b (1 - (Lx + Ly)).
Proof.
  intros tx ty Lx Ly b v Hb Hx Hy.
  unfold nrm_cdf.
  cbn [q_eval].
  apply real_integral_extensional; intro z.
  f_equal.
  apply real_indicator_extensional.
  unfold c_lt, c_not.
  cbn [satisfies term_eval].
  rewrite Hx, Hy.
  unfold update_real, update_real_values.
  cbn [real_program_values].
  rewrite rpv_eq_dec_refl.
  split.
  - intro H; lra.
  - intros H Hk; lra.
Qed.

(** * Composing the two substitutions the gadget leaves behind *)

Definition nl_flip_const (c : R) : Term := <{ $(nl_minus_one) * $(c) }>.

Lemma nl_subst_term_flip :
  forall (x : RealProgramVar) (c : R) (t : Term),
    subst_real_term x (TConst c) (subst_real_term x (nl_flip x) t) =
    subst_real_term x (nl_flip_const c) t.
Proof.
  intros x c t.
  induction t; cbn; try congruence.
  destruct (real_program_var_eq_dec x0 x) as [He | He].
  - unfold nl_flip, nl_flip_const, nl_minus_one; cbn.
    rewrite rpv_eq_dec_refl; reflexivity.
  - cbn; destruct (real_program_var_eq_dec x0 x);
      [contradiction | reflexivity].
Qed.

Lemma nl_subst_cformula_flip :
  forall (x : RealProgramVar) (c : R) (g : CFormula),
    subst_real_cformula x (TConst c) (subst_real_cformula x (nl_flip x) g) =
    subst_real_cformula x (nl_flip_const c) g.
Proof.
  intros x c g.
  induction g; cbn; try congruence.
  rewrite !nl_subst_term_flip; reflexivity.
Qed.

Lemma nl_subst_svt :
  forall (x : RealProgramVar) (t : Term) (r : R) (gamma : CFormula),
    subst_real_pformula x t (svt_event_probability r gamma) =
    svt_event_probability r (subst_real_cformula x t gamma).
Proof. intros; reflexivity. Qed.

(** The whole block [x := c; abs x], one lemma per sign. *)

Lemma nl_block_neg :
  forall (x : RealProgramVar) (c r : R) (gamma : CFormula),
    (c < 0)%R ->
    {{ $(svt_event_probability r
           (subst_real_cformula x (nl_flip_const c) gamma)) }}
      $(nl_block x c)
    {{ $(svt_event_probability r gamma) }}.
Proof.
  intros x c r gamma Hc.
  unfold nl_block.
  rewrite <- (nl_subst_cformula_flip x c gamma).
  rewrite <- (nl_subst_svt x (TConst c) r
                (subst_real_cformula x (nl_flip x) gamma)).
  rewrite <- (nl_subst_svt x (nl_flip x) r gamma).
  apply nl_abs_neg; exact Hc.
Qed.

Lemma nl_block_pos :
  forall (x : RealProgramVar) (c r : R) (gamma : CFormula),
    (0 <= c)%R ->
    {{ $(svt_event_probability r
           (subst_real_cformula x (TConst c) gamma)) }}
      $(nl_block x c)
    {{ $(svt_event_probability r gamma) }}.
Proof.
  intros x c r gamma Hc.
  unfold nl_block.
  rewrite <- nl_subst_svt.
  apply nl_abs_pos; exact Hc.
Qed.

(** The boolean assignment's weakest precondition, in [svt] shape. *)
Lemma nl_bool_pre :
  forall r : R,
    subst_bool_pformula nl_inside nl_test
      (svt_event_probability r (FProgBool nl_inside)) =
    svt_event_probability r nl_test.
Proof. intros; reflexivity. Qed.

(** * The derivation, parameterised by the two effective terms *)

Lemma nl_noise_valid_under :
  forall (b : R) (pre : PFormula),
    (0 < b)%R ->
    pformula_valid
      [[ $(pre) -> almost_sure[$(distribution_valid_formula (nl_noise b))] ]].
Proof.
  intros b pre Hb ps Hadm.
  cbn [psatisfies]; intro Hignore.
  clear Hignore; revert ps.
  apply p_almost_sure_of_pointwise.
  intro v.
  unfold nl_noise.
  cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
  intro Hle; lra.
Qed.

Lemma nl_derivation :
  forall (px py cx cy b : R) (Tx Ty : Term) (Lx Ly : R),
    (0 < b)%R ->
    (forall w : state, term_eval Tx w = Lx) ->
    (forall w : state, term_eval Ty w = Ly) ->
    subst_real_term nl_ax Tx Ty = Ty ->
    (forall (r : R) (gamma : CFormula),
       {{ $(svt_event_probability r (subst_real_cformula nl_ax Tx gamma)) }}
         $(nl_block nl_ax (px - cx))
       {{ $(svt_event_probability r gamma) }}) ->
    (forall (r : R) (gamma : CFormula),
       {{ $(svt_event_probability r (subst_real_cformula nl_ay Ty gamma)) }}
         $(nl_block nl_ay (py - cy))
       {{ $(svt_event_probability r gamma) }}) ->
    {{ Pr[true] = 1 }}
      $(nl_prog px py cx cy b)
    {{ $(svt_event_probability (nrm_cdf b (1 - (Lx + Ly)))
           (FProgBool nl_inside)) }}.
Proof.
  intros px py cx cy b Tx Ty Lx Ly Hb HTx HTy Hclosed Hax Hay.
  set (R0 := nrm_cdf b (1 - (Lx + Ly))).
  unfold nl_prog.
  eapply HSeq with
    (eta2 := svt_event_probability R0
               (subst_real_cformula nl_ax Tx
                  (subst_real_cformula nl_ay Ty nl_test))).
  - apply HRealSample.
    + intro ps.
    + intro Hadm.
      cbn [psatisfies]; intro Hnorm.
      apply psatisfies_p_eq in Hnorm.
      cbn [pterm_eval] in Hnorm.
      apply psatisfies_p_eq.
      cbn [sample_pterm pterm_eval].
      symmetry.
      apply t3_expect_const.
      * exact Hnorm.
      * intro v.
        rewrite (nl_test_subst Tx Ty Hclosed).
        apply (nl_integral Tx Ty Lx Ly b v Hb HTx HTy).
    + apply nl_noise_valid_under; exact Hb.
  - eapply HSeq with
      (eta2 := svt_event_probability R0
                 (subst_real_cformula nl_ay Ty nl_test)).
    + apply Hax.
    + eapply HSeq with (eta2 := svt_event_probability R0 nl_test).
      * apply Hay.
      * rewrite <- (nl_bool_pre R0).
        apply HBoolAssign.
Qed.

(** * The mechanism

    Four cases, one per sign pattern; each supplies the effective term the
    taken branch leaves behind, and they differ only in which gadget lemma
    is used. *)

Theorem nl_correct :
  forall px py cx cy b : R,
    (0 < b)%R ->
    {{ Pr[true] = 1 }}
      $(nl_prog px py cx cy b)
    {{ Pr[nl_inside] = $(nrm_cdf b (1 - nl_L px py cx cy)) }}.
Proof.
  intros px py cx cy b Hb.
  eapply HConseq with
    (eta1 := [[ Pr[true] = 1 ]])
    (eta2 := svt_event_probability (nrm_cdf b (1 - nl_L px py cx cy))
               (FProgBool nl_inside)).
  - intro ps; cbn [psatisfies]; tauto.
  - unfold nl_L.
    destruct (Rlt_dec (px - cx) 0) as [Hx | Hx];
      destruct (Rlt_dec (py - cy) 0) as [Hy | Hy].
    + apply (nl_derivation px py cx cy b
               (nl_flip_const (px - cx)) (nl_flip_const (py - cy))
               (Rabs (px - cx)) (Rabs (py - cy)) Hb).
      * intro w; unfold nl_flip_const, nl_minus_one; cbn [term_eval];
          rewrite (Rabs_left _ Hx); ring.
      * intro w; unfold nl_flip_const, nl_minus_one; cbn [term_eval];
          rewrite (Rabs_left _ Hy); ring.
      * reflexivity.
      * intros r gamma; apply nl_block_neg; exact Hx.
      * intros r gamma; apply nl_block_neg; exact Hy.
    + apply (nl_derivation px py cx cy b
               (nl_flip_const (px - cx)) (TConst (py - cy))
               (Rabs (px - cx)) (Rabs (py - cy)) Hb).
      * intro w; unfold nl_flip_const, nl_minus_one; cbn [term_eval];
          rewrite (Rabs_left _ Hx); ring.
      * intro w; cbn [term_eval]; rewrite Rabs_pos_eq by lra; reflexivity.
      * reflexivity.
      * intros r gamma; apply nl_block_neg; exact Hx.
      * intros r gamma; apply nl_block_pos; lra.
    + apply (nl_derivation px py cx cy b
               (TConst (px - cx)) (nl_flip_const (py - cy))
               (Rabs (px - cx)) (Rabs (py - cy)) Hb).
      * intro w; cbn [term_eval]; rewrite Rabs_pos_eq by lra; reflexivity.
      * intro w; unfold nl_flip_const, nl_minus_one; cbn [term_eval];
          rewrite (Rabs_left _ Hy); ring.
      * reflexivity.
      * intros r gamma; apply nl_block_pos; lra.
      * intros r gamma; apply nl_block_neg; exact Hy.
    + apply (nl_derivation px py cx cy b
               (TConst (px - cx)) (TConst (py - cy))
               (Rabs (px - cx)) (Rabs (py - cy)) Hb).
      * intro w; cbn [term_eval]; rewrite Rabs_pos_eq by lra; reflexivity.
      * intro w; cbn [term_eval]; rewrite Rabs_pos_eq by lra; reflexivity.
      * reflexivity.
      * intros r gamma; apply nl_block_pos; lra.
      * intros r gamma; apply nl_block_pos; lra.
  - intro ps; cbn [psatisfies]; intro H.
    apply psatisfies_p_eq in H.
    apply psatisfies_p_eq.
    symmetry; exact H.
Qed.
