(**
  OneDimPoints.v

  Program ([op_prog p c b]):
      n1 <- sample(laplace(0, b));
      n2 <- sample(laplace(0, b));
      pp := p + n1;
      cc := c + n2;
      inside := (-1 < pp - cc /\ pp - cc <= 1)
  Triple ([op_correct], for 0 < b; post [op_post], D := [p - c],
          G(t) := E[ integral u ~ laplace(0, b), integral w ~ laplace(0, b),
                     indicator[w <= u + t] ]  ([op_G]):
      { Pr[true] = 1 }
        op_prog p c b
      { Pr[inside] = G(D + 1) - G(D - 1) }
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
Require Import MeasureIntegration CPHL.
Require Import CPHLFacts.CalculationFacts.
Require Import SampleBeforeLoop.
Require Import CdfAssertions.
Require Import DiskLaplaceFacts.
Require Import LaplaceConvolution.
Require Import LaplaceCdfConvolution.
Require Import OneDimDistance.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * The program *)

Definition op_pp : RealProgramVar := real_program_var "op_pp".
Definition op_cc : RealProgramVar := real_program_var "op_cc".
Definition op_n1 : RealProgramVar := real_program_var "op_n1".
Definition op_n2 : RealProgramVar := real_program_var "op_n2".
Definition op_u : RealProgramVar := real_program_var "op_u".
Definition op_w : RealProgramVar := real_program_var "op_w".
Definition op_inside : BoolProgramVar := bool_program_var "op_inside".

Definition op_minus_one : Term := TConst (-1).

Definition op_gap : Term := <{ op_pp + $(op_minus_one) * op_cc }>.

Definition op_window : CFormula :=
  <{ ($(op_minus_one) < $(op_gap)) /\ ($(op_gap) <= 1) }>.

Definition op_noise (b : R) : Distribution := <{ laplace(0, b) }>.

Definition op_prog (p c b : R) : Cmd :=
  <{ op_n1   sample $(op_noise b);
     op_n2   sample $(op_noise b);
     op_pp   := $(p) + op_n1;
     op_cc   := $(c) + op_n2;
     op_inside b= $(op_window) }>.

Definition op_D (p c : R) : R := (p - c)%R.

(** * The postcondition *)

(** [D + 1] and [D - 1] as closed terms. *)
Definition op_Dp (p c : R) : Term := <{ $(p) + $(op_minus_one) * $(c) + 1 }>.
Definition op_Dm (p c : R) : Term :=
  <{ $(p) + $(op_minus_one) * $(c) + $(op_minus_one) }>.

(** The CDF at [t] of the difference [w - u] of two Laplace(0, b) draws,
    written with binders [x] (outer) and [y] (inner). *)
Definition op_Gq (x y : RealProgramVar) (b : R) (t : Term) : PConstruct :=
  QIntegral x (op_noise b)
    (QIntegral y (op_noise b) (QIndicator (FLe (TProgVar y) (TAdd (TProgVar x) t)))).

Definition op_G (b : R) (t : Term) : Pterm := PExpect (op_Gq op_u op_w b t).

Definition op_answer (p c b : R) : Pterm :=
  p_sub (op_G b (op_Dp p c)) (op_G b (op_Dm p c)).

Definition op_post (p c b : R) : PFormula :=
  [[ Pr[op_inside] = $(op_answer p c b) ]].

(** * The weakest preconditions *)

Definition op_s4 (p c b : R) : PFormula :=
  subst_bool_pformula op_inside op_window (op_post p c b).

Definition op_s3 (p c b : R) : PFormula :=
  subst_real_pformula op_cc <{ $(c) + op_n2 }> (op_s4 p c b).

Definition op_s2 (p c b : R) : PFormula :=
  subst_real_pformula op_pp <{ $(p) + op_n1 }> (op_s3 p c b).

Definition op_s1 (p c b : R) : PFormula :=
  sample_pformula op_n2 (op_noise b) (op_s2 p c b).

Definition op_pre (p c b : R) : PFormula :=
  sample_pformula op_n1 (op_noise b) (op_s1 p c b).

(** The guard once both assignments have been substituted away. *)
Definition op_gap_sub (p c : R) : Term :=
  <{ ($(p) + op_n1) + $(op_minus_one) * ($(c) + op_n2) }>.

Definition op_guard (p c : R) : CFormula :=
  <{ ($(op_minus_one) < $(op_gap_sub p c)) /\ ($(op_gap_sub p c) <= 1) }>.

Definition op_wrap (b : R) (q : PConstruct) : PConstruct :=
  QIntegral op_n1 (op_noise b) (QIntegral op_n2 (op_noise b) q).

Lemma op_pre_shape :
  forall p c b : R,
    op_pre p c b =
    p_eq (PExpect (op_wrap b (QIndicator (op_guard p c))))
      (p_sub (PExpect (op_wrap b (op_Gq op_u op_w b (op_Dp p c))))
             (PExpect (op_wrap b (op_Gq op_u op_w b (op_Dm p c))))).
Proof. intros; vm_compute; reflexivity. Qed.

(** * Evaluation *)

Lemma op_lookup_other :
  forall (v : state) (x y : RealProgramVar) (k r : R),
    x <> y ->
    term_eval (TProgVar x) (update_real (update_real v x k) y r) = k.
Proof.
  intros v x y k r Hxy.
  cbn [term_eval update_real real_program_values].
  unfold update_real_values.
  destruct (real_program_var_eq_dec x y) as [He | _]; [contradiction |].
  destruct (real_program_var_eq_dec x x) as [_ | Hn]; [reflexivity | contradiction].
Qed.

(** The real value of the difference CDF. *)
Definition op_gval (b t : R) : R :=
  real_integral (fun k => lap_density 0 b k * lap_atmost 0 b (k + t)).

Lemma op_Gq_value :
  forall (x y : RealProgramVar) (b : R) (T : Term) (t : R) (v : state),
    0 < b -> x <> y ->
    (forall w, term_eval T w = t) ->
    q_eval (op_Gq x y b T) v = op_gval b t.
Proof.
  intros x y b T t v Hb Hxy HT.
  unfold op_Gq.
  rewrite q_integral_density by (cbn [distribution_valid op_noise term_eval]; exact Hb).
  apply real_integral_extensional; intro k.
  f_equal.
  unfold op_noise.
  apply (disk_laplace_indicator y _ 0 b _ (fun r => r <= k + t)).
  - exact Hb.
  - reflexivity.
  - intro r; cbn [satisfies].
    rewrite update_real_same.
    change (term_eval (TAdd (TProgVar x) T) (update_real (update_real v x k) y r))
      with (term_eval (TProgVar x) (update_real (update_real v x k) y r)
            + term_eval T (update_real (update_real v x k) y r)).
    rewrite (op_lookup_other v x y k r Hxy), HT; reflexivity.
Qed.

Lemma op_n1_neq_n2 : op_n1 <> op_n2.
Proof. unfold op_n1, op_n2; intro H; inversion H. Qed.

Lemma op_u_neq_w : op_u <> op_w.
Proof. unfold op_u, op_w; intro H; inversion H. Qed.

Lemma op_Dp_value : forall p c w, term_eval (op_Dp p c) w = op_D p c + 1.
Proof. intros; unfold op_Dp, op_minus_one, op_D; cbn [term_eval]; ring. Qed.

Lemma op_Dm_value : forall p c w, term_eval (op_Dm p c) w = op_D p c - 1.
Proof. intros; unfold op_Dm, op_minus_one, op_D; cbn [term_eval]; ring. Qed.

(** The inner window integral is a difference of two Laplace CDFs. *)
Lemma op_inner :
  forall (p c b : R) (w : state),
    0 < b ->
    q_eval (QIntegral op_n2 (op_noise b) (QIndicator (op_guard p c))) w +
    q_eval (QIntegral op_n2 (op_noise b)
              (QIndicator (FLe (TProgVar op_n2) (TAdd (TProgVar op_n1) (op_Dm p c))))) w =
    q_eval (QIntegral op_n2 (op_noise b)
              (QIndicator (FLe (TProgVar op_n2) (TAdd (TProgVar op_n1) (op_Dp p c))))) w.
Proof.
  intros p c b w Hb.
  set (k1 := term_eval (TProgVar op_n1) w).
  assert (Hk1 : forall r, term_eval (TProgVar op_n1) (update_real w op_n2 r) = k1).
  { intro r; unfold k1; cbn [term_eval update_real real_program_values].
    unfold update_real_values.
    destruct (real_program_var_eq_dec op_n1 op_n2) as [He | _];
      [exfalso; exact (op_n1_neq_n2 He) | reflexivity]. }
  unfold op_noise.
  rewrite (disk_laplace_indicator op_n2 _ 0 b _
             (fun r => k1 + (op_D p c - 1) <= r < k1 + (op_D p c + 1))).
  rewrite (disk_laplace_indicator op_n2 _ 0 b _
             (fun r => r <= k1 + (op_D p c - 1))).
  rewrite (disk_laplace_indicator op_n2 _ 0 b _
             (fun r => r <= k1 + (op_D p c + 1))).
  - rewrite (disk_lap_window 0 b _ _ Hb) by lra.
    change (real_integral (fun r => lap_density 0 b r * real_indicator (r <= k1 + (op_D p c - 1))))
      with (lap_atmost 0 b (k1 + (op_D p c - 1))).
    change (real_integral (fun r => lap_density 0 b r * real_indicator (r <= k1 + (op_D p c + 1))))
      with (lap_atmost 0 b (k1 + (op_D p c + 1))).
    ring.
  all: try exact Hb; try reflexivity.
  - intro r; cbn [satisfies]; rewrite update_real_same.
    change (term_eval (TAdd (TProgVar op_n1) (op_Dp p c)) (update_real w op_n2 r))
      with (term_eval (TProgVar op_n1) (update_real w op_n2 r)
            + term_eval (op_Dp p c) (update_real w op_n2 r)).
    rewrite Hk1, op_Dp_value; reflexivity.
  - intro r; cbn [satisfies]; rewrite update_real_same.
    change (term_eval (TAdd (TProgVar op_n1) (op_Dm p c)) (update_real w op_n2 r))
      with (term_eval (TProgVar op_n1) (update_real w op_n2 r)
            + term_eval (op_Dm p c) (update_real w op_n2 r)).
    rewrite Hk1, op_Dm_value; reflexivity.
  - assert (E : forall r, term_eval (op_gap_sub p c) (update_real w op_n2 r)
                         = op_D p c + k1 - r).
    { intro r'.
      pose proof (Hk1 r') as E1.
      pose proof (update_real_same w op_n2 r') as E2.
      unfold op_gap_sub, op_minus_one, op_D.
      cbn [term_eval] in E1, E2 |- *.
      rewrite E1, E2; ring. }
    intro r; unfold op_guard.
    rewrite od_satisfies_c_and.
    unfold c_lt.
    cbn [satisfies c_not].
    rewrite !E.
    unfold op_minus_one; cbn [term_eval].
    split; intros [H1 H2]; split; lra.
Qed.

Lemma op_lhs_value :
  forall (p c b : R) (v : state),
    0 < b ->
    q_eval (op_wrap b (QIndicator (op_guard p c))) v =
    op_gval b (op_D p c + 1) - op_gval b (op_D p c - 1).
Proof.
  intros p c b v Hb.
  pose proof (q_integral_partition op_n1 (op_noise b) _ _ _
                (fun w => op_inner p c b w Hb) v) as Hpart.
  fold (op_wrap b (QIndicator (op_guard p c))) in Hpart.
  change (QIntegral op_n1 (op_noise b) (QIntegral op_n2 (op_noise b)
            (QIndicator (FLe (TProgVar op_n2) (TAdd (TProgVar op_n1) (op_Dm p c))))))
    with (op_Gq op_n1 op_n2 b (op_Dm p c)) in Hpart.
  change (QIntegral op_n1 (op_noise b) (QIntegral op_n2 (op_noise b)
            (QIndicator (FLe (TProgVar op_n2) (TAdd (TProgVar op_n1) (op_Dp p c))))))
    with (op_Gq op_n1 op_n2 b (op_Dp p c)) in Hpart.
  rewrite (op_Gq_value _ _ b _ (op_D p c - 1) v Hb op_n1_neq_n2 (op_Dm_value p c)) in Hpart.
  rewrite (op_Gq_value _ _ b _ (op_D p c + 1) v Hb op_n1_neq_n2 (op_Dp_value p c)) in Hpart.
  lra.
Qed.

Lemma op_wrap_G_value :
  forall (b : R) (T : Term) (t : R) (v : state),
    0 < b -> (forall w, term_eval T w = t) ->
    q_eval (op_wrap b (op_Gq op_u op_w b T)) v = op_gval b t.
Proof.
  intros b T t v Hb HT.
  unfold op_wrap.
  apply disk_integral_const; [cbn [distribution_valid op_noise term_eval]; exact Hb |].
  intro w; apply disk_integral_const; [cbn [distribution_valid op_noise term_eval]; exact Hb |].
  intro w'; apply op_Gq_value; [exact Hb | exact op_u_neq_w | exact HT].
Qed.

Lemma op_pre_valid :
  forall p c b : R,
    0 < b ->
    pformula_valid [[ Pr[true] = 1 -> $(op_pre p c b) ]].
Proof.
  intros p c b Hb ps Hadm.
  cbn [psatisfies]; intros _.
  rewrite op_pre_shape.
  apply psatisfies_p_eq.
  rewrite pterm_eval_p_sub; cbn [pterm_eval].
  rewrite (expect_const_construct _ (op_wrap b (QIndicator (op_guard p c)))
             _ (fun v => op_lhs_value p c b v Hb)).
  rewrite (expect_const_construct _ (op_wrap b (op_Gq op_u op_w b (op_Dp p c)))
             (op_gval b (op_D p c + 1)))
    by (intro v; apply op_wrap_G_value; [exact Hb | apply op_Dp_value]).
  rewrite (expect_const_construct _ (op_wrap b (op_Gq op_u op_w b (op_Dm p c)))
             (op_gval b (op_D p c - 1)))
    by (intro v; apply op_wrap_G_value; [exact Hb | apply op_Dm_value]).
  ring.
Qed.

Lemma op_noise_valid_under :
  forall (b : R) (pre : PFormula),
    0 < b ->
    pformula_valid
      [[ $(pre) -> almost_sure[$(distribution_valid_formula (op_noise b))] ]].
Proof.
  intros b pre Hb ps Hadm.
  cbn [psatisfies]; intros _.
  revert ps Hadm.
  apply p_almost_sure_of_pointwise.
  intro v.
  unfold op_noise.
  cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
  intro Hle; lra.
Qed.

(** * The mechanism *)

Theorem op_correct :
  forall p c b : R,
    0 < b ->
    {{ Pr[true] = 1 }}
      $(op_prog p c b)
    {{ $(op_post p c b) }}.
Proof.
  intros p c b Hb.
  unfold op_prog.
  eapply HSeq with (eta2 := op_s1 p c b).
  - apply HRealSample.
    + apply op_pre_valid; exact Hb.
    + apply op_noise_valid_under; exact Hb.
  - eapply HSeq with (eta2 := op_s2 p c b).
    + apply HRealSample.
      * intros ps _; cbn [psatisfies]; intro H; exact H.
      * apply op_noise_valid_under; exact Hb.
    + eapply HSeq with (eta2 := op_s3 p c b).
      * apply HRealAssign.
      * eapply HSeq with (eta2 := op_s4 p c b).
        -- apply HRealAssign.
        -- apply HBoolAssign.
Qed.

(** * Closed forms, for comparison only (not used in any triple) *)

(** The syntactic difference CDF evaluates to [lcc_G] times the mass. *)
Lemma op_G_closed :
  forall (b : R) (T : Term) (t : R) (ps : Pstate),
    0 < b -> (forall w, term_eval T w = t) ->
    pterm_eval (op_G b T) ps =
    lcc_G b t * expectation (pstate_measure ps) (q_eval (QIndicator c_true)).
Proof.
  intros b T t ps Hb HT.
  unfold op_G; cbn [pterm_eval].
  rewrite (expect_const_construct _ _ (op_gval b t))
    by (intro v; apply op_Gq_value; [exact Hb | exact op_u_neq_w | exact HT]).
  f_equal.
  unfold op_gval.
  rewrite <- (lcc_convolution_cdf b t Hb).
  apply real_integral_extensional; intro k.
  unfold lap_density, lc_density; rewrite Rminus_0_r; reflexivity.
Qed.

Lemma op_gval_closed : forall b t : R, 0 < b -> op_gval b t = lcc_G b t.
Proof.
  intros b t Hb; unfold op_gval.
  rewrite <- (lcc_convolution_cdf b t Hb).
  apply real_integral_extensional; intro k.
  unfold lap_density, lc_density; rewrite Rminus_0_r; reflexivity.
Qed.

(** At a point exactly on the centre, perturbing the two points separately
    is less accurate than perturbing the difference (OneDimDistance.v), by
    exactly [exp(-1/b) / (2b)]. *)
Lemma op_window_centre :
  forall p b : R,
    0 < b ->
    op_gval b (op_D p p + 1) - op_gval b (op_D p p - 1)
    = 1 - (1 + 1 / (2 * b)) * exp (-1 / b).
Proof.
  intros p b Hb.
  rewrite !op_gval_closed by exact Hb.
  unfold op_D, lcc_G.
  replace (p - p + 1) with 1 by ring.
  replace (p - p - 1) with (-1) by ring.
  destruct (Rle_dec 1 0) as [H1 | H1]; [lra |].
  destruct (Rle_dec (-1) 0) as [H2 | H2]; [| lra].
  replace (- (1) / b) with (-1 / b) by (field; lra).
  field; lra.
Qed.

Corollary op_less_accurate_than_od :
  forall p b : R,
    0 < b ->
    let od := lap_atmost 0 b (1 - od_D p p) - lap_atmost 0 b (-1 - od_D p p) in
    let op := op_gval b (op_D p p + 1) - op_gval b (op_D p p - 1) in
    od - op = exp (-1 / b) / (2 * b) /\ op < od.
Proof.
  intros p b Hb od op.
  unfold od, op.
  rewrite (od_window_centre p b Hb), (op_window_centre p b Hb).
  assert (Hpos : 0 < exp (-1 / b)) by apply exp_pos.
  assert (Hgap : 0 < exp (-1 / b) / (2 * b))
    by (unfold Rdiv; apply Rmult_lt_0_compat; [exact Hpos | apply Rinv_0_lt_compat; lra]).
  split; [field; lra |].
  assert (E : 1 - exp (-1 / b) - (1 - (1 + 1 / (2 * b)) * exp (-1 / b))
              = exp (-1 / b) / (2 * b)) by (field; lra).
  lra.
Qed.
