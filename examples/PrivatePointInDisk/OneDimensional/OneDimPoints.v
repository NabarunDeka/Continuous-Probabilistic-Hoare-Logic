(**
  OneDimPoints.v -- the ONE-DIMENSIONAL private membership test, with the two
  POINTS perturbed independently.

      n1     <- sample(Laplace(0, b));
      n2     <- sample(Laplace(0, b));
      pp     := p + n1;                    (* perturbed point  *)
      cc     := c + n2;                    (* perturbed centre *)
      inside := (-1 < pp - cc  /\  pp - cc <= 1)

  THE TRIPLE ([op_correct], for [0 < b], writing [D] for [p - c]):

      { Pr[tt] = 1 }
          op_prog p c b
      { Pr[inside] = G_b(D + 1) - G_b(D - 1) }

  where [G_b] is the CDF of a difference of two independent Laplace(0,b)
  variables, computed in LaplaceCdfConvolution.v.

  WHY THIS IS THE INTERESTING HALF.  OneDimDistance.v perturbs the scalar
  difference and needs ONE integral.  Here each point carries its own noise,
  so the weakest precondition has TWO nested integrals and the event couples
  them -- exactly the shape that is unreachable in two dimensions.  It works
  here for one reason only: in one dimension "inside the unit ball" is the
  INTERVAL [-1 < x <= 1], whose sections have CONSTANT endpoints.  The inner
  integral is therefore a difference of Laplace CDFs, and the outer integral
  of a Laplace density against a Laplace CDF is exactly the cumulative
  convolution.

  In two dimensions the same program shape gives sections of a DISK, with
  endpoints [+/- sqrt(1 - t^2)], and no closed form exists.  So these two
  files together establish the sharp statement:

      independent double perturbation is NOT what blocks the disk variant --
      the disk is.

  See flags/FLAGS.md F14.

  A NOTE ON THE WINDOW.  The test here is [-1 < x <= 1] whereas
  OneDimDistance.v uses [-1 <= x < 1].  The asymmetry is forced: [n2] enters
  the difference NEGATED, so the inequalities flip, and CPHL.v offers only a
  strict-below closed form ([laplace_integral_strict_cdf], see F6).  Choosing
  the window this way makes the inner region half-open in the direction the
  available law can evaluate.  Under continuous noise the endpoints carry no
  mass, so the two conventions describe the same mechanism.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import ClassicalDescription.
From Stdlib Require Import Classical.
Require Import CPHL.
Require Import SampleBeforeLoop.
Require Import HalfLaplaceRejection.
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

(** The guard once both assignments have been substituted away. *)
Definition op_gap_sub (p c : R) : Term :=
  <{ ($(p) + op_n1) + $(op_minus_one) * ($(c) + op_n2) }>.

Definition op_guard (p c : R) : CFormula :=
  <{ ($(op_minus_one) < $(op_gap_sub p c)) /\ ($(op_gap_sub p c) <= 1) }>.

(** The answer. *)
Definition op_answer (p c b : R) : R :=
  (lcc_G b (op_D p c + 1) - lcc_G b (op_D p c - 1))%R.

(** * Bookkeeping *)

Lemma op_n1_neq_n2 : op_n1 <> op_n2.
Proof. unfold op_n1, op_n2; intro H; inversion H. Qed.

Lemma op_dec_neq :
  forall (x y : RealProgramVar) (A : Type) (a c : A),
    x <> y -> (if real_program_var_eq_dec x y then a else c) = c.
Proof.
  intros x y A a c H.
  destruct (real_program_var_eq_dec x y) as [He | He];
    [contradiction | reflexivity].
Qed.

Lemma op_q_eval_integral :
  forall (x : RealProgramVar) (d : Distribution) (q : PConstruct) (v : state),
    q_eval (QIntegral x d q) v =
    real_integral
      (fun k => distribution_density d v k * q_eval q (update_real v x k)).
Proof. reflexivity. Qed.

Lemma op_density_eq :
  forall (b : R) (v : state) (k : R),
    distribution_density (Laplace (TConst 0) (TConst b)) v k = lc_density b k.
Proof. intros b v k; symmetry; apply lc_density_is_laplace. Qed.

Lemma op_gap_value :
  forall (p c k1 k2 : R) (v : state),
    term_eval (op_gap_sub p c)
      (update_real (update_real v op_n1 k1) op_n2 k2) =
    (op_D p c + k1 - k2)%R.
Proof.
  intros p c k1 k2 v.
  unfold op_gap_sub, op_minus_one, op_D, update_real, update_real_values.
  cbn [term_eval real_program_values].
  rewrite (op_dec_neq op_n1 op_n2) by exact op_n1_neq_n2.
  rewrite !rpv_eq_dec_refl.
  ring.
Qed.

(** * The inner integral: a difference of Laplace CDFs *)

Lemma op_inner :
  forall (p c b k1 : R) (v : state),
    (0 < b)%R ->
    q_eval
      [[ integral op_n2 ~ $(Laplace (TConst 0) (TConst b)),
         indicator[ $(op_guard p c) ] ]]
      (update_real v op_n1 k1) =
    (laplace_cdf 0 b (k1 + (op_D p c + 1))
     - laplace_cdf 0 b (k1 + (op_D p c - 1)))%R.
Proof.
  intros p c b k1 v Hb.
  rewrite op_q_eval_integral.
  rewrite (real_integral_extensional
             _ (fun k2 =>
                  ((1 / (2 * b)) * exp (- Rabs (k2 - 0) / b))
                  * real_indicator (k2 < k1 + (op_D p c + 1))%R
                  - ((1 / (2 * b)) * exp (- Rabs (k2 - 0) / b))
                    * real_indicator (k2 < k1 + (op_D p c - 1))%R)).
  - rewrite od_integral_minus.
    rewrite !laplace_integral_strict_cdf by exact Hb.
    reflexivity.
  - intro k2.
    cbn [q_eval].
    rewrite (real_indicator_extensional
               _ ((k1 + (op_D p c - 1) <= k2 < k1 + (op_D p c + 1))%R)).
    + rewrite (od_window_indicator (k1 + (op_D p c - 1))
                 (k1 + (op_D p c + 1)) k2) by lra.
      cbn [distribution_density term_eval]; ring.
    + unfold op_guard.
      rewrite od_satisfies_c_and.
      unfold op_minus_one, c_lt.
      cbn [satisfies c_not term_eval].
      rewrite !op_gap_value.
      split.
      * intros [H1 H2]; split; lra.
      * intros [H1 H2]; split; lra.
Qed.

(** * The outer integral: the cumulative convolution *)

Lemma op_qeval :
  forall (p c b : R) (v : state),
    (0 < b)%R ->
    q_eval
      [[ integral op_n1 ~ $(Laplace (TConst 0) (TConst b)),
         integral op_n2 ~ $(Laplace (TConst 0) (TConst b)),
         indicator[ $(op_guard p c) ] ]] v =
    op_answer p c b.
Proof.
  intros p c b v Hb.
  unfold op_answer.
  rewrite op_q_eval_integral.
  rewrite (real_integral_extensional
             _ (fun k1 =>
                  lc_density b k1 * laplace_cdf 0 b (k1 + (op_D p c + 1))
                  - lc_density b k1 * laplace_cdf 0 b (k1 + (op_D p c - 1)))).
  - rewrite od_integral_minus.
    rewrite !lcc_convolution_cdf by exact Hb.
    reflexivity.
  - intro k1.
    rewrite op_density_eq.
    rewrite (op_inner p c b k1 v Hb).
    ring.
Qed.

(** * The weakest precondition

    Five commands, so four intermediate assertions.  Each is literally the
    weakest-precondition operator applied to the next, which is why the
    Hoare steps below are exact matches rather than consequences. *)

Definition op_post (p c b : R) : PFormula :=
  [[ Pr[op_inside] = $(op_answer p c b) ]].

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

(** The two assignments close the guard; [op_n1] and [op_n2] stay bound. *)
Lemma op_pre_shape :
  forall p c b : R,
    op_pre p c b =
    [[ E[ integral op_n1 ~ $(Laplace (TConst 0) (TConst b)),
          integral op_n2 ~ $(Laplace (TConst 0) (TConst b)),
          indicator[ $(op_guard p c) ] ]
       = $(op_answer p c b) ]].
Proof. intros; reflexivity. Qed.

Lemma op_normalized_implies_pre :
  forall p c b : R,
    (0 < b)%R ->
    pformula_valid [[ Pr[true] = 1 -> $(op_pre p c b) ]].
Proof.
  intros p c b Hb ps Hadm.
  cbn [psatisfies]; intro Hnorm.
  apply psatisfies_p_eq in Hnorm.
  cbn [pterm_eval] in Hnorm.
  rewrite op_pre_shape.
  apply psatisfies_p_eq.
  cbn [pterm_eval].
  apply t3_expect_const.
  - exact Hnorm.
  - intro v; apply op_qeval; exact Hb.
Qed.

Lemma op_noise_valid_under :
  forall (b : R) (pre : PFormula),
    (0 < b)%R ->
    pformula_valid
      [[ $(pre) -> almost_sure[$(distribution_valid_formula (op_noise b))] ]].
Proof.
  intros b pre Hb ps Hadm.
  cbn [psatisfies]; intro Hignore.
  clear Hignore; revert ps.
  apply p_almost_sure_of_pointwise.
  intro v.
  unfold op_noise.
  cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
  intro Hle; lra.
Qed.

(** * The mechanism *)

Theorem op_correct :
  forall p c b : R,
    (0 < b)%R ->
    {{ Pr[true] = 1 }}
      $(op_prog p c b)
    {{ Pr[op_inside] = $(op_answer p c b) }}.
Proof.
  intros p c b Hb.
  unfold op_prog.
  eapply HSeq with (eta2 := op_s1 p c b).
  - apply HRealSample.
    + apply op_normalized_implies_pre; exact Hb.
    + apply op_noise_valid_under; exact Hb.
  - eapply HSeq with (eta2 := op_s2 p c b).
    + apply HRealSample.
      * intro ps; cbn [psatisfies]; intro H; exact H.
      * apply op_noise_valid_under; exact Hb.
    + eapply HSeq with (eta2 := op_s3 p c b).
      * apply HRealAssign.
      * eapply HSeq with (eta2 := op_s4 p c b).
        -- apply HRealAssign.
        -- apply HBoolAssign.
Qed.

(** * Comparing the two one-dimensional mechanisms

    Both decide the same question with the same per-draw noise scale, but
    perturbing the two points independently injects the DIFFERENCE of two
    Laplace draws rather than a single one.  At the hardest input -- a point
    exactly at the centre, where the answer should be "inside" -- that costs
    accuracy, and the loss is exactly [exp(-1/b) / (2b)]. *)

Lemma od_answer_centre :
  forall p b : R,
    (0 < b)%R -> od_answer p p b = (1 - exp (-1 / b))%R.
Proof.
  intros p b Hb.
  assert (Hb2 : (b <> 0)%R) by lra.
  unfold od_answer, od_D, laplace_cdf.
  replace (1 - (p - p))%R with 1%R by ring.
  replace (-1 - (p - p))%R with (-1)%R by ring.
  destruct (Rle_dec 1 0) as [H1 | H1]; [lra |].
  destruct (Rle_dec (-1) 0) as [H2 | H2]; [| lra].
  replace (- (1 - 0) / b)%R with (-1 / b)%R by (field; exact Hb2).
  replace ((-1 - 0) / b)%R with (-1 / b)%R by (field; exact Hb2).
  field; exact Hb2.
Qed.

Lemma op_answer_centre :
  forall p b : R,
    (0 < b)%R ->
    op_answer p p b = (1 - (1 + 1 / (2 * b)) * exp (-1 / b))%R.
Proof.
  intros p b Hb.
  assert (Hb2 : (b <> 0)%R) by lra.
  unfold op_answer, op_D, lcc_G.
  replace (p - p + 1)%R with 1%R by ring.
  replace (p - p - 1)%R with (-1)%R by ring.
  destruct (Rle_dec 1 0) as [H1 | H1]; [lra |].
  destruct (Rle_dec (-1) 0) as [H2 | H2]; [| lra].
  replace (- (1) / b)%R with (-1 / b)%R by (field; exact Hb2).
  field; exact Hb2.
Qed.

(** Perturbing the two points is strictly less accurate than perturbing the
    difference, by exactly [exp(-1/b) / (2b)]. *)
Corollary op_less_accurate_than_od :
  forall p b : R,
    (0 < b)%R ->
    (od_answer p p b - op_answer p p b)%R = (exp (-1 / b) / (2 * b))%R
    /\ (op_answer p p b < od_answer p p b)%R.
Proof.
  intros p b Hb.
  assert (Hb2 : (b <> 0)%R) by lra.
  assert (Hpos : (0 < exp (-1 / b))%R) by apply exp_pos.
  assert (Hinv : (0 < / (2 * b))%R) by (apply Rinv_0_lt_compat; lra).
  rewrite (od_answer_centre p b Hb), (op_answer_centre p b Hb).
  split.
  - field; exact Hb2.
  - assert (Hgap : (0 < exp (- 1 / b) / (2 * b))%R)
      by (unfold Rdiv; apply Rmult_lt_0_compat; assumption).
    lra.
Qed.
