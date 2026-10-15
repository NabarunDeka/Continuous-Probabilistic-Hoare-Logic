(**
  OneDimDistance.v

  Program ([od_prog p c b]):
      e := p - c;
      n <- sample(laplace(0, b));
      e := e + n;
      inside := (-1 <= e /\ e < 1)
  Triple ([od_correct], for 0 < b; post [od_post], D := [od_diff p c]):
      { Pr[true] = 1 }
        od_prog p c b
      { Pr[inside] = E[ integral z ~ laplace(0, b), indicator[z <= 1 - D] ]
                     - E[ integral z ~ laplace(0, b), indicator[z <= -1 - D] ] }
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import Classical.
Require Import CPHL.
Require Import SampleBeforeLoop.
Require Import CdfAssertions.
Require Import DiskLaplaceFacts.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * The program

    [p] and [c] are Rocq reals, so [od_diff] is a closed term in the
    parameters. *)

Definition od_e : RealProgramVar := real_program_var "od_e".
Definition od_n : RealProgramVar := real_program_var "od_n".
Definition od_z : RealProgramVar := real_program_var "od_z".
Definition od_inside : BoolProgramVar := bool_program_var "od_inside".

Definition od_minus_one : Term := TConst (-1).

Definition od_diff (p c : R) : Term := <{ $(p) + $(od_minus_one) * $(c) }>.

Definition od_D (p c : R) : R := (p - c)%R.

Definition od_noise (b : R) : Distribution := <{ laplace(0, b) }>.

Definition od_shift : Term := <{ od_e + od_n }>.

Definition od_window : CFormula :=
  <{ ($(od_minus_one) <= od_e) /\ (od_e < 1) }>.

Definition od_prog (p c b : R) : Cmd :=
  <{ od_e      := $(od_diff p c);
     od_n      sample $(od_noise b);
     od_e      := $(od_shift);
     od_inside b= $(od_window) }>.

(** * The postcondition: the Laplace mass of the window, as two syntactic
    CDFs at the cutoffs [1 - D] and [-1 - D]. *)

Definition od_hi (p c : R) : Term := <{ 1 + $(od_minus_one) * $(od_diff p c) }>.
Definition od_lo (p c : R) : Term :=
  <{ $(od_minus_one) + $(od_minus_one) * $(od_diff p c) }>.

Definition od_cdf (p c b : R) (cut : Term) : PConstruct :=
  [[ integral od_z ~ $(od_noise b), indicator[od_z <= $(cut)] ]].

Definition od_answer (p c b : R) : Pterm :=
  p_sub (PExpect (od_cdf p c b (od_hi p c))) (PExpect (od_cdf p c b (od_lo p c))).

Definition od_post (p c b : R) : PFormula :=
  [[ Pr[od_inside] = $(od_answer p c b) ]].

(** * Small facts *)

(** A half-open window is the difference of two half-lines. *)
Lemma od_window_indicator :
  forall A B z : R,
    (A <= B)%R ->
    real_indicator (A <= z < B)%R =
    (real_indicator (z < B)%R - real_indicator (z < A)%R)%R.
Proof.
  intros A B z Hab.
  destruct (Rlt_dec z A) as [H1 | H1].
  - rewrite (real_indicator_false (A <= z < B)%R) by (intros [Ha _]; lra).
    rewrite (real_indicator_true (z < A)%R H1).
    rewrite (real_indicator_true (z < B)%R) by lra.
    ring.
  - destruct (Rlt_dec z B) as [H2 | H2].
    + rewrite (real_indicator_true (A <= z < B)%R
                 (conj (Rnot_lt_le _ _ H1) H2)).
      rewrite (real_indicator_false (z < A)%R) by lra.
      rewrite (real_indicator_true (z < B)%R H2).
      ring.
    + rewrite (real_indicator_false (A <= z < B)%R) by (intros [_ Hb]; lra).
      rewrite (real_indicator_false (z < A)%R) by lra.
      rewrite (real_indicator_false (z < B)%R) by lra.
      ring.
Qed.

Lemma od_diff_value :
  forall (p c : R) (v : state),
    term_eval (od_diff p c) v = od_D p c.
Proof.
  intros p c v.
  unfold od_diff, od_minus_one, od_D.
  cbn [term_eval]; ring.
Qed.

(** [c_and] is encoded through implication, so unpacking it is classical. *)
Lemma od_satisfies_c_and :
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


Lemma od_hi_value :
  forall (p c : R) (v : state), term_eval (od_hi p c) v = 1 - od_D p c.
Proof. intros; unfold od_hi, od_diff, od_minus_one, od_D; cbn [term_eval]; ring. Qed.

Lemma od_lo_value :
  forall (p c : R) (v : state), term_eval (od_lo p c) v = -1 - od_D p c.
Proof. intros; unfold od_lo, od_diff, od_minus_one, od_D; cbn [term_eval]; ring. Qed.


Lemma od_cdf_value :
  forall (p c b : R) (cut : Term) (k : R) (v : state),
    0 < b ->
    (forall w, term_eval cut w = k) ->
    q_eval (od_cdf p c b cut) v = lap_atmost 0 b k.
Proof.
  intros p c b cut k v Hb Hcut.
  unfold od_cdf, od_noise.
  apply (disk_laplace_indicator od_z _ 0 b _ (fun r => r <= k)).
  - exact Hb.
  - reflexivity.
  - intro r; cbn [satisfies]; rewrite update_real_same, Hcut; reflexivity.
Qed.

(** * The weakest preconditions *)

Definition od_after_add (p c b : R) : PFormula :=
  subst_bool_pformula od_inside od_window (od_post p c b).

Definition od_after_sample (p c b : R) : PFormula :=
  subst_real_pformula od_e od_shift (od_after_add p c b).

Definition od_after_assign (p c b : R) : PFormula :=
  sample_pformula od_n (od_noise b) (od_after_sample p c b).

Definition od_guard (p c : R) : CFormula :=
  <{ ($(od_minus_one) <= $(od_diff p c) + od_n) /\ ($(od_diff p c) + od_n < 1) }>.

Definition od_pre (p c b : R) : PFormula :=
  [[ E[ integral od_n ~ $(od_noise b), indicator[ $(od_guard p c) ] ]
     = $(p_sub
           (PExpect (QIntegral od_n (od_noise b) (od_cdf p c b (od_hi p c))))
           (PExpect (QIntegral od_n (od_noise b) (od_cdf p c b (od_lo p c))))) ]].

Lemma od_pre_is_wp :
  forall p c b : R,
    subst_real_pformula od_e (od_diff p c) (od_after_assign p c b) =
    od_pre p c b.
Proof. intros; vm_compute; reflexivity. Qed.

(** * Evaluating the pieces *)

Lemma od_guard_value :
  forall (p c b : R) (v : state),
    0 < b ->
    q_eval [[ integral od_n ~ $(od_noise b), indicator[ $(od_guard p c) ] ]] v
    = lap_atmost 0 b (1 - od_D p c) - lap_atmost 0 b (-1 - od_D p c).
Proof.
  intros p c b v Hb.
  unfold od_noise.
  rewrite (disk_laplace_indicator od_n _ 0 b _
             (fun r => -1 - od_D p c <= r < 1 - od_D p c)).
  - apply disk_lap_window; [exact Hb | lra].
  - exact Hb.
  - reflexivity.
  - intro r; unfold od_guard.
    rewrite od_satisfies_c_and.
    unfold od_minus_one, c_lt.
    cbn [satisfies c_not].
    change (term_eval (TAdd (od_diff p c) (TProgVar od_n)) (update_real v od_n r))
      with (term_eval (od_diff p c) (update_real v od_n r)
            + term_eval (TProgVar od_n) (update_real v od_n r)).
    rewrite update_real_same, od_diff_value.
    cbn [term_eval].
    split; intros [H1 H2]; split; lra.
Qed.

Lemma od_pre_valid :
  forall p c b : R,
    0 < b ->
    pformula_valid [[ Pr[true] = 1 -> $(od_pre p c b) ]].
Proof.
  intros p c b Hb ps Hadm.
  cbn [psatisfies]; intros _.
  unfold od_pre; apply psatisfies_p_eq.
  rewrite pterm_eval_p_sub; cbn [pterm_eval].
  rewrite (expect_const_construct _ _ _ (fun v => od_guard_value p c b v Hb)).
  rewrite (expect_const_construct _
             (QIntegral od_n (od_noise b) (od_cdf p c b (od_hi p c)))
             (lap_atmost 0 b (1 - od_D p c))).
  2:{ intro v; apply disk_integral_const.
      - cbn [distribution_valid od_noise term_eval]; exact Hb.
      - intro w; apply od_cdf_value; [exact Hb | apply od_hi_value]. }
  rewrite (expect_const_construct _
             (QIntegral od_n (od_noise b) (od_cdf p c b (od_lo p c)))
             (lap_atmost 0 b (-1 - od_D p c))).
  2:{ intro v; apply disk_integral_const.
      - cbn [distribution_valid od_noise term_eval]; exact Hb.
      - intro w; apply od_cdf_value; [exact Hb | apply od_lo_value]. }
  ring.
Qed.

Lemma od_noise_valid_under :
  forall (b : R) (pre : PFormula),
    0 < b ->
    pformula_valid
      [[ $(pre) -> almost_sure[$(distribution_valid_formula (od_noise b))] ]].
Proof.
  intros b pre Hb ps Hadm.
  cbn [psatisfies]; intros _.
  revert ps Hadm.
  apply p_almost_sure_of_pointwise.
  intro v.
  unfold od_noise.
  cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
  intro Hle; lra.
Qed.

(** * The mechanism *)

Theorem od_correct :
  forall p c b : R,
    0 < b ->
    {{ Pr[true] = 1 }}
      $(od_prog p c b)
    {{ $(od_post p c b) }}.
Proof.
  intros p c b Hb.
  unfold od_prog.
  eapply HSeq with (eta2 := od_after_assign p c b).
  - eapply HConseq with
      (eta1 := subst_real_pformula od_e (od_diff p c) (od_after_assign p c b))
      (eta2 := od_after_assign p c b).
    + rewrite od_pre_is_wp.
      apply od_pre_valid; exact Hb.
    + apply HRealAssign.
    + intros ps _; cbn [psatisfies]; tauto.
  - eapply HSeq with (eta2 := od_after_sample p c b).
    + apply HRealSample.
      * intros ps _; cbn [psatisfies]; intro H; exact H.
      * apply od_noise_valid_under; exact Hb.
    + eapply HSeq with (eta2 := od_after_add p c b).
      * apply HRealAssign.
      * apply HBoolAssign.
Qed.

(** * Closed form, for comparison only (not used in any triple) *)

Lemma od_answer_value :
  forall (p c b : R) (ps : Pstate),
    0 < b ->
    pterm_eval (od_answer p c b) ps =
    (lap_atmost 0 b (1 - od_D p c) - lap_atmost 0 b (-1 - od_D p c)) *
      expectation (pstate_measure ps) (q_eval (QIndicator c_true)).
Proof.
  intros p c b ps Hb.
  unfold od_answer; rewrite pterm_eval_p_sub; cbn [pterm_eval].
  rewrite (expect_const_construct _ (od_cdf p c b (od_hi p c))
             (lap_atmost 0 b (1 - od_D p c)))
    by (intro v; apply od_cdf_value; [exact Hb | apply od_hi_value]).
  rewrite (expect_const_construct _ (od_cdf p c b (od_lo p c))
             (lap_atmost 0 b (-1 - od_D p c)))
    by (intro v; apply od_cdf_value; [exact Hb | apply od_lo_value]).
  ring.
Qed.

(** At a point exactly on the centre the window mass is [1 - exp(-1/b)]. *)
Lemma od_window_centre :
  forall p b : R,
    0 < b ->
    lap_atmost 0 b (1 - od_D p p) - lap_atmost 0 b (-1 - od_D p p)
    = 1 - exp (-1 / b).
Proof.
  intros p b Hb.
  unfold od_D.
  replace (1 - (p - p)) with 1 by ring.
  replace (-1 - (p - p)) with (-1) by ring.
  rewrite !disk_lap_atmost_closed by exact Hb.
  rewrite Rminus_0_r, Rminus_0_r.
  rewrite disk_F_nonneg by lra.
  rewrite disk_F_nonpos by lra.
  replace (- (1) / b) with (-1 / b) by (field; lra).
  field.
Qed.
