(**
  PointInDiskAdditive.v

  Program ([pda_prog px py cx cy b]):
      d := (px - cx)^2 + (py - cy)^2;
      n <- sample(laplace(0, b));
      d := d + n;
      inside := (d < 1)
  Triple ([pda_correct], for 0 < b; post [pda_post], D := [pdi_sqdist px py cx cy]):
      { Pr[true] = 1 }
        pda_prog px py cx cy b
      { Pr[inside] = E[ integral z ~ laplace(D, b), indicator[z <= 1] ] }
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
Require Import CPHL.
Require Import SampleBeforeLoop.
Require Import CdfAssertions.
Require Import DiskLaplaceFacts.
Require Import PointInDiskInPlace.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * The program

    As in PointInDiskInPlace.v the four coordinates are Rocq reals, so
    [pda_sqdist] is a closed polynomial term in the parameters. *)

Definition pda_d : RealProgramVar := real_program_var "pda_d".
Definition pda_n : RealProgramVar := real_program_var "pda_n".
Definition pda_inside : BoolProgramVar := bool_program_var "pda_inside".

Definition pda_minus_one : Term := TConst (-1).

Definition pda_delta (u w : R) : Term := <{ $(u) + $(pda_minus_one) * $(w) }>.

Definition pda_sqdist (px py cx cy : R) : Term :=
  <{ ($(pda_delta px cx) * $(pda_delta px cx))
     + ($(pda_delta py cy) * $(pda_delta py cy)) }>.

Definition pda_D (px py cx cy : R) : R :=
  ((px - cx) * (px - cx) + (py - cy) * (py - cy))%R.

(** Centred noise, in its own variable. *)
Definition pda_noise (b : R) : Distribution := <{ laplace(0, b) }>.

Definition pda_shift : Term := <{ pda_d + pda_n }>.

Definition pda_test : CFormula := <{ pda_d < 1 }>.

Definition pda_prog (px py cx cy b : R) : Cmd :=
  <{ pda_d      := $(pda_sqdist px py cx cy);
     pda_n      sample $(pda_noise b);
     pda_d      := $(pda_shift);
     pda_inside b= $(pda_test) }>.

(** * The squared distance evaluates to [pda_D] in every state *)

Lemma pda_sqdist_value :
  forall (px py cx cy : R) (v : state),
    term_eval (pda_sqdist px py cx cy) v = pda_D px py cx cy.
Proof.
  intros px py cx cy v.
  unfold pda_sqdist, pda_delta, pda_minus_one, pda_D.
  cbn [term_eval]; ring.
Qed.

(** * The postcondition: the same syntactic CDF as PointInDiskInPlace.v *)

Definition pda_post (px py cx cy b : R) : PFormula :=
  [[ Pr[pda_inside] = E[$(pdi_cdf px py cx cy b)] ]].

(** * The weakest preconditions *)

Definition pda_after_add (px py cx cy b : R) : PFormula :=
  subst_bool_pformula pda_inside pda_test (pda_post px py cx cy b).

Definition pda_after_sample (px py cx cy b : R) : PFormula :=
  subst_real_pformula pda_d pda_shift (pda_after_add px py cx cy b).

Definition pda_after_assign (px py cx cy b : R) : PFormula :=
  sample_pformula pda_n (pda_noise b) (pda_after_sample px py cx cy b).

Definition pda_pre (px py cx cy b : R) : PFormula :=
  [[ E[ integral pda_n ~ $(pda_noise b),
        indicator[ $(pda_sqdist px py cx cy) + pda_n < 1 ] ]
     = E[ integral pda_n ~ $(pda_noise b), $(pdi_cdf px py cx cy b) ] ]].

Lemma pda_pre_is_wp :
  forall px py cx cy b : R,
    subst_real_pformula pda_d (pda_sqdist px py cx cy)
      (pda_after_assign px py cx cy b) = pda_pre px py cx cy b.
Proof. intros; vm_compute; reflexivity. Qed.

(** * Evaluating the two sides

    Centred noise lands on the CDF at [1 - D] about [0]; translation
    invariance ([disk_lap_atmost_shift]) moves it to [1] about [D]. *)

Lemma pda_pre_valid :
  forall px py cx cy b : R,
    0 < b ->
    pformula_valid [[ Pr[true] = 1 -> $(pda_pre px py cx cy b) ]].
Proof.
  intros px py cx cy b Hb ps Hadm.
  cbn [psatisfies]; intros _.
  unfold pda_pre; apply psatisfies_p_eq; cbn [pterm_eval].
  apply expectation_extensional; intro v.
  rewrite (disk_integral_const _ _ (pdi_cdf px py cx cy b) v
             (lap_atmost (pdi_D px py cx cy) b 1)).
  - unfold pda_noise.
    rewrite (disk_laplace_indicator pda_n _ 0 b _
               (fun r => r < 1 - pda_D px py cx cy)).
    + transitivity (lap_below 0 b (1 - pda_D px py cx cy)); [reflexivity |].
      rewrite <- (lap_atmost_below 0 b Hb).
      rewrite (disk_lap_atmost_shift (pdi_D px py cx cy) b 1 Hb).
      unfold pda_D, pdi_D; reflexivity.
    + exact Hb.
    + reflexivity.
    + intro r; unfold c_lt; cbn [satisfies c_not].
      change (term_eval (TAdd (pda_sqdist px py cx cy) (TProgVar pda_n))
                (update_real v pda_n r))
        with (term_eval (pda_sqdist px py cx cy) (update_real v pda_n r)
              + term_eval (TProgVar pda_n) (update_real v pda_n r)).
      rewrite update_real_same, pda_sqdist_value.
      cbn [term_eval]; split; intro H; lra.
  - cbn [distribution_valid term_eval pda_noise]; exact Hb.
  - intro w; apply pdi_cdf_value; exact Hb.
Qed.

Lemma pda_noise_valid_under :
  forall (b : R) (pre : PFormula),
    0 < b ->
    pformula_valid
      [[ $(pre) -> almost_sure[$(distribution_valid_formula (pda_noise b))] ]].
Proof.
  intros b pre Hb ps Hadm.
  cbn [psatisfies]; intros _.
  revert ps Hadm.
  apply p_almost_sure_of_pointwise.
  intro v.
  unfold pda_noise.
  cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
  intro Hle; lra.
Qed.

(** * The mechanism *)

Theorem pda_correct :
  forall px py cx cy b : R,
    0 < b ->
    {{ Pr[true] = 1 }}
      $(pda_prog px py cx cy b)
    {{ $(pda_post px py cx cy b) }}.
Proof.
  intros px py cx cy b Hb.
  unfold pda_prog.
  eapply HSeq with (eta2 := pda_after_assign px py cx cy b).
  - eapply HConseq with
      (eta1 := subst_real_pformula pda_d (pda_sqdist px py cx cy)
                 (pda_after_assign px py cx cy b))
      (eta2 := pda_after_assign px py cx cy b).
    + rewrite pda_pre_is_wp.
      apply pda_pre_valid; exact Hb.
    + apply HRealAssign.
    + intros ps _; cbn [psatisfies]; tauto.
  - eapply HSeq with (eta2 := pda_after_sample px py cx cy b).
    + apply HRealSample.
      * intros ps _; cbn [psatisfies]; intro H; exact H.
      * apply pda_noise_valid_under; exact Hb.
    + eapply HSeq with (eta2 := pda_after_add px py cx cy b).
      * apply HRealAssign.
      * apply HBoolAssign.
Qed.

(** * Cross-check against the in-place variant

    [pda_post] and [pdi_post] assert the same syntactic CDF for
    [Pr[inside]], so the two mechanisms are output-equivalent. *)
Lemma pda_agrees_with_in_place :
  forall px py cx cy b : R,
    pda_post px py cx cy b =
    [[ Pr[pda_inside] = E[$(pdi_cdf px py cx cy b)] ]]
    /\ pdi_post px py cx cy b =
    [[ Pr[pdi_inside] = E[$(pdi_cdf px py cx cy b)] ]].
Proof. intros; split; reflexivity. Qed.
