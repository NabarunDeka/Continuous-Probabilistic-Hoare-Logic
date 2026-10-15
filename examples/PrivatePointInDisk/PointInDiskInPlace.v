(**
  PointInDiskInPlace.v

  Program ([pdi_prog px py cx cy b]):
      d := (px - cx)^2 + (py - cy)^2;
      d <- sample(laplace(d, b));
      inside := (d < 1)
  Triple ([pdi_correct], for 0 < b; post [pdi_post], D := [pdi_sqdist px py cx cy]):
      { Pr[true] = 1 }
        pdi_prog px py cx cy b
      { Pr[inside] = E[ integral z ~ laplace(D, b), indicator[z <= 1] ] }
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
Require Import CPHL.
Require Import SampleBeforeLoop.
Require Import CdfAssertions.
Require Import DiskLaplaceFacts.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * The program

    The four coordinates are Rocq reals, so [pdi_sqdist] is a closed
    polynomial term in the parameters. *)

Definition pdi_d : RealProgramVar := real_program_var "pdi_d".
Definition pdi_z : RealProgramVar := real_program_var "pdi_z".
Definition pdi_inside : BoolProgramVar := bool_program_var "pdi_inside".

Definition pdi_minus_one : Term := TConst (-1).

Definition pdi_delta (u w : R) : Term := <{ $(u) + $(pdi_minus_one) * $(w) }>.

Definition pdi_sqdist (px py cx cy : R) : Term :=
  <{ ($(pdi_delta px cx) * $(pdi_delta px cx))
     + ($(pdi_delta py cy) * $(pdi_delta py cy)) }>.

(** The true squared distance, as a real (used only inside proofs). *)
Definition pdi_D (px py cx cy : R) : R :=
  ((px - cx) * (px - cx) + (py - cy) * (py - cy))%R.

Definition pdi_noise (b : R) : Distribution := <{ laplace(pdi_d, b) }>.

Definition pdi_test : CFormula := <{ pdi_d < 1 }>.

Definition pdi_prog (px py cx cy b : R) : Cmd :=
  <{ pdi_d      := $(pdi_sqdist px py cx cy);
     pdi_d      sample $(pdi_noise b);
     pdi_inside b= $(pdi_test) }>.

(** The Laplace law centred on the true squared distance. *)
Definition pdi_law (px py cx cy b : R) : Distribution :=
  Laplace (pdi_sqdist px py cx cy) (TConst b).

(** The syntactic CDF of that law at the radius [1]. *)
Definition pdi_cdf (px py cx cy b : R) : PConstruct :=
  [[ integral pdi_z ~ $(pdi_law px py cx cy b), indicator[pdi_z <= 1] ]].

Definition pdi_post (px py cx cy b : R) : PFormula :=
  [[ Pr[pdi_inside] = E[$(pdi_cdf px py cx cy b)] ]].

Lemma pdi_sqdist_value :
  forall (px py cx cy : R) (v : state),
    term_eval (pdi_sqdist px py cx cy) v = pdi_D px py cx cy.
Proof.
  intros px py cx cy v.
  unfold pdi_sqdist, pdi_delta, pdi_minus_one, pdi_D.
  cbn [term_eval]; ring.
Qed.

(** * The weakest preconditions *)

Definition pdi_after_sample (px py cx cy b : R) : PFormula :=
  subst_bool_pformula pdi_inside pdi_test (pdi_post px py cx cy b).

Definition pdi_after_assign (px py cx cy b : R) : PFormula :=
  sample_pformula pdi_d (pdi_noise b) (pdi_after_sample px py cx cy b).

Definition pdi_pre (px py cx cy b : R) : PFormula :=
  [[ E[ integral pdi_d ~ $(pdi_law px py cx cy b), indicator[ $(pdi_test) ] ]
     = E[ integral pdi_d ~ $(pdi_law px py cx cy b), $(pdi_cdf px py cx cy b) ] ]].

Lemma pdi_pre_is_wp :
  forall px py cx cy b : R,
    subst_real_pformula pdi_d (pdi_sqdist px py cx cy)
      (pdi_after_assign px py cx cy b) = pdi_pre px py cx cy b.
Proof. intros; vm_compute; reflexivity. Qed.

(** * Evaluating the two sides *)

Lemma pdi_cdf_value :
  forall (px py cx cy b : R) (v : state),
    0 < b ->
    q_eval (pdi_cdf px py cx cy b) v = lap_atmost (pdi_D px py cx cy) b 1.
Proof.
  intros px py cx cy b v Hb.
  unfold pdi_cdf, pdi_law.
  apply (disk_laplace_indicator pdi_z _ _ b _ (fun r => r <= 1)).
  - exact Hb.
  - apply pdi_sqdist_value.
  - intro r; cbn [satisfies]; rewrite update_real_same; reflexivity.
Qed.

Lemma pdi_pre_valid :
  forall px py cx cy b : R,
    0 < b ->
    pformula_valid [[ Pr[true] = 1 -> $(pdi_pre px py cx cy b) ]].
Proof.
  intros px py cx cy b Hb ps Hadm.
  cbn [psatisfies]; intros _.
  unfold pdi_pre; apply psatisfies_p_eq; cbn [pterm_eval].
  apply expectation_extensional; intro v.
  rewrite (disk_integral_const _ _ (pdi_cdf px py cx cy b) v (lap_atmost (pdi_D px py cx cy) b 1)).
  - unfold pdi_law.
    rewrite (disk_laplace_indicator pdi_d _ (pdi_D px py cx cy) b _ (fun r => r < 1)).
    + rewrite (lap_atmost_below _ b Hb); reflexivity.
    + exact Hb.
    + apply pdi_sqdist_value.
    + intro r; unfold pdi_test, c_lt; cbn [satisfies c_not].
      rewrite update_real_same; cbn [term_eval]; split; intro H; lra.
  - cbn [distribution_valid term_eval pdi_law]; exact Hb.
  - intro w; apply pdi_cdf_value; exact Hb.
Qed.

Lemma pdi_noise_valid_under :
  forall (b : R) (pre : PFormula),
    0 < b ->
    pformula_valid
      [[ $(pre) -> almost_sure[$(distribution_valid_formula (pdi_noise b))] ]].
Proof.
  intros b pre Hb ps Hadm.
  cbn [psatisfies]; intros _.
  revert ps Hadm.
  apply p_almost_sure_of_pointwise.
  intro v.
  unfold pdi_noise.
  cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
  intro Hle; lra.
Qed.

(** * The mechanism *)

Theorem pdi_correct :
  forall px py cx cy b : R,
    0 < b ->
    {{ Pr[true] = 1 }}
      $(pdi_prog px py cx cy b)
    {{ $(pdi_post px py cx cy b) }}.
Proof.
  intros px py cx cy b Hb.
  unfold pdi_prog.
  eapply HSeq with (eta2 := pdi_after_assign px py cx cy b).
  - eapply HConseq with
      (eta1 := subst_real_pformula pdi_d (pdi_sqdist px py cx cy)
                 (pdi_after_assign px py cx cy b))
      (eta2 := pdi_after_assign px py cx cy b).
    + rewrite pdi_pre_is_wp.
      apply pdi_pre_valid; exact Hb.
    + apply HRealAssign.
    + intros ps _; cbn [psatisfies]; tauto.
  - eapply HSeq with (eta2 := pdi_after_sample px py cx cy b).
    + apply HRealSample.
      * intros ps _; cbn [psatisfies]; intro H; exact H.
      * apply pdi_noise_valid_under; exact Hb.
    + apply HBoolAssign.
Qed.
