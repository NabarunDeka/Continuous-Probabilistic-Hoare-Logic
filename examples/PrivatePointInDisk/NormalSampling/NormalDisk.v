(**
  NormalDisk.v

  Program ([nd_prog px py cx cy b]):
      nd_n1 <- sample(gaussian(0, b));
      nd_n3 <- sample(gaussian(0, b));
      nd_n2 <- sample(gaussian(0, b));
      nd_n4 <- sample(gaussian(0, b));
      nd_inside := ( ((px+nd_n1) - (cx+nd_n3))^2 + ((py+nd_n2) - (cy+nd_n4))^2 < 1 )
  Triple ([nd_correct], for 0 < b and any precondition eta; post [nd_post]):
      { eta }
        nd_prog px py cx cy b
      { Pr[nd_inside] = E[ integral nd_z1 ~ gaussian(0, b), integral nd_z3 ~ gaussian(0, b),
                           integral nd_z2 ~ gaussian(0, b), integral nd_z4 ~ gaussian(0, b),
                           indicator[ ((px+nd_z1) - (cx+nd_z3))^2
                                      + ((py+nd_z2) - (cy+nd_z4))^2 < 1 ] ] }
  Unproved targets: [nd_reduction_target] (4-fold = 2-fold integral with
  deviation s, s * s = 2 * b * b), [nd_central_target] (centre case equals
  E[ integral nd_n1 ~ exponential(1/(4 b b)), indicator[nd_n1 < 1] ]).
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
Require Import CPHL.
Require Import CPHLFacts.DistributionFacts CPHLFacts.CalculationFacts.
Require Import SampleBeforeLoop.
Require Import HalfLaplaceRejection.
Require Import GaussianDifference.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * Cutting two noises down to one (analytic layer only)

    The difference of the two normals acting on a coordinate is itself
    normal, with deviation [s] where [s * s = 2 * b * b] (that is,
    [s = b * sqrt 2]).  The deviation is a parameter so that no square root
    appears inside a distribution term. *)

Theorem nd_combined_noise :
  forall b s z : R,
    (0 < b)%R -> (0 < s)%R -> (s * s = 2 * b * b)%R ->
    real_integral (fun u => gc_density 0 b u * gc_density 0 b (u - z)) =
    gc_density 0 s z.
Proof.
  intros b s z Hb Hs Hss.
  rewrite (gc_difference 0 b 0 b s z Hb Hb Hs) by lra.
  f_equal; ring.
Qed.

(** The combined noise is itself a CPHL distribution. *)
Definition nd_combined (s : R) : Distribution := <{ gaussian(0, s) }>.

Lemma nd_combined_density :
  forall (s z : R) (v : state),
    distribution_density (nd_combined s) v z = gc_density 0 s z.
Proof. intros; reflexivity. Qed.

(** * The program *)

Definition nd_n1 : RealProgramVar := real_program_var "nd_n1".
Definition nd_n3 : RealProgramVar := real_program_var "nd_n3".
Definition nd_n2 : RealProgramVar := real_program_var "nd_n2".
Definition nd_n4 : RealProgramVar := real_program_var "nd_n4".
Definition nd_inside : BoolProgramVar := bool_program_var "nd_inside".

Definition nd_minus_one : Term := TConst (-1).

Definition nd_noise (b : R) : Distribution := <{ gaussian(0, b) }>.

Definition nd_z1 : RealProgramVar := real_program_var "nd_z1".
Definition nd_z3 : RealProgramVar := real_program_var "nd_z3".
Definition nd_z2 : RealProgramVar := real_program_var "nd_z2".
Definition nd_z4 : RealProgramVar := real_program_var "nd_z4".

(** The disk test over four noise variables [a1 a3 a2 a4]. *)
Definition nd_disk_at (a1 a3 a2 a4 : RealProgramVar) (px py cx cy : R) : CFormula :=
  <{ ((($(px) + a1) + $(nd_minus_one) * ($(cx) + a3))
      * (($(px) + a1) + $(nd_minus_one) * ($(cx) + a3)))
     + ((($(py) + a2) + $(nd_minus_one) * ($(cy) + a4))
        * (($(py) + a2) + $(nd_minus_one) * ($(cy) + a4))) < 1 }>.

Definition nd_disk (px py cx cy : R) : CFormula :=
  nd_disk_at nd_n1 nd_n3 nd_n2 nd_n4 px py cx cy.

Definition nd_prog (px py cx cy b : R) : Cmd :=
  <{ nd_n1 sample $(nd_noise b);
     nd_n3 sample $(nd_noise b);
     nd_n2 sample $(nd_noise b);
     nd_n4 sample $(nd_noise b);
     nd_inside b= $(nd_disk px py cx cy) }>.

(** The four-fold integral of the disk event, with bound variables
    [a1 a3 a2 a4]. *)
Definition nd_construct_at (a1 a3 a2 a4 : RealProgramVar) (px py cx cy b : R)
  : PConstruct :=
  [[ integral a1 ~ $(nd_noise b),
     integral a3 ~ $(nd_noise b),
     integral a2 ~ $(nd_noise b),
     integral a4 ~ $(nd_noise b),
     indicator[ $(nd_disk_at a1 a3 a2 a4 px py cx cy) ] ]].

(** The probability of the disk event, as used in the postcondition. *)
Definition nd_construct (px py cx cy b : R) : PConstruct :=
  nd_construct_at nd_z1 nd_z3 nd_z2 nd_z4 px py cx cy b.

(** The two-fold one, after the combination [nd_combined_noise] licenses
    (with combined deviation [s], [s * s = 2 * b * b]). *)
Definition nd_two_construct (px py cx cy s : R) : PConstruct :=
  [[ integral nd_n1 ~ $(nd_combined s),
     integral nd_n2 ~ $(nd_combined s),
     indicator[ (($(px) + $(nd_minus_one) * $(cx)) + nd_n1)
                * (($(px) + $(nd_minus_one) * $(cx)) + nd_n1)
                + (($(py) + $(nd_minus_one) * $(cy)) + nd_n2)
                  * (($(py) + $(nd_minus_one) * $(cy)) + nd_n2) < 1 ] ]].

(** * Weakest precondition *)

Definition nd_post (px py cx cy b : R) : PFormula :=
  [[ Pr[nd_inside] = E[ $(nd_construct px py cx cy b) ] ]].

Definition nd_s3 (px py cx cy b : R) : PFormula :=
  subst_bool_pformula nd_inside (nd_disk px py cx cy) (nd_post px py cx cy b).
Definition nd_s2 (px py cx cy b : R) : PFormula :=
  sample_pformula nd_n4 (nd_noise b) (nd_s3 px py cx cy b).
Definition nd_s1 (px py cx cy b : R) : PFormula :=
  sample_pformula nd_n2 (nd_noise b) (nd_s2 px py cx cy b).
Definition nd_s0 (px py cx cy b : R) : PFormula :=
  sample_pformula nd_n3 (nd_noise b) (nd_s1 px py cx cy b).
Definition nd_pre (px py cx cy b : R) : PFormula :=
  sample_pformula nd_n1 (nd_noise b) (nd_s0 px py cx cy b).

Definition nd_wrap (b : R) (q : PConstruct) : PConstruct :=
  [[ integral nd_n1 ~ $(nd_noise b),
     integral nd_n3 ~ $(nd_noise b),
     integral nd_n2 ~ $(nd_noise b),
     integral nd_n4 ~ $(nd_noise b), $(q) ]].

Lemma nd_pre_shape :
  forall px py cx cy b : R,
    nd_pre px py cx cy b =
    [[ E[ $(nd_construct_at nd_n1 nd_n3 nd_n2 nd_n4 px py cx cy b) ]
       = E[ $(nd_wrap b (nd_construct px py cx cy b)) ] ]].
Proof. intros; reflexivity. Qed.

(** * Analysis *)

Lemma nd_noise_valid :
  forall (b : R) (v : state), 0 < b -> distribution_valid (nd_noise b) v.
Proof. intros b v Hb; exact Hb. Qed.

(** Integrating a state-independent body against a valid law returns it. *)
Lemma nd_integral_const :
  forall (x : RealProgramVar) (d : Distribution) (q : PConstruct) (v : state) (c : R),
    distribution_valid d v ->
    (forall w : state, q_eval q w = c) ->
    q_eval (QIntegral x d q) v = c.
Proof.
  intros x d q v c Hd Hc.
  rewrite (q_integral_density x d q v Hd).
  rewrite (real_integral_extensional _ (fun z => c * distribution_density d v z))
    by (intro z; rewrite Hc; apply Rmult_comm).
  rewrite real_integral_scale by exact (distribution_density_integrable Hd).
  rewrite (real_integral_distribution_density Hd).
  change (c * 1 = c); ring.
Qed.

(** The four-fold integral rebinds every variable its indicator reads. *)
Lemma nd_construct_state_free :
  forall (px py cx cy b : R) (v w : state),
    0 < b ->
    q_eval (nd_construct_at nd_n1 nd_n3 nd_n2 nd_n4 px py cx cy b) v =
    q_eval (nd_construct px py cx cy b) w.
Proof.
  intros px py cx cy b v w Hb.
  assert (Hall : forall u, distribution_valid (nd_noise b) u)
    by (intro u; exact Hb).
  unfold nd_construct, nd_construct_at.
  rewrite !(q_eval_integral_density _ _ _ Hall).
  (* Variable lookups compute: both sides are convertible pointwise. *)
  apply real_integral_extensional; intro a; f_equal.
Qed.

Lemma nd_pre_valid :
  forall px py cx cy b : R,
    0 < b -> pformula_valid (nd_pre px py cx cy b).
Proof.
  intros px py cx cy b Hb ps Hadm.
  rewrite nd_pre_shape.
  apply psatisfies_p_eq.
  cbn [pterm_eval].
  apply expectation_extensional; intro v.
  symmetry.
  unfold nd_wrap.
  set (c := q_eval (nd_construct_at nd_n1 nd_n3 nd_n2 nd_n4 px py cx cy b) v).
  assert (Hc : forall w, q_eval (nd_construct px py cx cy b) w = c)
    by (intro w; unfold c; symmetry; apply nd_construct_state_free; exact Hb).
  apply nd_integral_const; [apply nd_noise_valid; exact Hb | intro w1].
  apply nd_integral_const; [apply nd_noise_valid; exact Hb | intro w2].
  apply nd_integral_const; [apply nd_noise_valid; exact Hb | intro w3].
  apply nd_integral_const; [apply nd_noise_valid; exact Hb | exact Hc].
Qed.

(** * The mechanism *)

Lemma nd_noise_valid_under :
  forall (b : R) (pre : PFormula),
    (0 < b)%R ->
    pformula_valid
      [[ $(pre) -> almost_sure[$(distribution_valid_formula (nd_noise b))] ]].
Proof.
  intros b pre Hb ps Hadm.
  cbn [psatisfies]; intros _.
  refine (p_almost_sure_of_pointwise _ _ ps Hadm).
  intro v.
  unfold nd_noise.
  cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
  intro Hle; lra.
Qed.

Theorem nd_correct :
  forall (px py cx cy b : R) (eta : PFormula),
    (0 < b)%R ->
    {{ $(eta) }}
      $(nd_prog px py cx cy b)
    {{ Pr[nd_inside] = E[ $(nd_construct px py cx cy b) ] }}.
Proof.
  intros px py cx cy b eta Hb.
  unfold nd_prog.
  eapply HSeq with (eta2 := nd_s0 px py cx cy b).
  - apply HRealSample.
    + intros ps Hadm _.
      apply nd_pre_valid; assumption.
    + apply nd_noise_valid_under; exact Hb.
  - eapply HSeq with (eta2 := nd_s1 px py cx cy b).
    + apply HRealSample.
      * intros ps Hadm; cbn [psatisfies]; intro H; exact H.
      * apply nd_noise_valid_under; exact Hb.
    + eapply HSeq with (eta2 := nd_s2 px py cx cy b).
      * apply HRealSample.
        -- intros ps Hadm; cbn [psatisfies]; intro H; exact H.
        -- apply nd_noise_valid_under; exact Hb.
      * eapply HSeq with (eta2 := nd_s3 px py cx cy b).
        -- apply HRealSample.
           ++ intros ps Hadm; cbn [psatisfies]; intro H; exact H.
           ++ apply nd_noise_valid_under; exact Hb.
        -- apply HBoolAssign.
Qed.

(** * Statements that remain open (unproved targets) *)

(** 4 -> 2: the four-fold integral equals the two-fold one with combined
    deviation [s] ([s * s = 2 * b * b]).  Needs Fubini and a translation
    change of variables for the nested kernel integrals. *)
Definition nd_reduction_target (px py cx cy b s : R) : Prop :=
  (s * s = 2 * b * b)%R ->
  forall v : state,
    q_eval (nd_construct px py cx cy b) v =
    q_eval (nd_two_construct px py cx cy s) v.

(** The central case: [Pr[inside] = 1 - exp(-1/(4 b^2))], written as the
    probability that an [exponential(1/(4 b b))] sample lies below [1].
    Needs polar coordinates in two dimensions. *)
Definition nd_central_target (p b : R) : Prop :=
  forall v : state,
    q_eval (nd_construct p p p p b) v =
    q_eval [[ integral nd_n1 ~ exponential($(1 / (4 * b * b))), indicator[ nd_n1 < 1 ] ]] v.
