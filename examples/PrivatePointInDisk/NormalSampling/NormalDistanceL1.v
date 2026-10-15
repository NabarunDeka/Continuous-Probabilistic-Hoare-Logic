(**
  NormalDistanceL1.v

  Program ([nl_prog px py cx cy b]):
      nl_n <- sample(gaussian(0, b));
      nl_ax := px - cx;  if nl_ax < 0 then nl_ax := -1 * nl_ax else skip end;
      nl_ay := py - cy;  if nl_ay < 0 then nl_ay := -1 * nl_ay else skip end;
      nl_inside := (nl_ax + nl_ay + nl_n < 1)
  Triple ([nl_correct], for 0 < b, 0 <= Lx, Lx * Lx = (px-cx)^2, 0 <= Ly,
          Ly * Ly = (py-cy)^2, any precondition eta; post [nl_post]):
      { eta }
        nl_prog px py cx cy b
      { Pr[nl_inside] = E[ integral nl_z ~ gaussian(0, b),
                            indicator[nl_z < 1 - (Lx + Ly)] ] }
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import Classical.
Require Import CPHL.
Require Import CPHLFacts.DistributionFacts CPHLFacts.CalculationFacts.
Require Import SampleBeforeLoop.
Require Import HalfLaplaceRejection.
Require Import SVT.
Require Import CdfAssertions.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

Local Ltac mathcomp_tauto :=
  first [solve [intuition fail] |
    apply (proj1 (boolp.not_notP _)); solve [intuition fail] ].

(** * The absolute-value gadget *)

Definition nl_minus_one : Term := TConst (-1).

Definition nl_neg (x : RealProgramVar) : CFormula := <{ x < 0 }>.
Definition nl_flip (x : RealProgramVar) : Term := <{ $(nl_minus_one) * x }>.

Definition nl_abs (x : RealProgramVar) : Cmd :=
  <{ if $(nl_neg x) then x := $(nl_flip x) else skip end }>.

Definition nl_block (x : RealProgramVar) (c : R) : Cmd :=
  <{ x := $(TConst c); $(nl_abs x) }>.

(** The probability logic variable carrying the tracked value, and an
    auxiliary one for the branch that receives no mass. *)
Definition nl_y : ProbLogicVar := prob_logic_var "nl_y".
Definition nl_y0 : ProbLogicVar := prob_logic_var "nl_y0".

Definition nl_eq (y : ProbLogicVar) (q : PConstruct) : PFormula :=
  p_eq (PVar y) (PExpect q).

Definition nl_zero : PFormula := p_eq (PVar nl_y0) (PConst 0).

Lemma nl_zero_analytical : pformula_analytical nl_zero.
Proof.
  exact (svt_rigid_constant_analytical nl_y0 0).
Qed.

Lemma nl_y0_not_y : ~ prob_logic_var_occurs_pformula nl_y0 (nl_eq nl_y (QIndicator c_true)).
Proof.
  cbn [nl_eq p_eq p_and p_not prob_logic_var_occurs_pformula
       prob_logic_var_occurs_pterm].
  unfold nl_y0, nl_y; intuition congruence.
Qed.

Lemma nl_y0_not_in_eq :
  forall q : PConstruct, ~ prob_logic_var_occurs_pformula nl_y0 (nl_eq nl_y q).
Proof.
  intro q.
  cbn [nl_eq p_eq p_and p_not prob_logic_var_occurs_pformula
       prob_logic_var_occurs_pterm].
  unfold nl_y0, nl_y; intuition congruence.
Qed.

(** Taking off the auxiliary variable once the branch sum is known. *)
Lemma nl_drop_aux :
  forall (eta : PFormula) (s : Cmd) (q : PConstruct) (sum : Pterm),
    (forall ps, pterm_eval sum ps = pterm_eval (PAdd (PVar nl_y) (PVar nl_y0)) ps) ->
    {{ $(eta) }} $(s) {{ $(p_eq sum (PExpect q)) }} ->
    {{ $(subst_prob_pformula nl_y0 (PConst 0) eta) }} $(s) {{ $(nl_eq nl_y q) }}.
Proof.
  intros eta s q sum Hsum H.
  eapply HElimv with (eta1 := eta) (y := nl_y0) (p := PConst 0).
  - eapply HConseq with
      (eta1 := p_and eta nl_zero)
      (eta2 := p_and (p_eq sum (PExpect q)) nl_zero).
    + intros ps Hadm; cbn [psatisfies]; mathcomp_tauto.
    + apply HAnd.
      * eapply HConseq with (eta1 := eta) (eta2 := p_eq sum (PExpect q)).
        -- intros ps Hadm; cbn [psatisfies]; intro Hp.
           apply psatisfies_p_and in Hp; exact (proj1 Hp).
        -- exact H.
        -- intros ps Hadm; cbn [psatisfies]; tauto.
      * eapply HConseq with (eta1 := nl_zero) (eta2 := nl_zero).
        -- intros ps Hadm; cbn [psatisfies]; intro Hp.
           apply psatisfies_p_and in Hp; exact (proj2 Hp).
        -- apply HFree; exact nl_zero_analytical.
        -- intros ps Hadm; cbn [psatisfies]; tauto.
    + intros ps Hadm; cbn [psatisfies]; intro Hp.
      apply psatisfies_p_and in Hp; destruct Hp as [Hs Hz].
      unfold nl_zero in Hz; unfold nl_eq.
      apply psatisfies_p_eq in Hs; apply psatisfies_p_eq in Hz.
      apply psatisfies_p_eq.
      rewrite Hsum in Hs.
      cbn [pterm_eval] in Hs, Hz |- *.
      lra.
  - cbn [prob_logic_var_occurs_pterm]; tauto.
  - apply nl_y0_not_in_eq.
Qed.

(** All mass on the THEN branch: the ELSE branch's value is the auxiliary
    variable, eliminated to [0]. *)
Lemma nl_gadget_then :
  forall (x : RealProgramVar) (c : R) (q : PConstruct) (eta : PFormula),
    pformula_valid
      (PFImpl eta
        (subst_real_pformula x (TConst c)
          (subst_prob_pformula nl_y0 (PConst 0)
            (if_precondition
              (subst_real_pformula x (nl_flip x) (nl_eq nl_y q))
              (nl_eq nl_y0 q) (nl_neg x))))) ->
    {{ $(eta) }} $(nl_block x c) {{ $(nl_eq nl_y q) }}.
Proof.
  intros x c q eta Hpre.
  unfold nl_block.
  eapply HSeq with
    (eta2 := subst_prob_pformula nl_y0 (PConst 0)
               (if_precondition
                 (subst_real_pformula x (nl_flip x) (nl_eq nl_y q))
                 (nl_eq nl_y0 q) (nl_neg x))).
  - eapply HConseq; [exact Hpre | apply HRealAssign |].
    intros ps Hadm; cbn [psatisfies]; tauto.
  - apply (nl_drop_aux _ _ q (PAdd (PVar nl_y) (PVar nl_y0))).
    + intro ps; reflexivity.
    + unfold nl_abs; apply HIfEq.
      * apply HRealAssign.
      * apply HSkip.
Qed.

(** All mass on the ELSE branch. *)
Lemma nl_gadget_else :
  forall (x : RealProgramVar) (c : R) (q : PConstruct) (eta : PFormula),
    pformula_valid
      (PFImpl eta
        (subst_real_pformula x (TConst c)
          (subst_prob_pformula nl_y0 (PConst 0)
            (if_precondition
              (subst_real_pformula x (nl_flip x) (nl_eq nl_y0 q))
              (nl_eq nl_y q) (nl_neg x))))) ->
    {{ $(eta) }} $(nl_block x c) {{ $(nl_eq nl_y q) }}.
Proof.
  intros x c q eta Hpre.
  unfold nl_block.
  eapply HSeq with
    (eta2 := subst_prob_pformula nl_y0 (PConst 0)
               (if_precondition
                 (subst_real_pformula x (nl_flip x) (nl_eq nl_y0 q))
                 (nl_eq nl_y q) (nl_neg x))).
  - eapply HConseq; [exact Hpre | apply HRealAssign |].
    intros ps Hadm; cbn [psatisfies]; tauto.
  - apply (nl_drop_aux _ _ q (PAdd (PVar nl_y0) (PVar nl_y))).
    + intro ps; cbn [pterm_eval]; ring.
    + unfold nl_abs; apply HIfEq.
      * apply HRealAssign.
      * apply HSkip.
Qed.

(** * Formula-level helpers *)

Lemma nl_expect_iff :
  forall (mu : Measure) (g1 g2 : CFormula),
    (forall v : state, satisfies v g1 <-> satisfies v g2) ->
    expectation mu (q_eval (QIndicator g1)) =
    expectation mu (q_eval (QIndicator g2)).
Proof.
  intros mu g1 g2 H.
  apply expectation_extensional; intro v.
  rewrite !q_eval_indicatorE; apply real_indicator_extensional, H.
Qed.

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

(** Structural commutations, by computation. *)

Lemma nl_push_real_and : forall x t a b,
  subst_real_pformula x t (p_and a b) =
  p_and (subst_real_pformula x t a) (subst_real_pformula x t b).
Proof. reflexivity. Qed.
Lemma nl_push_real_eq : forall x t p1 p2,
  subst_real_pformula x t (p_eq p1 p2) =
  p_eq (subst_real_pterm x t p1) (subst_real_pterm x t p2).
Proof. reflexivity. Qed.
Lemma nl_push_prob_and : forall y p a b,
  subst_prob_pformula y p (p_and a b) =
  p_and (subst_prob_pformula y p a) (subst_prob_pformula y p b).
Proof. reflexivity. Qed.
Lemma nl_push_prob_eq : forall y p p1 p2,
  subst_prob_pformula y p (p_eq p1 p2) =
  p_eq (subst_prob_pterm y p p1) (subst_prob_pterm y p p2).
Proof. reflexivity. Qed.
Lemma nl_push_cond_eq : forall g p1 p2,
  condition_pformula (p_eq p1 p2) g =
  p_eq (condition_pterm p1 g) (condition_pterm p2 g).
Proof. reflexivity. Qed.

Lemma nl_y_ne_y0 : forall (A : Type) (a b : A),
  (if prob_logic_var_eq_dec nl_y nl_y0 then a else b) = b.
Proof.
  intros A a b; destruct (prob_logic_var_eq_dec nl_y nl_y0) as [H | H];
    [unfold nl_y, nl_y0 in H; inversion H | reflexivity].
Qed.

Lemma nl_y0_eq_y0 : forall (A : Type) (a b : A),
  (if prob_logic_var_eq_dec nl_y0 nl_y0 then a else b) = a.
Proof.
  intros A a b; destruct (prob_logic_var_eq_dec nl_y0 nl_y0) as [H | H];
    [reflexivity | contradiction].
Qed.

Ltac nl_unfold_pre :=
  unfold if_precondition, nl_eq;
  rewrite ?nl_push_cond_eq, ?nl_push_prob_and, ?nl_push_prob_eq,
    ?nl_push_real_and, ?nl_push_real_eq, ?nl_push_real_eq;
  apply psatisfies_p_and; split; apply psatisfies_p_eq;
  cbn [subst_prob_pterm condition_pterm subst_real_pterm];
  rewrite ?nl_y_ne_y0, ?nl_y0_eq_y0;
  cbn [subst_real_pterm pterm_eval
       subst_real_pconstruct subst_real_pconstruct_fuel
       condition_pconstruct condition_pconstruct_fuel pconstruct_size].

(** * The gadget on indicator probabilities *)

Lemma nl_ind_block_neg :
  forall (x : RealProgramVar) (c : R) (gamma : CFormula),
    (c < 0)%R ->
    {{ $(nl_eq nl_y (QIndicator (subst_real_cformula x (nl_flip_const c) gamma))) }}
      $(nl_block x c)
    {{ $(nl_eq nl_y (QIndicator gamma)) }}.
Proof.
  intros x c gamma Hc.
  apply nl_gadget_then.
  intros ps Hadm; cbn [psatisfies]; intro Hpre.
  unfold nl_eq in Hpre; apply psatisfies_p_eq in Hpre; cbn [pterm_eval] in Hpre.
  nl_unfold_pre.
  - rewrite Hpre.
    apply nl_expect_iff; intro v.
    rewrite nl_subst_and, nl_subst_neg, nl_subst_cformula_flip, nl_sat_and.
    split.
    + intro H; split; [exact H | apply nl_sat_lt; exact Hc].
    + intros [H _]; exact H.
  - symmetry; apply expect_indicator_unsat; intro v.
    rewrite nl_subst_and, nl_subst_not, nl_subst_neg, nl_sat_and.
    intros [_ H]; apply H, nl_sat_lt; exact Hc.
Qed.

Lemma nl_ind_block_pos :
  forall (x : RealProgramVar) (c : R) (gamma : CFormula),
    (0 <= c)%R ->
    {{ $(nl_eq nl_y (QIndicator (subst_real_cformula x (TConst c) gamma))) }}
      $(nl_block x c)
    {{ $(nl_eq nl_y (QIndicator gamma)) }}.
Proof.
  intros x c gamma Hc.
  apply nl_gadget_else.
  intros ps Hadm; cbn [psatisfies]; intro Hpre.
  unfold nl_eq in Hpre; apply psatisfies_p_eq in Hpre; cbn [pterm_eval] in Hpre.
  nl_unfold_pre.
  - symmetry; apply expect_indicator_unsat; intro v.
    rewrite nl_subst_and, nl_subst_neg, nl_sat_and.
    intros [_ H]; apply nl_sat_lt in H; lra.
  - rewrite Hpre.
    apply nl_expect_iff; intro v.
    rewrite nl_subst_and, nl_subst_not, nl_subst_neg, nl_sat_and.
    split.
    + intro H; split; [exact H |].
      intro Hk; apply nl_sat_lt in Hk; lra.
    + intros [H _]; exact H.
Qed.

(** * The program *)

Definition nl_ax : RealProgramVar := real_program_var "nl_ax".
Definition nl_ay : RealProgramVar := real_program_var "nl_ay".
Definition nl_n  : RealProgramVar := real_program_var "nl_n".
Definition nl_z  : RealProgramVar := real_program_var "nl_z".
Definition nl_inside : BoolProgramVar := bool_program_var "nl_inside".

Definition nl_noise (b : R) : Distribution := <{ gaussian(0, b) }>.

Definition nl_test : CFormula := <{ ((nl_ax + nl_ay) + nl_n) < 1 }>.

Definition nl_prog (px py cx cy b : R) : Cmd :=
  <{ nl_n sample $(nl_noise b);
     $(nl_block nl_ax (px - cx));
     $(nl_block nl_ay (py - cy));
     nl_inside b= $(nl_test) }>.

(** The centred normal CDF at [cut], as a construct. *)
Definition nl_cdf (b cut : R) : PConstruct :=
  [[ integral nl_z ~ $(nl_noise b), indicator[ nl_z < $(cut) ] ]].

Definition nl_post (b cut : R) : PFormula :=
  [[ Pr[nl_inside] = E[ $(nl_cdf b cut) ] ]].

(** * The gadget leaves the closed CDF construct unchanged *)

Definition nl_cdf_and (b cut : R) (g : CFormula) : PConstruct :=
  [[ integral nl_z ~ $(nl_noise b), indicator[ (nl_z < $(cut)) /\ $(g) ] ]].

Lemma nl_cdf_then_form :
  forall (x : RealProgramVar) (b cut c : R),
    x = nl_ax \/ x = nl_ay ->
    subst_real_pconstruct x (TConst c)
      (condition_pconstruct (subst_real_pconstruct x (nl_flip x) (nl_cdf b cut))
         (nl_neg x)) =
    nl_cdf_and b cut <{ $(c) < 0 }>.
Proof.
  intros x b cut c [-> | ->];
    unfold nl_cdf, nl_cdf_and, nl_neg, nl_flip, nl_noise, nl_minus_one,
      nl_ax, nl_ay, nl_z;
    cbn; reflexivity.
Qed.

Lemma nl_cdf_else_form :
  forall (x : RealProgramVar) (b cut c : R),
    x = nl_ax \/ x = nl_ay ->
    subst_real_pconstruct x (TConst c)
      (condition_pconstruct (nl_cdf b cut) (c_not (nl_neg x))) =
    nl_cdf_and b cut <{ ~ ($(c) < 0) }>.
Proof.
  intros x b cut c [-> | ->];
    unfold nl_cdf, nl_cdf_and, nl_neg, nl_flip, nl_noise, nl_minus_one,
      nl_ax, nl_ay, nl_z;
    cbn; reflexivity.
Qed.

Lemma nl_cdf_and_value :
  forall (b cut : R) (g : CFormula) (P : Prop) (v : state),
    0 < b ->
    (forall w, satisfies w g <-> P) ->
    q_eval (nl_cdf_and b cut g) v =
    q_eval (nl_cdf b cut) v * real_indicator P.
Proof.
  intros b cut g P v Hb Hg.
  unfold nl_cdf_and, nl_cdf.
  rewrite !q_integral_density by exact Hb.
  destruct (classic P) as [HP | HP].
  - rewrite (real_indicator_true P HP), Rmult_1_r.
    apply real_integral_extensional; intro z.
    f_equal.
    rewrite !q_eval_indicatorE.
    apply real_indicator_extensional.
    rewrite nl_sat_and.
    split.
    + intros [H _]; exact H.
    + intro H; split; [exact H | apply Hg; exact HP].
  - rewrite (real_indicator_false P HP), Rmult_0_r.
    rewrite <- real_integral_zero.
    apply real_integral_extensional; intro z.
    rewrite q_eval_indicatorE.
    rewrite real_indicator_false; [ring |].
    rewrite nl_sat_and.
    intros [_ H]; apply HP, (proj1 (Hg _) H).
Qed.


Lemma nl_sat_not_lt :
  forall (v : state) (c : R), satisfies v <{ ~ ($(c) < 0) }> <-> ~ (c < 0)%R.
Proof.
  intros v c.
  change (satisfies v (c_not <{ $(c) < 0 }>)) with (~ satisfies v <{ $(c) < 0 }>).
  rewrite nl_sat_lt; tauto.
Qed.

Ltac nl_unfold_pre_light :=
  unfold if_precondition, nl_eq;
  rewrite ?nl_push_cond_eq, ?nl_push_prob_and, ?nl_push_prob_eq,
    ?nl_push_real_and, ?nl_push_real_eq, ?nl_push_real_eq;
  apply psatisfies_p_and; split; apply psatisfies_p_eq;
  cbn [subst_prob_pterm condition_pterm subst_real_pterm];
  rewrite ?nl_y_ne_y0, ?nl_y0_eq_y0;
  cbn [subst_real_pterm pterm_eval].

Lemma nl_cdf_block :
  forall (x : RealProgramVar) (c b cut : R),
    x = nl_ax \/ x = nl_ay ->
    0 < b ->
    {{ $(nl_eq nl_y (nl_cdf b cut)) }}
      $(nl_block x c)
    {{ $(nl_eq nl_y (nl_cdf b cut)) }}.
Proof.
  intros x c b cut Hx Hb.
  destruct (Rlt_dec c 0) as [Hc | Hc].
  - apply nl_gadget_then.
    intros ps Hadm; cbn [psatisfies]; intro Hpre.
    unfold nl_eq in Hpre; apply psatisfies_p_eq in Hpre; cbn [pterm_eval] in Hpre.
    nl_unfold_pre_light.
    + rewrite (nl_cdf_then_form x b cut c Hx), Hpre.
      apply expectation_extensional; intro v.
      rewrite (nl_cdf_and_value b cut _ (c < 0) v Hb (fun w => nl_sat_lt w c)).
      rewrite (real_indicator_true _ Hc); ring.
    + rewrite (nl_cdf_else_form x b cut c Hx).
      rewrite (expect_const_construct _ _ 0); [ring |].
      intro v.
      rewrite (nl_cdf_and_value b cut _ (~ c < 0) v Hb (fun w => nl_sat_not_lt w c)).
      rewrite real_indicator_false; [ring | tauto].
  - apply nl_gadget_else.
    intros ps Hadm; cbn [psatisfies]; intro Hpre.
    unfold nl_eq in Hpre; apply psatisfies_p_eq in Hpre; cbn [pterm_eval] in Hpre.
    nl_unfold_pre_light.
    + rewrite (nl_cdf_then_form x b cut c Hx).
      rewrite (expect_const_construct _ _ 0); [ring |].
      intro v.
      rewrite (nl_cdf_and_value b cut _ (c < 0) v Hb (fun w => nl_sat_lt w c)).
      rewrite real_indicator_false; [ring | exact Hc].
    + rewrite (nl_cdf_else_form x b cut c Hx), Hpre.
      apply expectation_extensional; intro v.
      rewrite (nl_cdf_and_value b cut _ (~ c < 0) v Hb (fun w => nl_sat_not_lt w c)).
      rewrite (real_indicator_true _ Hc); ring.
Qed.

(** * The whole program, for any tracked construct *)

Lemma nl_noise_valid_under :
  forall (b : R) (pre : PFormula),
    (0 < b)%R ->
    pformula_valid
      [[ $(pre) -> almost_sure[$(distribution_valid_formula (nl_noise b))] ]].
Proof.
  intros b pre Hb ps Hadm.
  cbn [psatisfies]; intros _.
  refine (p_almost_sure_of_pointwise _ _ ps Hadm).
  intro v.
  unfold nl_noise.
  cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
  intro Hle; lra.
Qed.

Lemma nl_chain :
  forall (px py cx cy b : R) (q0 q1 q2 q3 : PConstruct),
    (0 < b)%R ->
    {{ $(nl_eq nl_y q3) }} $(nl_block nl_ax (px - cx)) {{ $(nl_eq nl_y q2) }} ->
    {{ $(nl_eq nl_y q2) }} $(nl_block nl_ay (py - cy)) {{ $(nl_eq nl_y q1) }} ->
    {{ $(nl_eq nl_y q1) }} nl_inside b= $(nl_test) {{ $(nl_eq nl_y q0) }} ->
    {{ $(nl_eq nl_y (QIntegral nl_n (nl_noise b) q3)) }}
      $(nl_prog px py cx cy b)
    {{ $(nl_eq nl_y q0) }}.
Proof.
  intros px py cx cy b q0 q1 q2 q3 Hb Hax Hay Hbool.
  unfold nl_prog.
  eapply HSeq with (eta2 := nl_eq nl_y q3).
  - apply HRealSample.
    + intros ps Hadm; cbn [psatisfies]; intro H; exact H.
    + apply nl_noise_valid_under; exact Hb.
  - eapply HSeq with (eta2 := nl_eq nl_y q2); [exact Hax |].
    eapply HSeq with (eta2 := nl_eq nl_y q1); [exact Hay | exact Hbool].
Qed.

(** The indicator chain. *)
Lemma nl_bool_ind :
  {{ $(nl_eq nl_y (QIndicator nl_test)) }} nl_inside b= $(nl_test)
  {{ $(nl_eq nl_y (QIndicator (FProgBool nl_inside))) }}.
Proof.
  assert (E : subst_bool_pformula nl_inside nl_test
                (nl_eq nl_y (QIndicator (FProgBool nl_inside))) =
              nl_eq nl_y (QIndicator nl_test))
    by (unfold nl_eq, nl_test, nl_inside; cbn; reflexivity).
  rewrite <- E; apply HBoolAssign.
Qed.

(** The CDF chain. *)
Lemma nl_bool_cdf :
  forall b cut : R,
    {{ $(nl_eq nl_y (nl_cdf b cut)) }} nl_inside b= $(nl_test)
    {{ $(nl_eq nl_y (nl_cdf b cut)) }}.
Proof.
  intros b cut.
  assert (E : subst_bool_pformula nl_inside nl_test (nl_eq nl_y (nl_cdf b cut)) =
              nl_eq nl_y (nl_cdf b cut))
    by (unfold nl_eq, nl_cdf, nl_noise, nl_z, nl_inside; cbn; reflexivity).
  rewrite <- E at 1; apply HBoolAssign.
Qed.

Definition nl_test_at (tx ty : Term) : CFormula :=
  <{ (($(tx) + $(ty)) + nl_n) < 1 }>.

(** * Analysis of the eliminated precondition *)

Lemma nl_integral_const :
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

Lemma nl_cdf_value :
  forall (b cut : R) (v : state),
    0 < b ->
    q_eval (nl_cdf b cut) v =
    real_integral (fun z => distribution_density (nl_noise b) v z *
                            real_indicator (z < cut)).
Proof.
  intros b cut v Hb.
  unfold nl_cdf.
  rewrite q_integral_density by exact Hb.
  apply real_integral_extensional; intro z.
  f_equal.
  rewrite q_eval_indicatorE.
  apply real_indicator_extensional.
  unfold c_lt, update_real, update_real_values.
  cbn [satisfies c_not term_eval real_program_values].
  unfold nl_z; rewrite rpv_eq_dec_refl.
  split; intro H; lra.
Qed.

Lemma nl_pre_equal :
  forall (b Lx Ly : R) (Tx Ty : Term),
    0 < b ->
    (forall w, term_eval Tx w = Lx) ->
    (forall w, term_eval Ty w = Ly) ->
    pformula_valid
      (p_eq (PExpect (QIntegral nl_n (nl_noise b) (QIndicator (nl_test_at Tx Ty))))
            (PExpect (QIntegral nl_n (nl_noise b) (nl_cdf b (1 - (Lx + Ly)))))).
Proof.
  intros b Lx Ly Tx Ty Hb HTx HTy ps Hadm.
  apply psatisfies_p_eq; cbn [pterm_eval].
  apply expectation_extensional; intro v.
  symmetry.
  rewrite (nl_integral_const nl_n (nl_noise b) _ v (q_eval (nl_cdf b (1 - (Lx + Ly))) v) Hb).
  2: { intro w; rewrite !nl_cdf_value by exact Hb; reflexivity. }
  rewrite nl_cdf_value by exact Hb.
  rewrite q_integral_density by exact Hb.
  apply real_integral_extensional; intro z.
  f_equal.
  rewrite q_eval_indicatorE.
  apply real_indicator_extensional.
  unfold nl_test_at, c_lt, update_real, update_real_values.
  cbn [satisfies c_not term_eval real_program_values].
  rewrite HTx, HTy.
  unfold nl_n; rewrite rpv_eq_dec_refl.
  split; intro H; lra.
Qed.

(** * The mechanism *)

Lemma nl_from_chains :
  forall (px py cx cy b Lx Ly : R) (Tx Ty : Term) (eta : PFormula),
    (0 < b)%R ->
    (forall w, term_eval Tx w = Lx) ->
    (forall w, term_eval Ty w = Ly) ->
    {{ $(nl_eq nl_y (QIntegral nl_n (nl_noise b) (QIndicator (nl_test_at Tx Ty)))) }}
      $(nl_prog px py cx cy b)
    {{ $(nl_eq nl_y (QIndicator (FProgBool nl_inside))) }} ->
    {{ $(eta) }}
      $(nl_prog px py cx cy b)
    {{ $(nl_post b (1 - (Lx + Ly))) }}.
Proof.
  intros px py cx cy b Lx Ly Tx Ty eta Hb HTx HTy HT.
  set (A := QIntegral nl_n (nl_noise b) (QIndicator (nl_test_at Tx Ty))).
  set (Q := nl_cdf b (1 - (Lx + Ly))).
  set (B := QIntegral nl_n (nl_noise b) Q).
  assert (HT' : hoare_derivable (nl_eq nl_y B) (nl_prog px py cx cy b) (nl_eq nl_y Q)).
  { apply (nl_chain px py cx cy b Q Q Q Q Hb).
    - apply nl_cdf_block; [left; reflexivity | exact Hb].
    - apply nl_cdf_block; [right; reflexivity | exact Hb].
    - apply nl_bool_cdf. }
  eapply HConseq with
    (eta1 := subst_prob_pformula nl_y (PExpect A) (nl_eq nl_y B))
    (eta2 := nl_post b (1 - (Lx + Ly))).
  - intros ps Hadm _.
    unfold nl_eq; rewrite nl_push_prob_eq.
    cbn [subst_prob_pterm].
    destruct (prob_logic_var_eq_dec nl_y nl_y) as [_ | Hn]; [| contradiction].
    exact (nl_pre_equal b Lx Ly Tx Ty Hb HTx HTy ps Hadm).
  - eapply HElimv with (eta1 := nl_eq nl_y B) (y := nl_y) (p := PExpect A).
    + eapply HConseq with
        (eta1 := p_and (nl_eq nl_y B) (p_eq (PVar nl_y) (PExpect A)))
        (eta2 := p_and (nl_eq nl_y (QIndicator (FProgBool nl_inside))) (nl_eq nl_y Q)).
      * intros ps Hadm; cbn [psatisfies]; tauto.
      * apply HAnd.
        -- eapply HConseq; [| exact HT |].
           ++ intros ps Hadm; cbn [psatisfies]; intro H.
              apply psatisfies_p_and in H; exact (proj2 H).
           ++ intros ps Hadm; cbn [psatisfies]; tauto.
        -- eapply HConseq; [| exact HT' |].
           ++ intros ps Hadm; cbn [psatisfies]; intro H.
              apply psatisfies_p_and in H; exact (proj1 H).
           ++ intros ps Hadm; cbn [psatisfies]; tauto.
      * intros ps Hadm; cbn [psatisfies]; intro H.
        apply psatisfies_p_and in H; destruct H as [H1 H2].
        unfold nl_eq in H1, H2.
        apply psatisfies_p_eq in H1; apply psatisfies_p_eq in H2.
        unfold nl_post; apply psatisfies_p_eq.
        cbn [pterm_eval] in H1, H2 |- *.
        fold Q. lra.
    + cbn [prob_logic_var_occurs_pterm]; tauto.
    + unfold nl_post; cbn [p_eq p_and p_not prob_logic_var_occurs_pformula
                         prob_logic_var_occurs_pterm]; tauto.
  - intros ps Hadm; cbn [psatisfies]; tauto.
Qed.

Lemma nl_abs_value :
  forall d L : R, 0 <= L -> L * L = d * d ->
    (d < 0 -> L = -1 * d) /\ (0 <= d -> L = d).
Proof.
  intros d L HL Hsq; split; intro Hd.
  - assert (H : (L - -1 * d) * (L + -1 * d) = 0) by nra.
    apply Rmult_integral in H; destruct H as [H | H]; nra.
  - assert (H : (L - d) * (L + d) = 0) by nra.
    apply Rmult_integral in H; destruct H as [H | H]; nra.
Qed.

Ltac nl_chain_tac :=
  match goal with
  | |- hoare_derivable
         (nl_eq nl_y (QIntegral nl_n (nl_noise ?b) (QIndicator (nl_test_at ?Tx ?Ty))))
         (nl_prog ?px ?py ?cx ?cy ?b) _ =>
      apply (nl_chain px py cx cy b (QIndicator (FProgBool nl_inside))
               (QIndicator nl_test)
               (QIndicator (subst_real_cformula nl_ay Ty nl_test))
               (QIndicator (nl_test_at Tx Ty))); [assumption | | | apply nl_bool_ind];
      [ first [ apply (nl_ind_block_neg nl_ax (px - cx)
                         (subst_real_cformula nl_ay Ty nl_test)); assumption
              | apply (nl_ind_block_pos nl_ax (px - cx)
                         (subst_real_cformula nl_ay Ty nl_test)); lra ]
      | first [ apply (nl_ind_block_neg nl_ay (py - cy) nl_test); assumption
              | apply (nl_ind_block_pos nl_ay (py - cy) nl_test); lra ] ]
  end.

Theorem nl_correct :
  forall (px py cx cy b Lx Ly : R) (eta : PFormula),
    (0 < b)%R ->
    (0 <= Lx)%R -> (Lx * Lx = (px - cx) * (px - cx))%R ->
    (0 <= Ly)%R -> (Ly * Ly = (py - cy) * (py - cy))%R ->
    {{ $(eta) }}
      $(nl_prog px py cx cy b)
    {{ Pr[nl_inside] = E[ integral nl_z ~ gaussian(0, b),
                           indicator[ nl_z < $(1 - (Lx + Ly)) ] ] }}.
Proof.
  intros px py cx cy b Lx Ly eta Hb HLx Hsqx HLy Hsqy.
  change (hoare_derivable eta (nl_prog px py cx cy b) (nl_post b (1 - (Lx + Ly)))).
  destruct (nl_abs_value (px - cx) Lx HLx Hsqx) as [Hxn Hxp].
  destruct (nl_abs_value (py - cy) Ly HLy Hsqy) as [Hyn Hyp].
  assert (Hflip : forall c w, term_eval (nl_flip_const c) w = -1 * c)
    by (intros; reflexivity).
  destruct (Rlt_dec (px - cx) 0) as [Hx | Hx];
    destruct (Rlt_dec (py - cy) 0) as [Hy | Hy].
  - apply (nl_from_chains px py cx cy b Lx Ly
             (nl_flip_const (px - cx)) (nl_flip_const (py - cy)) eta Hb).
    + intro w; rewrite Hflip; symmetry; apply Hxn, Hx.
    + intro w; rewrite Hflip; symmetry; apply Hyn, Hy.
    + nl_chain_tac.
  - apply (nl_from_chains px py cx cy b Lx Ly
             (nl_flip_const (px - cx)) (TConst (py - cy)) eta Hb).
    + intro w; rewrite Hflip; symmetry; apply Hxn, Hx.
    + intro w; cbn [term_eval]; symmetry; apply Hyp; lra.
    + nl_chain_tac.
  - apply (nl_from_chains px py cx cy b Lx Ly
             (TConst (px - cx)) (nl_flip_const (py - cy)) eta Hb).
    + intro w; cbn [term_eval]; symmetry; apply Hxp; lra.
    + intro w; rewrite Hflip; symmetry; apply Hyn, Hy.
    + nl_chain_tac.
  - apply (nl_from_chains px py cx cy b Lx Ly
             (TConst (px - cx)) (TConst (py - cy)) eta Hb).
    + intro w; cbn [term_eval]; symmetry; apply Hxp; lra.
    + intro w; cbn [term_eval]; symmetry; apply Hyp; lra.
    + nl_chain_tac.
Qed.
