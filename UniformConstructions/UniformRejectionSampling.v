(**
  UniformRejectionSampling.v -- the continuous analogue of the discrete
  rejection sampler in Probabilistic-Hoare-Logic/RejectionSampling.v.

      retry := tt;
      while retry do
        x     <- sample(Uniform(0,1));
        y     <- sample(Uniform(0,1));
        retry := (x < 1/2  /\  y < 1/2)
      end

  THE TRIPLE ([ur_one_third]):

      { E[1_tt] = w }
          ur_prog
      { Pr[x < 1/2  /\  1/2 <= y  /\  ~retry]  =  1/3 * w }

  The PHL original tosses two fair coins and retries while both land true;
  this replaces each toss with a uniform draw on the unit interval and
  retries while both land in the lower half.  Same fixed point,

      s = (1/4) * s + 1/4,   so   s = 1/3,

  and the same answer: the accepted point satisfies [x < 1/2 /\ 1/2 <= y]
  with probability exactly one third.

  Two samples per iteration, so the weakest precondition carries a DOUBLY
  nested [QIntegral].  It stays tractable because the events factor into an
  x-part and a y-part: the inner integral collapses to a constant times an
  indicator on the outer variable, which [real_integral_scale] pulls out.
  No two-dimensional reasoning is needed anywhere.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import ClassicalDescription.
From Stdlib Require Import Classical.
Require Import CPHL.
Require Import SampleBeforeLoop.
Require Import PersistentSampleLoop.
Require Import HalfLaplaceRejection.
Require Import UniformAxiomsAdditional.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * Helpers *)

Lemma ur_real_indicator_and :
  forall P Q : Prop,
    real_indicator (P /\ Q) = (real_indicator P * real_indicator Q)%R.
Proof.
  intros P Q.
  destruct (excluded_middle_informative P) as [HP | HP];
    destruct (excluded_middle_informative Q) as [HQ | HQ].
  - rewrite (real_indicator_true _ (conj HP HQ)).
    rewrite (real_indicator_true P HP), (real_indicator_true Q HQ); ring.
  - rewrite (real_indicator_false (P /\ Q)) by tauto.
    rewrite (real_indicator_false Q HQ); ring.
  - rewrite (real_indicator_false (P /\ Q)) by tauto.
    rewrite (real_indicator_false P HP); ring.
  - rewrite (real_indicator_false (P /\ Q)) by tauto.
    rewrite (real_indicator_false P HP); ring.
Qed.

Lemma rpv_eq_dec_neq :
  forall (x1 x2 : RealProgramVar) (A : Type) (a c : A),
    x1 <> x2 -> (if real_program_var_eq_dec x1 x2 then a else c) = c.
Proof.
  intros x1 x2 A a c Hne.
  destruct (real_program_var_eq_dec x1 x2) as [He | He];
    [contradiction | reflexivity].
Qed.

(** * The program *)

Definition ur_x : RealProgramVar := real_program_var "ur_x".
Definition ur_y : RealProgramVar := real_program_var "ur_y".
Definition ur_retry : BoolProgramVar := bool_program_var "ur_retry".
Definition ur_w : ProbLogicVar := prob_logic_var "ur_w".

Lemma ur_x_neq_y : ur_x <> ur_y.
Proof. unfold ur_x, ur_y; intro H; inversion H. Qed.

Definition ur_unit : Distribution := <{ uniform(0, 1) }>.

Definition ur_xlow : CFormula := <{ ur_x < $(1 / 2) }>.
Definition ur_ylow : CFormula := <{ ur_y < $(1 / 2) }>.
Definition ur_yhigh : CFormula := <{ $(1 / 2) <= ur_y }>.

Definition ur_reject : CFormula := <{ $(ur_xlow) /\ $(ur_ylow) }>.
Definition ur_target : CFormula := <{ $(ur_xlow) /\ $(ur_yhigh) }>.

Definition ur_guard : CFormula := <{ ur_retry }>.

Definition ur_body : Cmd :=
  <{ ur_x     sample $(ur_unit);
     ur_y     sample $(ur_unit);
     ur_retry b= $(ur_reject) }>.

Definition ur_loop : Cmd := <{ while $(ur_guard) do $(ur_body) end }>.

Definition ur_prog : Cmd := <{ ur_retry b= true; $(ur_loop) }>.

(** * Reading the two coordinates back out *)

Lemma ur_val_x :
  forall (v : state) (k m : R),
    real_program_values
      (update_real (update_real v ur_x k) ur_y m) ur_x = k.
Proof.
  intros v k m.
  unfold update_real, update_real_values.
  cbn [real_program_values].
  rewrite (rpv_eq_dec_neq ur_x ur_y _ _ _ ur_x_neq_y).
  rewrite rpv_eq_dec_refl.
  reflexivity.
Qed.

Lemma ur_val_y :
  forall (v : state) (k m : R),
    real_program_values
      (update_real (update_real v ur_x k) ur_y m) ur_y = m.
Proof.
  intros v k m.
  unfold update_real, update_real_values.
  cbn [real_program_values].
  rewrite rpv_eq_dec_refl.
  reflexivity.
Qed.

Lemma ur_sat_xlow :
  forall (v : state) (k m : R),
    satisfies (update_real (update_real v ur_x k) ur_y m) ur_xlow <->
    (k < 1 / 2)%R.
Proof.
  intros v k m.
  unfold ur_xlow, c_lt, c_not.
  cbn [satisfies term_eval].
  rewrite ur_val_x.
  split.
  - intro H.
    destruct (Rlt_dec k (1 / 2)) as [Hd | Hd]; [exact Hd |].
    exfalso; apply H; lra.
  - intros Hk Hc; lra.
Qed.

Lemma ur_sat_ylow :
  forall (v : state) (k m : R),
    satisfies (update_real (update_real v ur_x k) ur_y m) ur_ylow <->
    (m < 1 / 2)%R.
Proof.
  intros v k m.
  unfold ur_ylow, c_lt, c_not.
  cbn [satisfies term_eval].
  rewrite ur_val_y.
  split.
  - intro H.
    destruct (Rlt_dec m (1 / 2)) as [Hd | Hd]; [exact Hd |].
    exfalso; apply H; lra.
  - intros Hm Hc; lra.
Qed.

Lemma ur_sat_yhigh :
  forall (v : state) (k m : R),
    satisfies (update_real (update_real v ur_x k) ur_y m) ur_yhigh <->
    (1 / 2 <= m)%R.
Proof.
  intros v k m.
  unfold ur_yhigh.
  cbn [satisfies term_eval].
  rewrite ur_val_y.
  split; intro H; exact H.
Qed.

Lemma ur_indicator_reject :
  forall (v : state) (k m : R),
    real_indicator
      (satisfies (update_real (update_real v ur_x k) ur_y m) ur_reject) =
    (real_indicator (k < 1 / 2)%R * real_indicator (m < 1 / 2)%R)%R.
Proof.
  intros v k m.
  unfold ur_reject.
  rewrite (real_indicator_extensional _ ((k < 1/2)%R /\ (m < 1/2)%R)).
  - apply ur_real_indicator_and.
  - rewrite satisfies_c_and, ur_sat_xlow, ur_sat_ylow.
    split; intro H; exact H.
Qed.

Lemma ur_indicator_accept :
  forall (v : state) (k m : R),
    real_indicator
      (satisfies (update_real (update_real v ur_x k) ur_y m)
         (c_and ur_target (c_not ur_reject))) =
    (real_indicator (k < 1 / 2)%R * real_indicator (1 / 2 <= m)%R)%R.
Proof.
  intros v k m.
  rewrite (real_indicator_extensional _ ((k < 1/2)%R /\ (1/2 <= m)%R)).
  - apply ur_real_indicator_and.
  - rewrite satisfies_c_and.
    unfold ur_target.
    rewrite satisfies_c_and, ur_sat_xlow, ur_sat_yhigh.
    cbn [c_not satisfies].
    split.
    + intro H.
      destruct H as [Hxy Hrej].
      destruct Hxy as [Hk Hm].
      split; assumption.
    + intros [Hk Hm].
      split; [split; assumption |].
      intro Hrej.
      apply satisfies_c_and in Hrej.
      destruct Hrej as [_ Hyl].
      apply ur_sat_ylow in Hyl; lra.
Qed.

Lemma ur_cdf_half : uniform_cdf 0 1 (1 / 2) = (1 / 2)%R.
Proof.
  unfold uniform_cdf.
  destruct (Rle_dec (1 / 2) 0) as [H | H]; [lra |].
  destruct (Rle_dec 1 (1 / 2)) as [H' | H']; [lra |].
  field.
Qed.

(** * Evaluating the nested integral

    [q_eval_integral] peels exactly one binder, so the inner integral stays
    folded and can be discharged by its own lemma. *)

Lemma q_eval_integral :
  forall (x : RealProgramVar) (d : Distribution) (q : PConstruct) (v : state),
    q_eval (QIntegral x d q) v =
    real_integral
      (fun k => distribution_density d v k * q_eval q (update_real v x k)).
Proof. reflexivity. Qed.

Lemma ur_density_eq :
  forall (v : state) (z : R),
    distribution_density ur_unit v z = uniform_density_R 0 1 z.
Proof. reflexivity. Qed.

Lemma ur_inner_reject :
  forall (v : state) (k : R),
    q_eval (QIntegral ur_y ur_unit (QIndicator ur_reject))
      (update_real v ur_x k) =
    (real_indicator (k < 1 / 2)%R * (1 / 2))%R.
Proof.
  intros v k.
  rewrite q_eval_integral.
  transitivity
    (real_indicator (k < 1 / 2)%R *
     real_integral
       (fun m => uniform_density_R 0 1 m * real_indicator (m < 1 / 2)%R))%R.
  - rewrite <- real_integral_scale.
    apply real_integral_extensional; intro m.
    rewrite ur_density_eq.
    cbn [q_eval].
    rewrite ur_indicator_reject.
    ring.
  - rewrite uniform_integral_strict_cdf by lra.
    rewrite ur_cdf_half.
    reflexivity.
Qed.

Lemma ur_inner_accept :
  forall (v : state) (k : R),
    q_eval (QIntegral ur_y ur_unit
              (QIndicator (c_and ur_target (c_not ur_reject))))
      (update_real v ur_x k) =
    (real_indicator (k < 1 / 2)%R * (1 / 2))%R.
Proof.
  intros v k.
  rewrite q_eval_integral.
  transitivity
    (real_indicator (k < 1 / 2)%R *
     real_integral
       (fun m => uniform_density_R 0 1 m * real_indicator (1 / 2 <= m)%R))%R.
  - rewrite <- real_integral_scale.
    apply real_integral_extensional; intro m.
    rewrite ur_density_eq.
    cbn [q_eval].
    rewrite ur_indicator_accept.
    ring.
  - rewrite uniform_integral_survival by lra.
    rewrite ur_cdf_half.
    lra.
Qed.

Lemma ur_qeval_reject :
  forall v : state,
    q_eval
      (QIntegral ur_x ur_unit (QIntegral ur_y ur_unit (QIndicator ur_reject)))
      v = (1 / 4)%R.
Proof.
  intro v.
  rewrite q_eval_integral.
  transitivity
    ((1 / 2) *
     real_integral
       (fun k => uniform_density_R 0 1 k * real_indicator (k < 1 / 2)%R))%R.
  - rewrite <- real_integral_scale.
    apply real_integral_extensional; intro k.
    rewrite ur_density_eq, ur_inner_reject.
    ring.
  - rewrite uniform_integral_strict_cdf by lra.
    rewrite ur_cdf_half.
    lra.
Qed.

Lemma ur_qeval_accept :
  forall v : state,
    q_eval
      (QIntegral ur_x ur_unit
         (QIntegral ur_y ur_unit
            (QIndicator (c_and ur_target (c_not ur_reject))))) v = (1 / 4)%R.
Proof.
  intro v.
  rewrite q_eval_integral.
  transitivity
    ((1 / 2) *
     real_integral
       (fun k => uniform_density_R 0 1 k * real_indicator (k < 1 / 2)%R))%R.
  - rewrite <- real_integral_scale.
    apply real_integral_extensional; intro k.
    rewrite ur_density_eq, ur_inner_accept.
    ring.
  - rewrite uniform_integral_strict_cdf by lra.
    rewrite ur_cdf_half.
    lra.
Qed.

(** * Certificate data *)

Definition ur_regions (_ : nat) : CFormula := ur_guard.
Definition ur_transitions (_ _ : nat) : R := 1 / 4.
Definition ur_exits (_ : nat) : R := 1 / 4.
Definition ur_solution (_ : nat) : R := 1 / 3.
Definition ur_q : PConstruct := QIndicator ur_target.

(** [HRealSample]'s validity premise is an implication from the
    precondition, so it is stated in that shape. *)
Lemma ur_unit_valid_under :
  forall pre : PFormula,
    pformula_valid
      (PFImpl pre (p_almost_sure (distribution_valid_formula ur_unit))).
Proof.
  intros pre ps.
  cbn [psatisfies]; intro Hignore.
  clear Hignore; revert ps.
  apply p_almost_sure_of_pointwise.
  intro v.
  unfold ur_unit.
  cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
  intro Hle; lra.
Qed.

(** * The body premise *)

Lemma ur_body_step :
  forall i : nat,
    (i < 1)%nat ->
    hoare_derivable
      (p_concentrated_mass (ur_regions i) (PConst 1))
      ur_body
      (while_body_post 1 ur_regions (ur_transitions i) ur_guard ur_q
         (ur_exits i)).
Proof.
  intros i Hi.
  unfold ur_body.
  eapply HSeq with
    (eta2 :=
       sample_pformula ur_y ur_unit
         (subst_bool_pformula ur_retry ur_reject
            (while_body_post 1 ur_regions (ur_transitions i) ur_guard ur_q
               (ur_exits i)))).
  - apply HRealSample; [| apply ur_unit_valid_under].
    intro ps.
    cbn [psatisfies].
    intro Hpre.
    apply psatisfies_p_and in Hpre.
    destruct Hpre as [_ Hmass].
    apply psatisfies_p_eq in Hmass.
    cbn [pterm_eval] in Hmass.
    unfold while_body_post, ur_q, ur_regions, ur_guard, ur_transitions,
      ur_exits.
    cbn [finite_p_and condition_pconstruct condition_pconstruct_fuel
         pconstruct_size].
    rewrite !subst_bool_pformula_p_and, !subst_bool_pformula_p_eq.
    rewrite !sample_pformula_p_and, !sample_pformula_p_eq.
    apply psatisfies_p_and; split; [apply psatisfies_p_and; split | ].
    + apply psatisfies_p_true.
    + apply psatisfies_p_eq.
      cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_cformula
           sample_pterm pterm_eval].
      rewrite !bpv_eq_dec_refl.
      rewrite (t3_expect_const ps _ (1 / 4)%R Hmass);
        [reflexivity | intro v; apply ur_qeval_reject].
    + apply psatisfies_p_eq.
      cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_cformula
           ur_target c_and c_not sample_pterm pterm_eval].
      rewrite !bpv_eq_dec_refl.
      rewrite (t3_expect_const ps _ (1 / 4)%R Hmass);
        [reflexivity | intro v; apply ur_qeval_accept].
  - eapply HSeq with
      (eta2 :=
         subst_bool_pformula ur_retry ur_reject
           (while_body_post 1 ur_regions (ur_transitions i) ur_guard ur_q
              (ur_exits i))).
    + apply HRealSample; [| apply ur_unit_valid_under].
      intro ps; cbn [psatisfies]; intro H; exact H.
    + apply HBoolAssign.
Qed.

(** * The loop

    [s = (1/4) * s + 1/4], whose bounded solution is [1/3] -- the same
    fixed point the discrete PHL proof solves, reached through uniform
    integrals rather than coin tosses. *)

Lemma ur_loop_derivable :
  hoare_derivable
    (p_concentrated_mass (ur_regions 0) (PVar ur_w))
    ur_loop
    (p_eq (PExpect (condition_pconstruct ur_q (c_not ur_guard)))
       (PMul (PConst (ur_solution 0)) (PVar ur_w))).
Proof.
  eapply HWhile with
    (m := 1%nat) (k := 0%nat)
    (regions := ur_regions) (solution := ur_solution)
    (exits := ur_exits) (transitions := ur_transitions).
  - lia.
  - unfold while_regions_cover, cformula_valid, ur_regions.
    intro v; cbn [finite_c_or c_or c_not satisfies]; tauto.
  - unfold while_regions_in_guard, cformula_valid, ur_regions.
    intros i Hi v; cbn [satisfies]; tauto.
  - unfold while_regions_disjoint; intros i j Hi Hj; lia.
  - unfold while_progress, ur_exits.
    intros i Hi; left; lra.
  - exact ur_body_step.
  - unfold while_solution, ur_solution, ur_transitions, ur_exits.
    intros i Hi; cbn [finite_r_sum]; split; lra.
Qed.

(** * The sampler

    Conditioned on acceptance, the point lands in the upper-left quadrant
    of the unit square with probability exactly one third. *)

Theorem ur_one_third :
  {{ Pr[true] = ur_w }}
    $(ur_prog)
  {{ E[$(condition_pconstruct ur_q (c_not ur_guard))] = $(1 / 3) * ur_w }}.
Proof.
  unfold ur_prog.
  eapply HSeq with
    (eta2 := p_concentrated_mass (ur_regions 0) (PVar ur_w)).
  - eapply HConseq with
      (eta1 :=
         subst_bool_pformula ur_retry c_true
           (p_concentrated_mass (ur_regions 0) (PVar ur_w)))
      (eta2 := p_concentrated_mass (ur_regions 0) (PVar ur_w)).
    + intro ps.
      cbn [psatisfies].
      intro Hpre.
      apply psatisfies_p_eq in Hpre.
      cbn [pterm_eval] in Hpre.
      unfold p_concentrated_mass, ur_regions, ur_guard.
      rewrite subst_bool_pformula_p_and, !subst_bool_pformula_p_eq.
      apply psatisfies_p_and; split; apply psatisfies_p_eq;
        cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_cformula
             pterm_eval].
      * rewrite !bpv_eq_dec_refl; reflexivity.
      * exact Hpre.
    + apply HBoolAssign.
    + intro ps; cbn [psatisfies]; tauto.
  - replace (1 / 3)%R with (ur_solution 0) by reflexivity.
    exact ur_loop_derivable.
Qed.
