(** Derived syntactic rules for completeness; no new Hoare constructors.
    All results apply to arbitrary commands, including loops. *)
From Stdlib Require Import List Reals Lra.
Require Import CPHL Soundness.AssertionLogic Soundness.ProbabilisticSubstitution
  Completeness.Freshness.
Import ListNotations.

Lemma derive_pre pre pre' C post :
  pformula_valid (PFImpl pre pre') -> hoare_derivable pre' C post ->
  hoare_derivable pre C post.
Proof.
  intros Himp Hder; eapply HConseq; [exact Himp | exact Hder |].
  intros ps Hps H; exact H.
Qed.

Lemma derive_post pre C post post' :
  hoare_derivable pre C post -> pformula_valid (PFImpl post post') ->
  hoare_derivable pre C post'.
Proof.
  intros Hder Himp; eapply HConseq; [| exact Hder | exact Himp].
  intros ps Hps H; exact H.
Qed.

Lemma derive_true pre C : hoare_derivable pre C p_true.
Proof.
  eapply derive_pre with (pre' := p_true).
  - intros ps Hps H; apply psatisfies_true.
  - apply HFree; cbn [p_true pformula_analytical]; auto.
Qed.

(** Analytical assertions depend only on rigid external logical values. *)
Lemma derive_analytical_frame pre C post frame :
  pformula_analytical frame -> hoare_derivable pre C post ->
  hoare_derivable (p_and pre frame) C (p_and post frame).
Proof.
  intros Hframe Hder; apply HAnd.
  - eapply derive_pre; [| exact Hder].
    intros ps Hps H; apply (proj1 (psatisfies_and _ _ _)) in H; tauto.
  - eapply derive_pre with (pre' := frame).
    + intros ps Hps H; apply (proj1 (psatisfies_and _ _ _)) in H; tauto.
    + apply HFree; exact Hframe.
Qed.

Fixpoint pformula_conjunction (posts : list PFormula) : PFormula :=
  match posts with
  | [] => p_true
  | post :: rest => p_and post (pformula_conjunction rest)
  end.

Lemma psatisfies_conjunction ps posts :
  psatisfies ps (pformula_conjunction posts) <->
  forall post, In post posts -> psatisfies ps post.
Proof.
  induction posts as [|post rest IH]; cbn [pformula_conjunction].
  - split; [intros _ eta H; inversion H | intros _; apply psatisfies_true].
  - rewrite psatisfies_and, IH; cbn; split.
    + intros [Hpost Hrest] eta [<- | H]; auto.
    + intro H; split; [apply H; auto | intros eta Hin; apply H; auto].
Qed.

Lemma derive_conjunction pre C posts :
  (forall post, In post posts -> hoare_derivable pre C post) ->
  hoare_derivable pre C (pformula_conjunction posts).
Proof.
  induction posts as [|post rest IH]; intro H; cbn [pformula_conjunction].
  - apply derive_true.
  - apply HAnd; [apply H; cbn; auto | apply IH; intros eta Hin; apply H; cbn; auto].
Qed.

(** The head binding is the outermost conjunct and is eliminated first.
    Explicit pairs avoid any length assumptions about separately zipped lists. *)
Definition ProbBindings := list (ProbLogicVar * Pterm).

Fixpoint bindings_precondition (bindings : ProbBindings) (pre : PFormula) : PFormula :=
  match bindings with
  | [] => pre
  | (y,p) :: rest => p_and (bindings_precondition rest pre) (p_eq (PVar y) p)
  end.

Fixpoint substitute_bindings (bindings : ProbBindings) (pre : PFormula) : PFormula :=
  match bindings with
  | [] => pre
  | (y,p) :: rest => substitute_bindings rest (subst_prob_pformula y p pre)
  end.

(** Every auxiliary name is distinct and absent from every replacement.
    This is the situation obtained by choosing names fresh for all preterms. *)
Definition independent_bindings (bindings : ProbBindings) : Prop :=
  NoDup (map (@fst ProbLogicVar Pterm) bindings) /\
  forall y p z r, In (y,p) bindings -> In (z,r) bindings ->
    ~ prob_logic_var_occurs_pterm y r.

Lemma substitute_bindings_precondition y p bindings pre :
  (forall z r, In (z,r) bindings ->
    z <> y /\ ~ prob_logic_var_occurs_pterm y r) ->
  subst_prob_pformula y p (bindings_precondition bindings pre) =
  bindings_precondition bindings (subst_prob_pformula y p pre).
Proof.
  induction bindings as [|[z r] rest IH]; intro H; [reflexivity |].
  change (p_and (subst_prob_pformula y p (bindings_precondition rest pre))
    (subst_prob_pformula y p (p_eq (PVar z) r)) =
    p_and (bindings_precondition rest (subst_prob_pformula y p pre)) (p_eq (PVar z) r)).
  rewrite IH by (intros; apply H; cbn; auto).
  rewrite (subst_prob_pformula_fresh y p (p_eq (PVar z) r)); [reflexivity |].
  destruct (H z r (or_introl eq_refl)) as [Hneq Hfresh].
  cbn [p_eq p_and p_not prob_logic_var_occurs_pformula prob_logic_var_occurs_pterm];
    intuition congruence.
Qed.

Lemma derive_eliminate_bindings bindings pre C post :
  independent_bindings bindings ->
  (forall y p, In (y,p) bindings -> ~ prob_logic_var_occurs_pformula y post) ->
  hoare_derivable (bindings_precondition bindings pre) C post ->
  hoare_derivable (substitute_bindings bindings pre) C post.
Proof.
  revert pre; induction bindings as [|[y p] rest IH]; intros pre Hind Hpost Hder.
  - exact Hder.
  - destruct Hind as [Hdistinct Hfresh].
    inversion Hdistinct as [|? ? Hnotin Hnodup]; subst.
    assert (Htail : independent_bindings rest).
    { split; [exact Hnodup |].
      intros z r w t Hz Hw; apply (Hfresh z r w t); cbn; auto. }
    assert (Hy : ~ prob_logic_var_occurs_pterm y p).
    { apply (Hfresh y p y p); cbn; auto. }
    assert (HyPost : ~ prob_logic_var_occurs_pformula y post).
    { apply (Hpost y p); cbn; auto. }
    pose proof (HElimv (bindings_precondition rest pre) post y p C Hder Hy HyPost) as Helim.
    rewrite substitute_bindings_precondition in Helim.
    + cbn [substitute_bindings]; apply IH; [exact Htail | | exact Helim].
      intros z r Hz; apply (Hpost z r); cbn; auto.
    + intros z r Hz; split.
      * intro Heq; subst z; apply Hnotin.
        apply in_map_iff; exists (y,r); split; [reflexivity | exact Hz].
      * apply (Hfresh y p z r); cbn; auto.
Qed.

(** Exact SUM is derived from the existing lower and upper versions. *)
Lemma derive_sum_eq eta1 eta2 gamma1 gamma2 q y1 y2 C :
  cformula_valid (c_not (c_and gamma1 gamma2)) ->
  hoare_derivable (p_and eta1 (p_almost_sure gamma1)) C
    (p_eq (PVar y1) (PExpect q)) ->
  hoare_derivable (p_and eta2 (p_almost_sure gamma2)) C
    (p_eq (PVar y2) (PExpect q)) ->
  hoare_derivable (sum_precondition eta1 eta2 gamma1 gamma2) C
    (p_eq (PAdd (PVar y1) (PVar y2)) (PExpect q)).
Proof.
  intros Hdis H1 H2; unfold p_eq; apply HAnd.
  - apply HSumLe; [exact Hdis | |].
    + eapply derive_post; [exact H1 |].
      intros ps Hps H; apply (proj1 (psatisfies_eq _ _ _)) in H;
        cbn [psatisfies]; lra.
    + eapply derive_post; [exact H2 |].
      intros ps Hps H; apply (proj1 (psatisfies_eq _ _ _)) in H;
        cbn [psatisfies]; lra.
  - apply HSumGe; [exact Hdis | |].
    + eapply derive_post; [exact H1 |].
      intros ps Hps H; apply (proj1 (psatisfies_eq _ _ _)) in H;
        cbn [psatisfies]; lra.
    + eapply derive_post; [exact H2 |].
      intros ps Hps H; apply (proj1 (psatisfies_eq _ _ _)) in H;
        cbn [psatisfies]; lra.
Qed.
