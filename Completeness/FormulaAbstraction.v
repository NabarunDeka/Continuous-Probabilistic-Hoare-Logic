(** Replace comparison terms by fresh rigid variables, retaining the entire
    propositional structure. This is an assertion-language construction. *)
From Stdlib Require Import List.
Require Import CPHL Soundness.AssertionLogic Completeness.Freshness.
Import ListNotations.

Fixpoint comparison_terms (eta : PFormula) : list Pterm :=
  match eta with
  | PFLe a b => [a;b]
  | PFFalse => []
  | PFImpl a b => comparison_terms a ++ comparison_terms b
  end.

Lemma comparison_term_vars eta p y : In p (comparison_terms eta) ->
  prob_logic_var_occurs_pterm y p -> prob_logic_var_occurs_pformula y eta.
Proof.
  induction eta; cbn; intros H Hy.
  - destruct H as [H | H]; [subst; auto |].
    destruct H as [H | H]; [subst; auto | contradiction].
  - contradiction.
  - apply in_app_iff in H; destruct H; [left; eapply IHeta1 | right; eapply IHeta2]; eauto.
Qed.

Definition bindings_hold (ps : Pstate) (bs : list (ProbLogicVar * Pterm)) : Prop :=
  forall y p, In (y,p) bs -> pstate_prob_logic_values ps y = pterm_eval p ps.

(** The witness retains a binding for each comparison-term occurrence.
    Duplicate terms are allowed, but the auxiliary names are distinct. *)
Record formula_abstraction (eta : PFormula) (avoid : list ProbLogicVar)
    (frame : PFormula) (bs : list (ProbLogicVar * Pterm)) : Prop := {
  abstraction_analytical : pformula_analytical frame;
  abstraction_distinct : NoDup (map (@fst ProbLogicVar Pterm) bs);
  abstraction_avoids : forall y p, In (y,p) bs -> ~ In y avoid;
  abstraction_terms : forall y p, In (y,p) bs -> In p (comparison_terms eta);
  abstraction_correct : forall ps, bindings_hold ps bs ->
    (psatisfies ps frame <-> psatisfies ps eta)
}.

Lemma nodup_app_disjoint (A : Type) (xs ys : list A) :
  NoDup xs -> NoDup ys -> (forall x, In x xs -> ~ In x ys) -> NoDup (xs ++ ys).
Proof.
  intros Hxs Hys Hdis; induction Hxs; cbn; [exact Hys |].
  constructor.
  - rewrite in_app_iff; intro Hin; destruct Hin; [contradiction | eapply Hdis; eauto; cbn; auto].
  - apply IHHxs; intros z Hz; apply Hdis; cbn; auto.
Qed.

Theorem formula_abstraction_exists eta : forall avoid,
  exists frame bs, formula_abstraction eta avoid frame bs.
Proof.
  induction eta as [a b | | a IHa b IHb]; intro avoid.
  - set (u := fresh_prob_logic_var avoid).
    set (v := fresh_prob_logic_var (u :: avoid)).
    assert (Hu : ~ In u avoid) by apply fresh_prob_logic_var_not_in.
    assert (Hv : ~ In v (u :: avoid)) by apply fresh_prob_logic_var_not_in.
    exists (PFLe (PVar u) (PVar v)), [(u,a);(v,b)]; constructor.
    + cbn; auto.
    + cbn; repeat constructor; cbn in *; intuition congruence.
    + intros y p H; cbn in H; destruct H as [H | H].
      * inversion H; subst; exact Hu.
      * destruct H as [H | H]; [inversion H; subst; cbn in Hv; tauto | contradiction].
    + intros y p H; cbn in H; destruct H as [H | H].
      * inversion H; subst; cbn; auto.
      * destruct H as [H | H]; [inversion H; subst; cbn; auto | contradiction].
    + intros ps H; cbn [psatisfies pterm_eval].
      rewrite (H u a (or_introl eq_refl)), (H v b (or_intror (or_introl eq_refl))).
      reflexivity.
  - exists PFFalse, []; constructor.
    + cbn; auto.
    + constructor.
    + intros y p H; inversion H.
    + intros y p H; inversion H.
    + intros ps H; reflexivity.
  - destruct (IHa avoid) as [fa Hfa]; destruct Hfa as [ba Ha].
    destruct (IHb (map (@fst ProbLogicVar Pterm) ba ++ avoid)) as [fb Hfb];
    destruct Hfb as [bb Hb].
    exists (PFImpl fa fb), (ba ++ bb); constructor.
    + split; [exact (abstraction_analytical _ _ _ _ Ha) | exact (abstraction_analytical _ _ _ _ Hb)].
    + rewrite map_app; apply nodup_app_disjoint.
      * exact (abstraction_distinct _ _ _ _ Ha).
      * exact (abstraction_distinct _ _ _ _ Hb).
      * intros y Hya Hyb; apply in_map_iff in Hyb.
        destruct Hyb as [yp Hpair]; destruct yp as [z p];
        destruct Hpair as [Heq Hin]; cbn in Heq; subst z.
        apply (abstraction_avoids _ _ _ _ Hb y p Hin); apply in_app_iff; auto.
    + intros y p H; apply in_app_iff in H; destruct H as [H | H].
      * exact (abstraction_avoids _ _ _ _ Ha y p H).
      * intro Hy; apply (abstraction_avoids _ _ _ _ Hb y p H); apply in_app_iff; auto.
    + intros y p H; apply in_app_iff in H; cbn; apply in_app_iff.
      destruct H as [H | H]; [left; exact (abstraction_terms _ _ _ _ Ha y p H) |
        right; exact (abstraction_terms _ _ _ _ Hb y p H)].
    + intros ps H; cbn [psatisfies].
      assert (HA : bindings_hold ps ba).
      { intros y p Hin; apply H; apply in_app_iff; auto. }
      assert (HB : bindings_hold ps bb).
      { intros y p Hin; apply H; apply in_app_iff; auto. }
      rewrite (abstraction_correct _ _ _ _ Ha ps HA),
        (abstraction_correct _ _ _ _ Hb ps HB); reflexivity.
Qed.
