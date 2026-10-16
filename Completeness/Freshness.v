(** Finite support and capture-free probabilistic logical substitution.
    Integral binders bind program variables, never these logical variables. *)
From Stdlib Require Import List String Arith Lia.
Require Import CPHL Soundness.ProbabilisticSubstitution.
Import ListNotations.

Fixpoint pterm_prob_vars (p : Pterm) : list ProbLogicVar :=
  match p with
  | PVar y => [y]
  | PConst _ | PExpect _ => []
  | PAdd p1 p2 | PMul p1 p2 => pterm_prob_vars p1 ++ pterm_prob_vars p2
  end.

Fixpoint pformula_prob_vars (eta : PFormula) : list ProbLogicVar :=
  match eta with
  | PFLe p1 p2 => pterm_prob_vars p1 ++ pterm_prob_vars p2
  | PFFalse => []
  | PFImpl eta1 eta2 => pformula_prob_vars eta1 ++ pformula_prob_vars eta2
  end.

Lemma pterm_prob_vars_spec y p :
  In y (pterm_prob_vars p) <-> prob_logic_var_occurs_pterm y p.
Proof.
  induction p; cbn; try rewrite in_app_iff, IHp1, IHp2; intuition congruence.
Qed.

Lemma pformula_prob_vars_spec y eta :
  In y (pformula_prob_vars eta) <-> prob_logic_var_occurs_pformula y eta.
Proof.
  induction eta; cbn.
  - rewrite in_app_iff, !pterm_prob_vars_spec; reflexivity.
  - tauto.
  - rewrite in_app_iff, IHeta1, IHeta2; reflexivity.
Qed.

Definition prob_logic_var_name (y : ProbLogicVar) : string :=
  match y with prob_logic_var name => name end.

Fixpoint maximum_prob_logic_var_name_length (avoid : list ProbLogicVar) : nat :=
  match avoid with
  | [] => 0
  | y :: ys => Nat.max (String.length (prob_logic_var_name y))
      (maximum_prob_logic_var_name_length ys)
  end.

Definition fresh_prob_logic_var (avoid : list ProbLogicVar) : ProbLogicVar :=
  prob_logic_var (repeated_underscores (S (maximum_prob_logic_var_name_length avoid))).

Lemma prob_logic_var_name_length_bound y avoid : In y avoid ->
  (String.length (prob_logic_var_name y) <= maximum_prob_logic_var_name_length avoid)%nat.
Proof.
  induction avoid as [|z zs IH]; cbn; intros H; [contradiction |].
  destruct H as [<- | H]; [apply Nat.le_max_l |].
  eapply Nat.le_trans; [apply IH; exact H | apply Nat.le_max_r].
Qed.

Lemma fresh_prob_logic_var_not_in avoid : ~ In (fresh_prob_logic_var avoid) avoid.
Proof.
  intro H; pose proof (prob_logic_var_name_length_bound _ _ H) as Hb.
  unfold fresh_prob_logic_var in Hb; cbn in Hb.
  rewrite repeated_underscores_length in Hb; lia.
Qed.

Fixpoint fresh_prob_logic_vars (n : nat) (avoid : list ProbLogicVar) : list ProbLogicVar :=
  match n with
  | O => []
  | S k => let y := fresh_prob_logic_var avoid in
      y :: fresh_prob_logic_vars k (y :: avoid)
  end.

Lemma fresh_prob_logic_vars_length n avoid :
  List.length (fresh_prob_logic_vars n avoid) = n.
Proof. revert avoid; induction n; intro avoid; cbn; auto. Qed.

Lemma fresh_prob_logic_vars_avoid n avoid y :
  In y (fresh_prob_logic_vars n avoid) -> ~ In y avoid.
Proof.
  revert avoid; induction n as [|n IH]; intros avoid H; cbn in H; [contradiction |].
  destruct H as [<- | H].
  - apply fresh_prob_logic_var_not_in.
  - intro Ha; apply (IH _ H); cbn; auto.
Qed.

Lemma fresh_prob_logic_vars_nodup n avoid : NoDup (fresh_prob_logic_vars n avoid).
Proof.
  revert avoid; induction n as [|n IH]; intro avoid; cbn; constructor.
  - intro H; apply (fresh_prob_logic_vars_avoid _ _ _ H); cbn; auto.
  - apply IH.
Qed.

(** Union the support lists of every expression that must remain untouched.
    Duplicates in the avoidance list are harmless. *)
Lemma fresh_prob_logic_var_pterm p :
  ~ prob_logic_var_occurs_pterm (fresh_prob_logic_var (pterm_prob_vars p)) p.
Proof.
  rewrite <- pterm_prob_vars_spec; apply fresh_prob_logic_var_not_in.
Qed.

Lemma fresh_prob_logic_var_pformula eta :
  ~ prob_logic_var_occurs_pformula (fresh_prob_logic_var (pformula_prob_vars eta)) eta.
Proof.
  rewrite <- pformula_prob_vars_spec; apply fresh_prob_logic_var_not_in.
Qed.

(** Substitution removes the replaced occurrence and can introduce only
    variables from its replacement. This bound also covers self-reference. *)
Lemma subst_prob_pterm_occurs_bound y replacement p z :
  prob_logic_var_occurs_pterm z (subst_prob_pterm y replacement p) ->
  (z <> y /\ prob_logic_var_occurs_pterm z p) \/
  prob_logic_var_occurs_pterm z replacement.
Proof.
  induction p as [v | r | q | p1 IH1 p2 IH2 | p1 IH1 p2 IH2]; cbn.
  - destruct (prob_logic_var_eq_dec v y) as [Heq | Hneq]; cbn; intuition congruence.
  - tauto.
  - tauto.
  - intuition.
  - intuition.
Qed.

Lemma subst_prob_pformula_occurs_bound y replacement eta z :
  prob_logic_var_occurs_pformula z (subst_prob_pformula y replacement eta) ->
  (z <> y /\ prob_logic_var_occurs_pformula z eta) \/
  prob_logic_var_occurs_pterm z replacement.
Proof.
  induction eta; cbn.
  - pose proof (subst_prob_pterm_occurs_bound y replacement p1 z).
    pose proof (subst_prob_pterm_occurs_bound y replacement p2 z); tauto.
  - tauto.
  - tauto.
Qed.

Lemma subst_prob_pterm_preserves_fresh y replacement p z :
  ~ prob_logic_var_occurs_pterm z p ->
  ~ prob_logic_var_occurs_pterm z replacement ->
  ~ prob_logic_var_occurs_pterm z (subst_prob_pterm y replacement p).
Proof. pose proof (subst_prob_pterm_occurs_bound y replacement p z); tauto. Qed.

Lemma subst_prob_pformula_preserves_fresh y replacement eta z :
  ~ prob_logic_var_occurs_pformula z eta ->
  ~ prob_logic_var_occurs_pterm z replacement ->
  ~ prob_logic_var_occurs_pformula z (subst_prob_pformula y replacement eta).
Proof. pose proof (subst_prob_pformula_occurs_bound y replacement eta z); tauto. Qed.

Lemma subst_prob_pterm_removes y replacement p :
  ~ prob_logic_var_occurs_pterm y replacement ->
  ~ prob_logic_var_occurs_pterm y (subst_prob_pterm y replacement p).
Proof. pose proof (subst_prob_pterm_occurs_bound y replacement p y); tauto. Qed.

Lemma subst_prob_pformula_removes y replacement eta :
  ~ prob_logic_var_occurs_pterm y replacement ->
  ~ prob_logic_var_occurs_pformula y (subst_prob_pformula y replacement eta).
Proof. pose proof (subst_prob_pformula_occurs_bound y replacement eta y); tauto. Qed.

(** Independent bindings may be eliminated in either order. Cross-freshness
    prevents one replacement from being changed by the other substitution. *)
Lemma subst_prob_pterm_commute y z a b p :
  y <> z -> ~ prob_logic_var_occurs_pterm z a ->
  ~ prob_logic_var_occurs_pterm y b ->
  subst_prob_pterm y a (subst_prob_pterm z b p) =
  subst_prob_pterm z b (subst_prob_pterm y a p).
Proof.
  intros Hneq Ha Hb;
    induction p as [v | r | q | p1 IH1 p2 IH2 | p1 IH1 p2 IH2]; cbn.
  - destruct (prob_logic_var_eq_dec v z) as [Hz | Hz];
      destruct (prob_logic_var_eq_dec v y) as [Hy | Hy].
    + congruence.
    + subst v; rewrite (subst_prob_pterm_fresh y a b Hb); cbn.
      destruct (prob_logic_var_eq_dec z z); congruence.
    + subst v; rewrite (subst_prob_pterm_fresh z b a Ha); cbn.
      destruct (prob_logic_var_eq_dec y y); congruence.
    + cbn; destruct (prob_logic_var_eq_dec v y), (prob_logic_var_eq_dec v z); congruence.
  - reflexivity.
  - reflexivity.
  - now rewrite IH1, IH2.
  - now rewrite IH1, IH2.
Qed.

Lemma subst_prob_pformula_commute y z a b eta :
  y <> z -> ~ prob_logic_var_occurs_pterm z a ->
  ~ prob_logic_var_occurs_pterm y b ->
  subst_prob_pformula y a (subst_prob_pformula z b eta) =
  subst_prob_pformula z b (subst_prob_pformula y a eta).
Proof.
  intros Hneq Ha Hb; induction eta; cbn.
  - rewrite (subst_prob_pterm_commute y z a b p1 Hneq Ha Hb),
      (subst_prob_pterm_commute y z a b p2 Hneq Ha Hb); reflexivity.
  - reflexivity.
  - now rewrite IHeta1, IHeta2.
Qed.
