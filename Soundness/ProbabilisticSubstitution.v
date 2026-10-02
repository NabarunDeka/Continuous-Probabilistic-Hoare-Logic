(** External probabilistic-variable substitution and freshness. This layer
    changes rho only; real and Boolean logic coordinates remain part of the
    joint state measure and may be correlated with program coordinates. *)
From Stdlib Require Import Reals.
From mathcomp Require Import boot.
Require Import CPHL Soundness.AssertionLogic.

(** Assignment is a single update, not recursive substitution into its value. *)
Definition update_prob_assignment (rho : ProbLogicVar -> R)
  (y : ProbLogicVar) (value : R) : ProbLogicVar -> R :=
  fun z => if prob_logic_var_eq_dec z y then value else rho z.

Definition update_prob_state (ps : Pstate) (y : ProbLogicVar) (value : R) : Pstate :=
  {| pstate_measure := pstate_measure ps;
     pstate_prob_logic_values := update_prob_assignment (pstate_prob_logic_values ps) y value |}.

Lemma update_prob_assignment_here rho y value :
  update_prob_assignment rho y value y = value.
Proof.
  change ((if prob_logic_var_eq_dec y y then value else rho y) = value).
  destruct (prob_logic_var_eq_dec y y) as [Heq | Hneq].
  - reflexivity.
  - exfalso; apply Hneq; reflexivity.
Qed.

Lemma update_prob_assignment_other rho y z value : z <> y ->
  update_prob_assignment rho y value z = rho z.
Proof.
  intros H; change ((if prob_logic_var_eq_dec z y then value else rho z) = rho z).
  destruct (prob_logic_var_eq_dec z y) as [Heq | Hneq].
  - contradiction.
  - reflexivity.
Qed.

Lemma update_prob_state_measure ps y value :
  pstate_measure (update_prob_state ps y value) = pstate_measure ps.
Proof. reflexivity. Qed.

Lemma update_prob_state_admissible ps y value :
  pstate_admissible (update_prob_state ps y value) <-> pstate_admissible ps.
Proof. reflexivity. Qed.

(** No freshness assumption is needed here: the replacement is evaluated
    once in ps, even if it contains y or an expectation of the input measure. *)
Lemma subst_prob_pterm_correct y replacement p ps :
  pterm_eval (subst_prob_pterm y replacement p) ps =
  pterm_eval p (update_prob_state ps y (pterm_eval replacement ps)).
Proof.
  induction p as [z | c | q | p1 IHp1 p2 IHp2 | p1 IHp1 p2 IHp2];
    cbn [subst_prob_pterm pterm_eval update_prob_state
    pstate_measure pstate_prob_logic_values update_prob_assignment].
  - destruct (prob_logic_var_eq_dec z y) as [Heq | Hneq].
    + subst z; symmetry; apply update_prob_assignment_here.
    + symmetry; apply update_prob_assignment_other; exact Hneq.
  - reflexivity.
  - reflexivity.
  - rewrite IHp1 IHp2; reflexivity.
  - rewrite IHp1 IHp2; reflexivity.
Qed.

Lemma subst_prob_pformula_correct y replacement eta ps :
  psatisfies ps (subst_prob_pformula y replacement eta) <->
  psatisfies (update_prob_state ps y (pterm_eval replacement ps)) eta.
Proof.
  induction eta; cbn [subst_prob_pformula psatisfies].
  - now rewrite !subst_prob_pterm_correct.
  - tauto.
  - tauto.
Qed.

(** A variable absent from a term or formula can be changed without changing
    its interpretation. The measure and all other external values stay fixed. *)
Lemma pterm_eval_update_prob_fresh y p ps value :
  ~ prob_logic_var_occurs_pterm y p ->
  pterm_eval p (update_prob_state ps y value) = pterm_eval p ps.
Proof.
  induction p as [z | c | q | p1 IHp1 p2 IHp2 | p1 IHp1 p2 IHp2];
    cbn [prob_logic_var_occurs_pterm pterm_eval]; intros H.
  - apply update_prob_assignment_other; congruence.
  - reflexivity.
  - reflexivity.
  - assert (H1 : ~ prob_logic_var_occurs_pterm y p1) by tauto.
    assert (H2 : ~ prob_logic_var_occurs_pterm y p2) by tauto.
    rewrite (IHp1 H1) (IHp2 H2); reflexivity.
  - assert (H1 : ~ prob_logic_var_occurs_pterm y p1) by tauto.
    assert (H2 : ~ prob_logic_var_occurs_pterm y p2) by tauto.
    rewrite (IHp1 H1) (IHp2 H2); reflexivity.
Qed.

Lemma psatisfies_update_prob_fresh y eta ps value :
  ~ prob_logic_var_occurs_pformula y eta ->
  (psatisfies (update_prob_state ps y value) eta <-> psatisfies ps eta).
Proof.
  induction eta; cbn [prob_logic_var_occurs_pformula psatisfies]; intros H.
  - assert (H1 : ~ prob_logic_var_occurs_pterm y p1) by tauto.
    assert (H2 : ~ prob_logic_var_occurs_pterm y p2) by tauto.
    rewrite (pterm_eval_update_prob_fresh y p1 ps value H1)
      (pterm_eval_update_prob_fresh y p2 ps value H2); reflexivity.
  - tauto.
  - assert (H1 : ~ prob_logic_var_occurs_pformula y eta1) by tauto.
    assert (H2 : ~ prob_logic_var_occurs_pformula y eta2) by tauto.
    pose proof (IHeta1 H1); pose proof (IHeta2 H2); tauto.
Qed.

(** The same independence can be used before interpretation: substitution
    leaves a y-free syntactic expression unchanged. *)
Lemma subst_prob_pterm_fresh y replacement p :
  ~ prob_logic_var_occurs_pterm y p -> subst_prob_pterm y replacement p = p.
Proof.
  induction p as [z | c | q | p1 IHp1 p2 IHp2 | p1 IHp1 p2 IHp2];
    cbn [prob_logic_var_occurs_pterm subst_prob_pterm]; intros H.
  - destruct (prob_logic_var_eq_dec z y); [congruence | reflexivity].
  - reflexivity.
  - reflexivity.
  - assert (H1 : ~ prob_logic_var_occurs_pterm y p1) by tauto.
    assert (H2 : ~ prob_logic_var_occurs_pterm y p2) by tauto.
    rewrite (IHp1 H1) (IHp2 H2); reflexivity.
  - assert (H1 : ~ prob_logic_var_occurs_pterm y p1) by tauto.
    assert (H2 : ~ prob_logic_var_occurs_pterm y p2) by tauto.
    rewrite (IHp1 H1) (IHp2 H2); reflexivity.
Qed.

Lemma subst_prob_pformula_fresh y replacement eta :
  ~ prob_logic_var_occurs_pformula y eta -> subst_prob_pformula y replacement eta = eta.
Proof.
  induction eta; cbn [prob_logic_var_occurs_pformula subst_prob_pformula]; intros H.
  - assert (H1 : ~ prob_logic_var_occurs_pterm y p1) by tauto.
    assert (H2 : ~ prob_logic_var_occurs_pterm y p2) by tauto.
    rewrite (subst_prob_pterm_fresh y replacement p1 H1)
      (subst_prob_pterm_fresh y replacement p2 H2); reflexivity.
  - reflexivity.
  - assert (H1 : ~ prob_logic_var_occurs_pformula y eta1) by tauto.
    assert (H2 : ~ prob_logic_var_occurs_pformula y eta2) by tauto.
    rewrite (IHeta1 H1) (IHeta2 H2); reflexivity.
Qed.

(** Cmd does not inspect rho. Changing the entire assignment leaves the
    output measure identical, not merely equivalent on measurable events. *)
Lemma run_measure_external_independent c mu rho sigma :
  pstate_measure (CommandSemantics.run c
    {| pstate_measure := mu; pstate_prob_logic_values := rho |}) =
  pstate_measure (CommandSemantics.run c
    {| pstate_measure := mu; pstate_prob_logic_values := sigma |}).
Proof. reflexivity. Qed.

(** A frozen value is transported unchanged through execution, including
    loops and commands that lose mass; it is never recomputed at the output. *)
Lemma run_update_prob_state c ps y value :
  CommandSemantics.run c (update_prob_state ps y value) =
  update_prob_state (CommandSemantics.run c ps) y value.
Proof. reflexivity. Qed.

Lemma run_update_prob_value c ps y value :
  pstate_prob_logic_values (CommandSemantics.run c (update_prob_state ps y value)) y = value.
Proof. apply update_prob_assignment_here. Qed.
