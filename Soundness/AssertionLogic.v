(** Assertion metatheory for the soundness proof. These lemmas concern the
    concrete interpretation of formulas, not derivability in an EPPL calculus
    or soundness of a Hoare rule. *)
From Stdlib Require Import Reals Lra.
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals topology ereal measure.
From mathcomp Require Import lebesgue_integral lebesgue_stieltjes_measure Rstruct Rstruct_topology.
Require Import MeasureIntegration CPHL Soundness.AssertionFacts Soundness.TransformerFacts.

Import numFieldTopology.Exports MeasurableR ValuationSpace.
Open Scope R_scope.

(** Derived connectives use implication and false in the syntax. These
    equivalences expose their ordinary classical meanings to later proofs. *)
Lemma psatisfies_true ps : psatisfies ps p_true.
Proof. cbn [p_true psatisfies]; tauto. Qed.

Lemma psatisfies_false ps : ~ psatisfies ps PFFalse.
Proof. cbn [psatisfies]; tauto. Qed.

Lemma psatisfies_le ps p q :
  psatisfies ps (PFLe p q) <-> pterm_eval p ps <= pterm_eval q ps.
Proof. reflexivity. Qed.

Lemma psatisfies_impl ps eta xi :
  psatisfies ps (PFImpl eta xi) <-> (psatisfies ps eta -> psatisfies ps xi).
Proof. reflexivity. Qed.

Lemma psatisfies_not ps eta :
  psatisfies ps (p_not eta) <-> ~ psatisfies ps eta.
Proof. reflexivity. Qed.

Lemma psatisfies_and ps eta xi :
  psatisfies ps (p_and eta xi) <-> psatisfies ps eta /\ psatisfies ps xi.
Proof.
  (** The encoding is a double negation: discharge it using MathComp rather
      than allowing propositional automation to select Stdlib classic. *)
  change (~ (psatisfies ps eta -> ~ psatisfies ps xi) <->
    psatisfies ps eta /\ psatisfies ps xi).
  rewrite boolp.not_implyE boolp.not_notE; reflexivity.
Qed.

Lemma psatisfies_or ps eta xi :
  psatisfies ps (p_or eta xi) <-> psatisfies ps eta \/ psatisfies ps xi.
Proof.
  change ((~ psatisfies ps eta -> psatisfies ps xi) <->
    psatisfies ps eta \/ psatisfies ps xi).
  rewrite boolp.implyNp; reflexivity.
Qed.

Lemma psatisfies_iff ps eta xi :
  psatisfies ps (p_iff eta xi) <-> (psatisfies ps eta <-> psatisfies ps xi).
Proof. unfold p_iff; rewrite psatisfies_and; reflexivity. Qed.

Lemma psatisfies_eq ps p q :
  psatisfies ps (p_eq p q) <-> pterm_eval p ps = pterm_eval q ps.
Proof. cbn [p_eq p_and p_not psatisfies]; lra. Qed.

Lemma psatisfies_lt ps p q :
  psatisfies ps (p_lt p q) <-> pterm_eval p ps < pterm_eval q ps.
Proof. cbn [p_lt p_not psatisfies]; lra. Qed.

(** Almost-sure truth means concentration, including on a zero measure;
    it does not require probability one or normalization. *)
Lemma psatisfies_almost_sure ps gamma :
  psatisfies ps (p_almost_sure gamma) <->
  expectation (pstate_measure ps) (q_eval (QIndicator gamma)) =
    expectation (pstate_measure ps) (q_eval (QIndicator c_true)).
Proof. apply psatisfies_eq. Qed.

(** Measure equality is needed only on measurable events. Library measures
    may carry arbitrary values outside that interface, so record equality
    would impose an unnecessary condition. *)
Definition measure_equiv (mu nu : Measure) : Prop :=
  forall A, measurable A -> mu A = nu A.

Lemma measure_equiv_refl mu : measure_equiv mu mu.
Proof. intros A HA; reflexivity. Qed.

Lemma measure_equiv_sym mu nu : measure_equiv mu nu -> measure_equiv nu mu.
Proof. intros H A HA; symmetry; apply H; exact HA. Qed.

Lemma measure_equiv_trans mu nu xi :
  measure_equiv mu nu -> measure_equiv nu xi -> measure_equiv mu xi.
Proof. intros H1 H2 A HA; transitivity (nu A); [apply H1 | apply H2]; exact HA. Qed.

Lemma measure_equiv_subprob mu nu :
  measure_equiv mu nu -> (Subprob mu <-> Subprob nu).
Proof.
  intros H; unfold Subprob, ConcreteMeasure.Subprob.
  rewrite (H setT measurableT); reflexivity.
Qed.

(** This is extensionality of the total real integral, so it needs no
    admissibility assumption. Construct integrability on admissible states
    is already supplied by ConstructFacts and AssertionFacts. *)
Lemma expectation_measure_equiv mu nu f :
  measure_equiv mu nu -> expectation mu f = expectation nu f.
Proof.
  intros H; unfold expectation, ConcreteMeasure.expectation, Rintegral.
  f_equal; apply eq_measure_integral; intros A HA _; apply H; exact HA.
Qed.

Definition pstate_equiv (ps qs : Pstate) : Prop :=
  measure_equiv (pstate_measure ps) (pstate_measure qs) /\
  forall y, pstate_prob_logic_values ps y = pstate_prob_logic_values qs y.

Lemma pstate_equiv_refl ps : pstate_equiv ps ps.
Proof. split; [apply measure_equiv_refl | intro y; reflexivity]. Qed.

Lemma pstate_equiv_sym ps qs : pstate_equiv ps qs -> pstate_equiv qs ps.
Proof.
  intros [Hmu Hrho]; split.
  - apply measure_equiv_sym; exact Hmu.
  - intro y; symmetry; apply Hrho.
Qed.

Lemma pstate_equiv_trans ps qs rs :
  pstate_equiv ps qs -> pstate_equiv qs rs -> pstate_equiv ps rs.
Proof.
  intros [Hmu Hrho] [Hnu Hsigma]; split.
  - eapply measure_equiv_trans; eassumption.
  - intro y; transitivity (pstate_prob_logic_values qs y); auto.
Qed.

Lemma pstate_equiv_admissible ps qs :
  pstate_equiv ps qs -> (pstate_admissible ps <-> pstate_admissible qs).
Proof. intros [Hmu _]; apply measure_equiv_subprob; exact Hmu. Qed.

Lemma pterm_eval_equiv p ps qs :
  pstate_equiv ps qs -> pterm_eval p ps = pterm_eval p qs.
Proof.
  intros [Hmu Hrho]; induction p; cbn [pterm_eval].
  - apply Hrho.
  - reflexivity.
  - apply expectation_measure_equiv; exact Hmu.
  - rewrite IHp1 IHp2; reflexivity.
  - rewrite IHp1 IHp2; reflexivity.
Qed.

Lemma psatisfies_equiv eta ps qs :
  pstate_equiv ps qs -> (psatisfies ps eta <-> psatisfies qs eta).
Proof.
  intros H; induction eta; cbn [psatisfies].
  - rewrite (pterm_eval_equiv p1 ps qs H) (pterm_eval_equiv p2 ps qs H); reflexivity.
  - tauto.
  - tauto.
Qed.

(** Execution respects observable state equivalence for every command,
    including nested loops. This reuses the existing kernel transformer law. *)
Lemma run_pstate_equiv c ps qs : pstate_equiv ps qs ->
  pstate_equiv (CommandSemantics.run c ps) (CommandSemantics.run c qs).
Proof.
  intros [Hmu Hrho]; split.
  - intros A HA; apply transform_ext; [exact Hmu | exact HA].
  - exact Hrho.
Qed.

(** Analytical terms contain no expectations. The measures may therefore
    differ arbitrarily, even in total mass, provided rho agrees pointwise. *)
Lemma pterm_analytical_measure_independent p ps qs :
  pterm_analytical p ->
  (forall y, pstate_prob_logic_values ps y = pstate_prob_logic_values qs y) ->
  pterm_eval p ps = pterm_eval p qs.
Proof.
  induction p; cbn [pterm_analytical pterm_eval]; intros H Hrho.
  - apply Hrho.
  - reflexivity.
  - contradiction.
  - destruct H as [H1 H2]; rewrite (IHp1 H1 Hrho) (IHp2 H2 Hrho); reflexivity.
  - destruct H as [H1 H2]; rewrite (IHp1 H1 Hrho) (IHp2 H2 Hrho); reflexivity.
Qed.

Lemma psatisfies_analytical_measure_independent eta ps qs :
  pformula_analytical eta ->
  (forall y, pstate_prob_logic_values ps y = pstate_prob_logic_values qs y) ->
  (psatisfies ps eta <-> psatisfies qs eta).
Proof.
  induction eta; cbn [pformula_analytical psatisfies]; intros H Hrho.
  - destruct H as [H1 H2].
    rewrite (pterm_analytical_measure_independent p1 ps qs H1 Hrho)
      (pterm_analytical_measure_independent p2 ps qs H2 Hrho); reflexivity.
  - tauto.
  - destruct H as [H1 H2].
    pose proof (IHeta1 H1 Hrho); pose proof (IHeta2 H2 Hrho); tauto.
Qed.
