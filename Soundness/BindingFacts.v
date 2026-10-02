(** Local correctness of capture-avoiding Boolean substitution. Freshness
    includes nested binder names; alpha-renaming respects parameter scope. *)
From Stdlib Require Import Reals Lists.List Lia.
Require Import MeasureIntegration CPHL Soundness.StateFacts.
Import ListNotations.

(** The fresh name avoids every relevant source of capture, including an
    existing binder in the body and a real variable in the replacement. *)
Lemma bool_substitution_fresh_spec x d q beta :
  let z := fresh_real_program_var
    (x :: pconstruct_real_program_vars q ++ distribution_real_program_vars d ++
      cformula_real_program_vars beta) in
  z <> x /\ ~ In z (pconstruct_real_program_vars q) /\
  ~ In z (distribution_real_program_vars d) /\
  ~ In z (cformula_real_program_vars beta).
Proof.
  cbn zeta.
  set (z := fresh_real_program_var
    (x :: pconstruct_real_program_vars q ++ distribution_real_program_vars d ++
      cformula_real_program_vars beta)).
  assert (H : ~ In z (x :: pconstruct_real_program_vars q ++
    distribution_real_program_vars d ++ cformula_real_program_vars beta)).
  { apply fresh_real_program_var_not_in. }
  change (~ (x = z \/ In z (pconstruct_real_program_vars q ++
    distribution_real_program_vars d ++ cformula_real_program_vars beta))) in H.
  repeat rewrite in_app_iff in H.
  intuition congruence.
Qed.

(** Alpha-renaming changes names, never the number of construct nodes. This
    is the termination measure for recursive calls on a renamed body. *)
Lemma rename_bound_pconstruct_size old fresh q :
  pconstruct_size (rename_bound_pconstruct old fresh q) = pconstruct_size q.
Proof.
  induction q as [gamma | x d q IH]; cbn [rename_bound_pconstruct pconstruct_size].
  - reflexivity.
  - destruct (real_program_var_eq_dec x old); cbn [pconstruct_size]; congruence.
Qed.

Lemma subst_bool_pconstruct_fuel_size fuel b beta q :
  pconstruct_size (subst_bool_pconstruct_fuel fuel b beta q) = pconstruct_size q.
Proof.
  revert q; induction fuel as [|fuel IH]; intro q; [reflexivity|].
  destruct q as [gamma | x d q]; cbn [subst_bool_pconstruct_fuel pconstruct_size].
  - reflexivity.
  - destruct (in_dec real_program_var_eq_dec x (cformula_real_program_vars beta));
      cbn [pconstruct_size]; rewrite IH; try rewrite rename_bound_pconstruct_size;
      reflexivity.
Qed.

(** Sufficient fuel is observationally irrelevant even when each level
    renames its body. The zero-fuel fallback is never needed by the wrapper. *)
Lemma subst_bool_pconstruct_fuel_stable n m b beta q :
  (pconstruct_size q <= n)%nat -> (pconstruct_size q <= m)%nat ->
  subst_bool_pconstruct_fuel n b beta q = subst_bool_pconstruct_fuel m b beta q.
Proof.
  revert m q; induction n as [|n IH]; intros m q Hn Hm;
    destruct q as [gamma | x d q]; cbn [pconstruct_size] in Hn; try lia;
    destruct m as [|m]; cbn [pconstruct_size] in Hm; try lia;
    cbn [subst_bool_pconstruct_fuel]; try reflexivity.
  destruct (in_dec real_program_var_eq_dec x (cformula_real_program_vars beta));
    f_equal; apply IH; try rewrite rename_bound_pconstruct_size; lia.
Qed.

Lemma subst_bool_pconstruct_sufficient fuel b beta q :
  (pconstruct_size q <= fuel)%nat ->
  subst_bool_pconstruct_fuel fuel b beta q = subst_bool_pconstruct b beta q.
Proof.
  intro H; unfold subst_bool_pconstruct.
  apply subst_bool_pconstruct_fuel_stable; lia.
Qed.

(** The unchanged real-substitution and conditioning algorithms use the
    same size argument. These facts verify fuel sufficiency, not their full
    semantic substitution/conditioning theorems. *)
Lemma subst_real_pconstruct_fuel_stable n m x t q :
  (pconstruct_size q <= n)%nat -> (pconstruct_size q <= m)%nat ->
  subst_real_pconstruct_fuel n x t q = subst_real_pconstruct_fuel m x t q.
Proof.
  revert m q; induction n as [|n IH]; intros m q Hn Hm;
    destruct q as [gamma | y d q]; cbn [pconstruct_size] in Hn; try lia;
    destruct m as [|m]; cbn [pconstruct_size] in Hm; try lia;
    cbn [subst_real_pconstruct_fuel]; try reflexivity.
  destruct (real_program_var_eq_dec y x); [reflexivity|].
  destruct (in_dec real_program_var_eq_dec y (term_real_program_vars t));
    f_equal; apply IH; try rewrite rename_bound_pconstruct_size; lia.
Qed.

Lemma condition_pconstruct_fuel_stable n m q gamma :
  (pconstruct_size q <= n)%nat -> (pconstruct_size q <= m)%nat ->
  condition_pconstruct_fuel n q gamma = condition_pconstruct_fuel m q gamma.
Proof.
  revert m q; induction n as [|n IH]; intros m q Hn Hm;
    destruct q as [beta | x d q]; cbn [pconstruct_size] in Hn; try lia;
    destruct m as [|m]; cbn [pconstruct_size] in Hm; try lia;
    cbn [condition_pconstruct_fuel]; try reflexivity.
  destruct (in_dec real_program_var_eq_dec x (cformula_real_program_vars gamma));
    f_equal; apply IH; try rewrite rename_bound_pconstruct_size; lia.
Qed.

Lemma subst_bool_pconstruct_indicator b beta gamma :
  subst_bool_pconstruct b beta (QIndicator gamma) =
  QIndicator (subst_bool_cformula b beta gamma).
Proof. reflexivity. Qed.

(** The public equation exposes the collision branch without exposing fuel.
    Distribution parameters remain untouched by Boolean substitution. *)
Lemma subst_bool_pconstruct_integral b beta x d q :
  subst_bool_pconstruct b beta (QIntegral x d q) =
  if in_dec real_program_var_eq_dec x (cformula_real_program_vars beta)
  then let fresh := fresh_real_program_var
    (x :: pconstruct_real_program_vars q ++ distribution_real_program_vars d ++
      cformula_real_program_vars beta) in
    QIntegral fresh d (subst_bool_pconstruct b beta (rename_bound_pconstruct x fresh q))
  else QIntegral x d (subst_bool_pconstruct b beta q).
Proof.
  unfold subst_bool_pconstruct at 1.
  cbn [pconstruct_size subst_bool_pconstruct_fuel].
  destruct (in_dec real_program_var_eq_dec x (cformula_real_program_vars beta));
    unfold subst_bool_pconstruct; rewrite ?rename_bound_pconstruct_size; reflexivity.
Qed.

(** Distributions depend on real terms only. Boolean updates cannot change
    their law; a fresh real update likewise leaves both parameters unchanged. *)
Lemma distribution_measure_update_bool d v b value :
  distribution_measure d (update_bool v b value) = distribution_measure d v.
Proof.
  destruct d as [a c | a c | a c];
    unfold distribution_measure, DistributionSemantics.real_law;
    rewrite !term_eval_update_bool; reflexivity.
Qed.

Lemma distribution_measure_update_real_fresh d v x r :
  ~ In x (distribution_real_program_vars d) ->
  distribution_measure d (update_real v x r) = distribution_measure d v.
Proof.
  destruct d as [a c | a c | a c];
    cbn [distribution_real_program_vars]; rewrite in_app_iff; intro H;
    unfold distribution_measure, DistributionSemantics.real_law;
    rewrite !term_eval_update_real_fresh by tauto; reflexivity.
Qed.

(** The all-occurrences list is deliberately stronger than free support:
    fresh names also avoid binders, making update commutation immediate. *)
Lemma q_eval_update_real_fresh q v x r :
  ~ In x (pconstruct_real_program_vars q) ->
  q_eval q (update_real v x r) = q_eval q v.
Proof.
  (** Use the semantic bridge at leaves; binder reasoning stays unchanged. *)
  revert v; induction q as [gamma | y d q IH]; intros v H.
  - cbn [q_eval]; rewrite !formula_indicatorE; apply real_indicator_extensional.
    apply satisfies_update_real_fresh; exact H.
  - cbn [pconstruct_real_program_vars] in H; cbn [In] in H; rewrite in_app_iff in H.
    cbn [q_eval].
    rewrite distribution_measure_update_real_fresh by tauto.
    apply ConcreteMeasure.expectation_ext; intro z.
    rewrite update_real_commute by intuition congruence.
    apply IH; tauto.
Qed.

(** Renaming a formula under a fresh binder reads the same old coordinate
    value. Classical logic maps and Boolean coordinates are unchanged. *)
Lemma term_eval_rename_fresh t old fresh v r :
  ~ In fresh (term_real_program_vars t) ->
  term_eval (rename_real_term old fresh t) (update_real v fresh r) =
  term_eval t (update_real v old r).
Proof.
  induction t as [y | y | c | t1 IH1 t2 IH2 | t1 IH1 t2 IH2];
    cbn [term_real_program_vars]; try rewrite in_app_iff; intro H;
    cbn [rename_real_term term_eval].
  - destruct (real_program_var_eq_dec y old) as [E | Hyo]; cbn [term_eval].
    + subst y; now rewrite !update_real_here.
    + assert (Hyf : y <> fresh) by (cbn [In] in H; intuition congruence).
      rewrite (update_real_other v fresh y r Hyf).
      rewrite (update_real_other v old y r Hyo).
      reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2 by tauto; reflexivity.
  - rewrite IH1, IH2 by tauto; reflexivity.
Qed.

Lemma satisfies_rename_fresh gamma old fresh v r :
  ~ In fresh (cformula_real_program_vars gamma) ->
  (satisfies (update_real v fresh r) (rename_real_cformula old fresh gamma) <->
   satisfies (update_real v old r) gamma).
Proof.
  induction gamma as [b | b | t1 t2 | | g1 IH1 g2 IH2];
    cbn [cformula_real_program_vars]; try rewrite in_app_iff; intro H;
    cbn [rename_real_cformula satisfies]; try reflexivity.
  - rewrite !term_eval_rename_fresh by tauto; reflexivity.
  - specialize (IH1 ltac:(tauto)); specialize (IH2 ltac:(tauto)); tauto.
Qed.

Lemma distribution_measure_rename_fresh d old fresh v r :
  ~ In fresh (distribution_real_program_vars d) ->
  distribution_measure (rename_real_distribution old fresh d) (update_real v fresh r) =
  distribution_measure d (update_real v old r).
Proof.
  destruct d as [a c | a c | a c];
    cbn [distribution_real_program_vars]; rewrite in_app_iff; intro H;
    unfold distribution_measure, DistributionSemantics.real_law;
    cbn [rename_real_distribution];
    rewrite !term_eval_rename_fresh by tauto; reflexivity.
Qed.

(** A shadowing binder still renames its distribution parameters, evaluated
    in the enclosing state, but stops renaming its own body. Both branches
    preserve evaluation; the non-shadowing branch commutes distinct updates. *)
Lemma rename_bound_pconstruct_eval q old fresh v r :
  old <> fresh -> ~ In fresh (pconstruct_real_program_vars q) ->
  q_eval (rename_bound_pconstruct old fresh q) (update_real v fresh r) =
  q_eval q (update_real v old r).
Proof.
  revert v r; induction q as [gamma | x d q IH]; intros v r Hne Hfresh.
  - cbn [rename_bound_pconstruct q_eval]; rewrite !formula_indicatorE; apply real_indicator_extensional.
    apply satisfies_rename_fresh; exact Hfresh.
  - cbn [pconstruct_real_program_vars] in Hfresh; cbn [In] in Hfresh.
    rewrite in_app_iff in Hfresh.
    cbn [rename_bound_pconstruct].
    destruct (real_program_var_eq_dec x old) as [-> | Hxo]; cbn [q_eval];
      rewrite distribution_measure_rename_fresh by tauto;
      apply ConcreteMeasure.expectation_ext; intro z.
    + rewrite update_real_shadow.
      rewrite update_real_commute by congruence.
      apply q_eval_update_real_fresh; tauto.
    + rewrite (update_real_commute v fresh x r z) by intuition congruence.
      rewrite (update_real_commute v old x r z) by congruence.
      apply IH; tauto.
Qed.

Lemma integral_alpha_rename x fresh d q v :
  x <> fresh -> ~ In fresh (pconstruct_real_program_vars q) ->
  q_eval (QIntegral fresh d (rename_bound_pconstruct x fresh q)) v =
  q_eval (QIntegral x d q) v.
Proof.
  intros Hne Hfresh; cbn [q_eval]; apply ConcreteMeasure.expectation_ext.
  intro z; apply rename_bound_pconstruct_eval; assumption.
Qed.

(** Reifying a guard commutes with an update to an unmentioned real name.
    This prevents the replacement formula from seeing an integral's sample. *)
Lemma cformula_eval_bool_update_real_fresh beta v x r :
  ~ In x (cformula_real_program_vars beta) ->
  cformula_eval_bool beta (update_real v x r) = cformula_eval_bool beta v.
Proof.
  intro H; pose proof (satisfies_update_real_fresh beta v x r H) as Heq.
  (** Transfer semantic equivalence to Boolean equality through the public
      specification; no knowledge of the guard implementation is needed. *)
  apply Bool.eq_true_iff_eq.
  rewrite !CommandSemantics.cformula_eval_bool_spec; exact Heq.
Qed.

Lemma subst_bool_cformula_correct b beta gamma v :
  satisfies v (subst_bool_cformula b beta gamma) <->
  satisfies (update_bool v b (cformula_eval_bool beta v)) gamma.
Proof.
  induction gamma as [c | c | t1 t2 | | g1 IH1 g2 IH2];
    cbn [subst_bool_cformula satisfies].
  - destruct (bool_program_var_eq_dec c b) as [-> | Hcb]; cbn [satisfies].
    + (** The assigned bit represents exactly the replacement formula. *)
      rewrite update_bool_here; symmetry.
      apply CommandSemantics.cformula_eval_bool_spec.
    + rewrite update_bool_other by exact Hcb; reflexivity.
  - reflexivity.
  - now rewrite !term_eval_update_bool.
  - reflexivity.
  - tauto.
Qed.

(** This is the local repair theorem, before lifting substitution to terms,
    assertions, or Hoare rules. No admissibility or valid-parameter premise
    is needed: pointwise equal integrands use the same total sampling law. *)
Lemma subst_bool_pconstruct_fuel_correct fuel b beta q v :
  (pconstruct_size q <= fuel)%nat ->
  q_eval (subst_bool_pconstruct_fuel fuel b beta q) v =
  q_eval q (update_bool v b (cformula_eval_bool beta v)).
Proof.
  revert q v; induction fuel as [|fuel IH]; intros q v Hfuel;
    destruct q as [gamma | x d q]; cbn [pconstruct_size] in Hfuel; try lia.
  - cbn [subst_bool_pconstruct_fuel q_eval]; rewrite !formula_indicatorE; apply real_indicator_extensional.
    apply subst_bool_cformula_correct.
  - cbn [subst_bool_pconstruct_fuel].
    destruct (in_dec real_program_var_eq_dec x (cformula_real_program_vars beta))
      as [Hcapture | Hsafe].
    + pose proof (bool_substitution_fresh_spec x d q beta) as Hfresh.
      cbn zeta in Hfresh.
      cbn [q_eval]; rewrite distribution_measure_update_bool.
      apply ConcreteMeasure.expectation_ext; intro z.
      rewrite IH by (rewrite rename_bound_pconstruct_size; lia).
      rewrite cformula_eval_bool_update_real_fresh by tauto.
      rewrite update_real_bool_commute.
      apply rename_bound_pconstruct_eval; intuition congruence.
    + cbn [q_eval]; rewrite distribution_measure_update_bool.
      apply ConcreteMeasure.expectation_ext; intro z.
      rewrite IH by lia.
      rewrite cformula_eval_bool_update_real_fresh by exact Hsafe.
      now rewrite update_real_bool_commute.
Qed.

Theorem subst_bool_pconstruct_correct b beta q v :
  q_eval (subst_bool_pconstruct b beta q) v =
  q_eval q (update_bool v b (cformula_eval_bool beta v)).
Proof.
  unfold subst_bool_pconstruct; apply subst_bool_pconstruct_fuel_correct; lia.
Qed.
