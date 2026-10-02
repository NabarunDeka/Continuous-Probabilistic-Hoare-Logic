(** Algebraic state-update and finite-dependence facts. These concern the
    shared classical syntax; no measure or command semantics is assumed. *)
From Stdlib Require Import Reals Lists.List FunctionalExtensionality.
Require Import CPHL.
Import ValuationSpace ListNotations.

(** Record equality follows from agreement on all four coordinate families. *)
Lemma valuation_ext (v w : state) :
  (forall x, real_program_values v x = real_program_values w x) ->
  (forall b, bool_program_values v b = bool_program_values w b) ->
  (forall x, real_logic_values v x = real_logic_values w x) ->
  (forall b, bool_logic_values v b = bool_logic_values w b) -> v = w.
Proof.
  destruct v as [r b l k], w as [r' b' l' k']; simpl.
  intros Hr Hb Hl Hk; f_equal; apply functional_extensionality; assumption.
Qed.

(** Reading the assigned coordinate returns the new value; all other
    coordinates in the same program-variable family retain their old value. *)
Lemma update_real_here v x r : real_program_values (update_real v x r) x = r.
Proof.
  unfold update_real, update_real_values; simpl.
  destruct (real_program_var_eq_dec x x); congruence.
Qed.

Lemma update_real_other v x y r : y <> x ->
  real_program_values (update_real v x r) y = real_program_values v y.
Proof.
  intro H; unfold update_real, update_real_values; simpl.
  destruct (real_program_var_eq_dec y x); congruence.
Qed.

Lemma update_bool_here v b value :
  bool_program_values (update_bool v b value) b = value.
Proof.
  unfold update_bool, update_bool_values; simpl.
  destruct (bool_program_var_eq_dec b b); congruence.
Qed.

Lemma update_bool_other v b c value : c <> b ->
  bool_program_values (update_bool v b value) c = bool_program_values v c.
Proof.
  intro H; unfold update_bool, update_bool_values; simpl.
  destruct (bool_program_var_eq_dec c b); congruence.
Qed.

(** Logic maps are preserved as whole functions, even when the input measure
    will correlate them with program values. These are pointwise state facts. *)
Lemma real_update_preserves_rigid v x r :
  real_logic_values (update_real v x r) = real_logic_values v /\
  bool_logic_values (update_real v x r) = bool_logic_values v.
Proof. split; reflexivity. Qed.

Lemma bool_update_preserves_rigid v b value :
  real_logic_values (update_bool v b value) = real_logic_values v /\
  bool_logic_values (update_bool v b value) = bool_logic_values v.
Proof. split; reflexivity. Qed.

Lemma real_update_preserves_bools v x r :
  bool_program_values (update_real v x r) = bool_program_values v.
Proof. reflexivity. Qed.

Lemma bool_update_preserves_reals v b value :
  real_program_values (update_bool v b value) = real_program_values v.
Proof. reflexivity. Qed.

(** Updating with the existing value is the identity; repeated writes to one
    coordinate keep the last value. These equations support shadowing proofs. *)
Lemma update_real_self v x : update_real v x (real_program_values v x) = v.
Proof.
  apply valuation_ext; intro y; try reflexivity.
  unfold update_real, update_real_values; simpl.
  destruct (real_program_var_eq_dec y x); subst; reflexivity.
Qed.

Lemma update_bool_self v b : update_bool v b (bool_program_values v b) = v.
Proof.
  apply valuation_ext; intro c; try reflexivity.
  unfold update_bool, update_bool_values; simpl.
  destruct (bool_program_var_eq_dec c b); subst; reflexivity.
Qed.

Lemma update_real_shadow v x r s :
  update_real (update_real v x r) x s = update_real v x s.
Proof.
  apply valuation_ext; intro y; try reflexivity.
  unfold update_real, update_real_values; simpl.
  destruct (real_program_var_eq_dec y x); reflexivity.
Qed.

Lemma update_bool_shadow v b value next :
  update_bool (update_bool v b value) b next = update_bool v b next.
Proof.
  apply valuation_ext; intro c; try reflexivity.
  unfold update_bool, update_bool_values; simpl.
  destruct (bool_program_var_eq_dec c b); reflexivity.
Qed.

(** Distinct writes commute, including a real write with a Boolean write. *)
Lemma update_real_commute v x y r s : x <> y ->
  update_real (update_real v x r) y s = update_real (update_real v y s) x r.
Proof.
  intro H; apply valuation_ext; intro z; try reflexivity.
  unfold update_real, update_real_values; simpl.
  destruct (real_program_var_eq_dec z x), (real_program_var_eq_dec z y);
    subst; congruence.
Qed.

Lemma update_bool_commute v b c value next : b <> c ->
  update_bool (update_bool v b value) c next =
  update_bool (update_bool v c next) b value.
Proof.
  intro H; apply valuation_ext; intro z; try reflexivity.
  unfold update_bool, update_bool_values; simpl.
  destruct (bool_program_var_eq_dec z b), (bool_program_var_eq_dec z c);
    subst; congruence.
Qed.

Lemma update_real_bool_commute v x b r value :
  update_bool (update_real v x r) b value = update_real (update_bool v b value) x r.
Proof. reflexivity. Qed.

(** Exact occurrence lists for classical syntax include logic coordinates as
    well as program coordinates. Duplicates are harmless: membership, not
    multiplicity, is what the agreement lemmas use. Constructs with integral
    binders are deliberately left for the later binding/semantics tasks. *)
Fixpoint term_real_coordinates (t : Term) : list RealCoordinate :=
  match t with
  | TProgVar x => [inl x]
  | TLogicVar x => [inr x]
  | TConst _ => []
  | TAdd a b | TMul a b => term_real_coordinates a ++ term_real_coordinates b
  end.

Fixpoint cformula_real_coordinates (gamma : CFormula) : list RealCoordinate :=
  match gamma with
  | FProgBool _ | FLogicBool _ | FFalse => []
  | FLe a b => term_real_coordinates a ++ term_real_coordinates b
  | FImpl a b => cformula_real_coordinates a ++ cformula_real_coordinates b
  end.

Fixpoint cformula_bool_coordinates (gamma : CFormula) : list BoolCoordinate :=
  match gamma with
  | FProgBool b => [inl b]
  | FLogicBool b => [inr b]
  | FLe _ _ | FFalse => []
  | FImpl a b => cformula_bool_coordinates a ++ cformula_bool_coordinates b
  end.

(** A term observes only the finitely many real coordinates it mentions. *)
Lemma term_eval_agree t v w :
  (forall i, In i (term_real_coordinates t) ->
     real_coordinate i v = real_coordinate i w) ->
  term_eval t v = term_eval t w.
Proof.
  revert v w; induction t; intros v w H; simpl in *.
  - apply (H (inl x)); auto.
  - apply (H (inr x)); auto.
  - reflexivity.
  - f_equal.
    + apply IHt1; intros i Hi; apply H; apply in_or_app; auto.
    + apply IHt2; intros i Hi; apply H; apply in_or_app; auto.
  - f_equal.
    + apply IHt1; intros i Hi; apply H; apply in_or_app; auto.
    + apply IHt2; intros i Hi; apply H; apply in_or_app; auto.
Qed.

(** Satisfaction likewise needs agreement only on the formula's finite real
    and Boolean occurrence lists, rather than on all coordinates of a state. *)
Lemma satisfies_agree gamma v w :
  (forall i, In i (cformula_real_coordinates gamma) ->
     real_coordinate i v = real_coordinate i w) ->
  (forall i, In i (cformula_bool_coordinates gamma) ->
     bool_coordinate i v = bool_coordinate i w) ->
  (satisfies v gamma <-> satisfies w gamma).
Proof.
  revert v w; induction gamma; intros v w Hr Hb; simpl in *.
  - specialize (Hb (inl b) (or_introl eq_refl)); simpl in Hb.
    rewrite Hb; reflexivity.
  - specialize (Hb (inr b) (or_introl eq_refl)); simpl in Hb.
    rewrite Hb; reflexivity.
  - assert (H1 : term_eval t1 v = term_eval t1 w).
    { apply term_eval_agree; intros i Hi; apply Hr; apply in_or_app; auto. }
    assert (H2 : term_eval t2 v = term_eval t2 w).
    { apply term_eval_agree; intros i Hi; apply Hr; apply in_or_app; auto. }
    now rewrite H1, H2.
  - reflexivity.
  - assert (H1 : satisfies v gamma1 <-> satisfies w gamma1).
    { apply IHgamma1; intros i Hi; [apply Hr | apply Hb]; apply in_or_app; auto. }
    assert (H2 : satisfies v gamma2 <-> satisfies w gamma2).
    { apply IHgamma2; intros i Hi; [apply Hr | apply Hb]; apply in_or_app; auto. }
    tauto.
Qed.

(** Relate the new complete coordinate lists to the existing program-real
    occurrence lists used for fresh-name selection in CPHL. *)
Lemma term_program_coordinate_occurs t x :
  In (inl x) (term_real_coordinates t) <-> In x (term_real_program_vars t).
Proof.
  induction t; simpl; repeat rewrite in_app_iff; intuition congruence.
Qed.

Lemma cformula_program_coordinate_occurs gamma x :
  In (inl x) (cformula_real_coordinates gamma) <->
  In x (cformula_real_program_vars gamma).
Proof.
  induction gamma; simpl; repeat rewrite in_app_iff;
    try rewrite !term_program_coordinate_occurs; intuition congruence.
Qed.

(** A fresh real update cannot change evaluation. This is the local fact
    needed when a later alpha-renaming proof moves under an integral binder. *)
Lemma term_eval_update_real_fresh t v x r :
  ~ In x (term_real_program_vars t) ->
  term_eval t (update_real v x r) = term_eval t v.
Proof.
  intro H; apply term_eval_agree; intros [y | y] Hy; simpl.
  - apply update_real_other; intro E; subst y; apply H.
    apply (proj1 (term_program_coordinate_occurs t x)); exact Hy.
  - reflexivity.
Qed.

Lemma term_eval_update_bool t v b value :
  term_eval t (update_bool v b value) = term_eval t v.
Proof.
  apply term_eval_agree; intros [x | x] Hx; reflexivity.
Qed.

Lemma satisfies_update_real_fresh gamma v x r :
  ~ In x (cformula_real_program_vars gamma) ->
  (satisfies (update_real v x r) gamma <-> satisfies v gamma).
Proof.
  intro H; apply satisfies_agree.
  - intros [y | y] Hy; simpl.
    + apply update_real_other; intro E; subst y; apply H.
      apply (proj1 (cformula_program_coordinate_occurs gamma x)); exact Hy.
    + reflexivity.
  - intros [b | b] Hb; reflexivity.
Qed.

Lemma satisfies_update_bool_fresh gamma v b value :
  ~ In (inl b) (cformula_bool_coordinates gamma) ->
  (satisfies (update_bool v b value) gamma <-> satisfies v gamma).
Proof.
  intro H; apply satisfies_agree.
  - intros [x | x] Hx; reflexivity.
  - intros [c | c] Hc; simpl.
    + apply update_bool_other; intro E; subst c; contradiction.
    + reflexivity.
Qed.
