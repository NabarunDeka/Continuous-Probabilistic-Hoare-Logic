(** Finite matrix action on the existing nat-indexed certificate vectors.
    Only indices below m matter; no choice of a new index enumeration is needed. *)
From Stdlib Require Import Reals Lra Lia.
Require Import CPHL Soundness.FiniteExpectationBounds Soundness.RegionMeasureFacts.
Open Scope R_scope.

Definition matrix_apply m (a : nat -> nat -> R) (x : nat -> R) i :=
  finite_r_sum m (fun j => a i j * x j).
Fixpoint matrix_power_apply m a n (x : nat -> R) : nat -> R :=
  match n with
  | O => x
  | S n' => matrix_apply m a (matrix_power_apply m a n' x)
  end.
Definition matrix_nonnegative m (a : nat -> nat -> R) :=
  forall i j, (i < m)%nat -> (j < m)%nat -> 0 <= a i j.
Definition matrix_substochastic m (a : nat -> nat -> R) :=
  matrix_nonnegative m a /\ forall i, (i < m)%nat -> finite_r_sum m (a i) <= 1.
Definition matrix_deficit_progress m (a : nat -> nat -> R) :=
  forall i, (i < m)%nat ->
  0 < 1 - finite_r_sum m (a i) \/
  exists j, (j < i)%nat /\ 0 < a i j.

(** These algebraic identities use finite sums of real numbers only. *)
Lemma finite_r_sum_add m f h :
  finite_r_sum m (fun i => f i + h i) = finite_r_sum m f + finite_r_sum m h.
Proof. induction m; cbn [finite_r_sum]; [ring|rewrite IHm; ring]. Qed.
Lemma finite_r_sum_scale m c f :
  finite_r_sum m (fun i => c * f i) = c * finite_r_sum m f.
Proof. induction m; cbn [finite_r_sum]; [ring|rewrite IHm; ring]. Qed.
Lemma finite_r_sum_sub m f h :
  finite_r_sum m (fun i => f i - h i) = finite_r_sum m f - finite_r_sum m h.
Proof. induction m; cbn [finite_r_sum]; [ring|rewrite IHm; ring]. Qed.

Lemma matrix_apply_ext m a x y i :
  (forall j, (j < m)%nat -> x j = y j) -> matrix_apply m a x i = matrix_apply m a y i.
Proof. intro h; apply finite_r_sum_ext; intros j hj; rewrite h by assumption; reflexivity. Qed.
Lemma matrix_apply_add m a x y i :
  matrix_apply m a (fun j => x j + y j) i = matrix_apply m a x i + matrix_apply m a y i.
Proof.
  unfold matrix_apply; rewrite <- finite_r_sum_add; apply finite_r_sum_ext; intros; ring.
Qed.
Lemma matrix_apply_scale m a c x i :
  matrix_apply m a (fun j => c * x j) i = c * matrix_apply m a x i.
Proof.
  unfold matrix_apply; rewrite <- finite_r_sum_scale; apply finite_r_sum_ext; intros; ring.
Qed.
Lemma matrix_apply_zero m a i : matrix_apply m a (fun _ => 0) i = 0.
Proof. apply finite_r_sum_zero; intros; ring. Qed.
Lemma matrix_apply_one m a i : matrix_apply m a (fun _ => 1) i = finite_r_sum m (a i).
Proof. apply finite_r_sum_ext; intros; ring. Qed.
Lemma matrix_apply_le m a x y : matrix_nonnegative m a ->
  (forall j, (j < m)%nat -> x j <= y j) ->
  forall i, (i < m)%nat -> matrix_apply m a x i <= matrix_apply m a y i.
Proof.
  intros ha hxy i hi; apply finite_r_sum_le; intros j hj.
  apply Rmult_le_compat_l; [apply ha|apply hxy]; assumption.
Qed.
Lemma matrix_apply_nonnegative m a x : matrix_nonnegative m a ->
  (forall j, (j < m)%nat -> 0 <= x j) ->
  forall i, (i < m)%nat -> 0 <= matrix_apply m a x i.
Proof.
  intros ha hx i hi; apply finite_r_sum_nonnegative; intros j hj.
  apply Rmult_le_pos; [apply ha|apply hx]; assumption.
Qed.

(** Iteration is A^n acting on a vector. The composition lemma lets us
    group powers into contraction blocks without introducing spectral theory. *)
Lemma matrix_power_ext m a n x y :
  (forall j, (j < m)%nat -> x j = y j) ->
  forall i, (i < m)%nat -> matrix_power_apply m a n x i = matrix_power_apply m a n y i.
Proof.
  intro h; induction n; intros i hi; cbn [matrix_power_apply]; [apply h|apply matrix_apply_ext]; auto.
Qed.
Lemma matrix_power_le m a n x y : matrix_nonnegative m a ->
  (forall j, (j < m)%nat -> x j <= y j) ->
  forall i, (i < m)%nat -> matrix_power_apply m a n x i <= matrix_power_apply m a n y i.
Proof.
  intros ha h; induction n; intros i hi; cbn [matrix_power_apply]; [apply h|apply matrix_apply_le]; auto.
Qed.
Lemma matrix_power_nonnegative m a n x : matrix_nonnegative m a ->
  (forall j, (j < m)%nat -> 0 <= x j) ->
  forall i, (i < m)%nat -> 0 <= matrix_power_apply m a n x i.
Proof.
  intros ha h; induction n; intros i hi; cbn [matrix_power_apply]; [apply h|apply matrix_apply_nonnegative]; auto.
Qed.
Lemma matrix_power_add m a n x y i :
  matrix_power_apply m a n (fun j => x j + y j) i =
  matrix_power_apply m a n x i + matrix_power_apply m a n y i.
Proof.
  revert i; induction n; intro i; cbn [matrix_power_apply]; first reflexivity.
  transitivity (matrix_apply m a (fun j => matrix_power_apply m a n x j + matrix_power_apply m a n y j) i).
  - apply matrix_apply_ext; intros; apply IHn.
  - apply matrix_apply_add.
Qed.
Lemma matrix_power_scale m a n c x i :
  matrix_power_apply m a n (fun j => c * x j) i = c * matrix_power_apply m a n x i.
Proof.
  revert i; induction n; intro i; cbn [matrix_power_apply]; first reflexivity.
  transitivity (matrix_apply m a (fun j => c * matrix_power_apply m a n x j) i).
  - apply matrix_apply_ext; intros; apply IHn.
  - apply matrix_apply_scale.
Qed.
Lemma matrix_power_add_steps m a n k x i :
  matrix_power_apply m a (n + k) x i =
  matrix_power_apply m a n (matrix_power_apply m a k x) i.
Proof.
  revert i; induction n; intro i; cbn [Nat.add matrix_power_apply]; first reflexivity.
  apply matrix_apply_ext; intros; apply IHn.
Qed.
Lemma matrix_power_commute m a n x i :
  matrix_power_apply m a n (matrix_apply m a x) i =
  matrix_apply m a (matrix_power_apply m a n x) i.
Proof.
  change (matrix_power_apply m a n (matrix_power_apply m a 1 x) i =
    matrix_power_apply m a (S n) x i).
  rewrite <- (matrix_power_add_steps m a n 1 x i), Nat.add_1_r; reflexivity.
Qed.

(** Finite reward iteration starts at zero. The next lemma identifies it
    with the usual partial sum sum_(k<n) A^k b. *)
Fixpoint matrix_rewards m a (b : nat -> R) n : nat -> R :=
  match n with O => fun _ => 0 | S n' => fun i => b i + matrix_apply m a (matrix_rewards m a b n') i end.
Lemma matrix_rewards_tail m a b n i :
  matrix_rewards m a b (S n) i = matrix_rewards m a b n i + matrix_power_apply m a n b i.
Proof.
  revert i; induction n; intro i; cbn [matrix_rewards matrix_power_apply].
  - rewrite matrix_apply_zero; ring.
  - transitivity (b i + matrix_apply m a (fun j => matrix_rewards m a b n j + matrix_power_apply m a n b j) i).
    + f_equal; apply matrix_apply_ext; intros; apply IHn.
    + rewrite matrix_apply_add; ring.
Qed.
Lemma matrix_rewards_sum m a b n i :
  matrix_rewards m a b n i = finite_r_sum n (fun k => matrix_power_apply m a k b i).
Proof.
  induction n; first reflexivity.
  rewrite matrix_rewards_tail, IHn; reflexivity.
Qed.

(** Repeated substitution into x <= A*x+b leaves exactly one residual
    A^n*x. No stochastic or progress premise is needed for this finite bound. *)
Lemma matrix_subsolution_residual m a b x : matrix_nonnegative m a ->
  (forall i, (i < m)%nat -> x i <= b i + matrix_apply m a x i) ->
  forall n i, (i < m)%nat -> x i <= matrix_rewards m a b n i + matrix_power_apply m a n x i.
Proof.
  intros ha hx n; induction n; intros i hi; cbn [matrix_rewards matrix_power_apply]; first lra.
  pose proof (matrix_apply_le m a x
    (fun j => matrix_rewards m a b n j + matrix_power_apply m a n x j) ha IHn i hi) as h.
  rewrite matrix_apply_add in h; specialize (hx i hi); lra.
Qed.
Lemma matrix_solution_residual m a b x :
  (forall i, (i < m)%nat -> x i = b i + matrix_apply m a x i) ->
  forall n i, (i < m)%nat -> x i = matrix_rewards m a b n i + matrix_power_apply m a n x i.
Proof.
  intros hx n; induction n; intros i hi; cbn [matrix_rewards matrix_power_apply]; first ring.
  pose proof (matrix_apply_ext m a x
    (fun j => matrix_rewards m a b n j + matrix_power_apply m a n x j) i IHn) as h.
  rewrite matrix_apply_add in h; rewrite hx by assumption; lra.
Qed.
