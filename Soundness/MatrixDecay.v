(** Progress forces the finite substochastic matrix's surviving mass to
    vanish. The proof is elementary: decreasing indices, a finite uniform
    contraction, then geometric decay; no spectral-radius theorem is used. *)
From Stdlib Require Import Reals Lra Lia Arith.Wf_nat.
Require Import CPHL Soundness.FiniteExpectationBounds Soundness.RegionMeasureFacts
  Soundness.FiniteMatrix.
Open Scope R_scope.

Definition matrix_survival m a n := matrix_power_apply m a n (fun _ => 1).

Section Substochastic.
Context (m : nat) (a : nat -> nat -> R).
Hypothesis stochastic : matrix_substochastic m a.

Lemma matrix_survival_bounds n i : (i < m)%nat -> 0 <= matrix_survival m a n i <= 1.
Proof.
  intro hi; split.
  - apply matrix_power_nonnegative; [exact (proj1 stochastic)|intros; lra|exact hi].
  - revert i hi; induction n; intros i hi; cbn [matrix_survival matrix_power_apply]; first lra.
    eapply Rle_trans; first apply (matrix_apply_le m a _ (fun _ => 1) (proj1 stochastic) IHn i hi).
    rewrite matrix_apply_one; apply (proj2 stochastic); assumption.
Qed.

Lemma matrix_survival_step n i : (i < m)%nat ->
  matrix_survival m a (S n) i <= matrix_survival m a n i.
Proof.
  intro hi; unfold matrix_survival.
  change (matrix_apply m a (matrix_power_apply m a n (fun _ => 1)) i <=
    matrix_power_apply m a n (fun _ => 1) i).
  rewrite <- matrix_power_commute.
  apply matrix_power_le; [exact (proj1 stochastic)| |exact hi].
  intros j hj; rewrite matrix_apply_one; apply (proj2 stochastic); assumption.
Qed.
Lemma matrix_survival_antitone n k i : (n <= k)%nat -> (i < m)%nat ->
  matrix_survival m a k i <= matrix_survival m a n i.
Proof.
  intros hn hi; induction hn; first apply Rle_refl.
  eapply Rle_trans; [apply matrix_survival_step; exact hi|exact IHhn].
Qed.

(** A row loses mass either immediately, or via a successor which has
    already lost mass. Exit rewards need only bound the immediate deficit. *)
Lemma matrix_survival_deficit n i :
  1 - matrix_survival m a (S n) i =
  (1 - finite_r_sum m (a i)) +
  finite_r_sum m (fun j => a i j * (1 - matrix_survival m a n j)).
Proof.
  assert (he : finite_r_sum m (fun j => a i j * (1 - matrix_survival m a n j)) =
    finite_r_sum m (a i) - matrix_apply m a (matrix_survival m a n) i).
  { unfold matrix_apply; rewrite <- finite_r_sum_sub; apply finite_r_sum_ext; intros; ring. }
  rewrite he; unfold matrix_survival; cbn [matrix_power_apply]; ring.
Qed.

Lemma matrix_progress_strict : matrix_deficit_progress m a ->
  forall i, (i < m)%nat -> matrix_survival m a (S i) i < 1.
Proof.
  intros hp i; induction i using lt_wf_ind; intro hi.
  destruct (hp i hi) as [hd|[j [hj haj] ] ].
  - pose proof (matrix_survival_antitone 1 (S i) i ltac:(lia) hi) as hle.
    change (matrix_survival m a (S i) i <= matrix_apply m a (fun _ => 1) i) in hle.
    rewrite matrix_apply_one in hle; lra.
  - assert (hjm : (j < m)%nat) by lia.
    pose proof (H j hj hjm) as hstrict.
    pose proof (proj2 stochastic i hi) as hrow.
    pose proof (finite_r_sum_member_le m
      (fun k => a i k * (1 - matrix_survival m a (S j) k)) j hjm) as hterm.
    assert (hn : forall k, (k < m)%nat -> 0 <= a i k * (1 - matrix_survival m a (S j) k)).
    { intros k hk; pose proof (matrix_survival_bounds (S j) k hk).
      apply Rmult_le_pos; [apply (proj1 stochastic); assumption|lra]. }
    specialize (hterm hn).
    pose proof (matrix_survival_deficit (S j) i) as hdef.
    pose proof (matrix_survival_antitone (S (S j)) (S i) i ltac:(lia) hi) as hle.
    assert (0 < a i j * (1 - matrix_survival m a (S j) j)) by (apply Rmult_lt_0_compat; lra).
    lra.
Qed.
End Substochastic.

(** Finite rewards are nonnegative, and rewards plus surviving mass stay
    within one. This uses the reward budget, not equality with exit mass. *)
Theorem matrix_rewards_budget m a b : matrix_substochastic m a ->
  (forall i, (i < m)%nat -> 0 <= b i) ->
  (forall i, (i < m)%nat -> b i + finite_r_sum m (a i) <= 1) ->
  forall n i, (i < m)%nat ->
    0 <= matrix_rewards m a b n i /\
    matrix_rewards m a b n i + matrix_survival m a n i <= 1.
Proof.
  intros hs hb hbudget n; induction n; intros i hi.
  - cbn [matrix_rewards matrix_survival matrix_power_apply]; split; lra.
  - assert (hn : 0 <= matrix_apply m a (matrix_rewards m a b n) i).
    { apply matrix_apply_nonnegative; [exact (proj1 hs)|intros; apply IHn; assumption|exact hi]. }
    assert (hdom : forall j, (j < m)%nat ->
      matrix_rewards m a b n j + matrix_survival m a n j <= 1).
    { intros j hj; apply IHn; assumption. }
    pose proof (matrix_apply_le m a _ (fun _ => 1) (proj1 hs) hdom i hi) as h.
    rewrite matrix_apply_add, matrix_apply_one in h.
    specialize (hb i hi); specialize (hbudget i hi).
    cbn [matrix_rewards matrix_survival matrix_power_apply]; unfold matrix_survival in h; split; lra.
Qed.

Corollary matrix_rewards_bounds m a b : matrix_substochastic m a ->
  (forall i, (i < m)%nat -> 0 <= b i) ->
  (forall i, (i < m)%nat -> b i + finite_r_sum m (a i) <= 1) ->
  forall n i, (i < m)%nat -> 0 <= matrix_rewards m a b n i <= 1.
Proof.
  intros hs hb hr n i hi.
  pose proof (matrix_rewards_budget m a b hs hb hr n i hi).
  pose proof (matrix_survival_bounds m a hs n i hi); lra.
Qed.

(** A maximum over a finite set gives one contraction constant. For the
    empty index set choose zero; statements about a selected row are vacuous. *)
Lemma finite_uniform_lt_one m f :
  (forall i, (i < m)%nat -> 0 <= f i < 1) ->
  exists c, 0 <= c < 1 /\ forall i, (i < m)%nat -> f i <= c.
Proof.
  induction m; intro hf.
  - exists 0; split; [lra|intros; lia].
  - destruct (IHm ltac:(intros; apply hf; lia)) as [c [hc hb] ].
    pose proof (hf m ltac:(lia)) as hm.
    exists (Rmax c (f m)); split.
    + unfold Rmax; destruct (Rle_dec c (f m)); lra.
    + intros i hi; destruct (Nat.eq_dec i m) as [->|hne].
      * apply Rmax_r.
      * eapply Rle_trans; [apply hb; lia|apply Rmax_l].
Qed.

Theorem matrix_uniform_contraction m a : matrix_substochastic m a ->
  matrix_deficit_progress m a ->
  exists c, 0 <= c < 1 /\ forall i, (i < m)%nat -> matrix_survival m a m i <= c.
Proof.
  intros hs hp; apply finite_uniform_lt_one; intros i hi; split.
  - exact (proj1 (matrix_survival_bounds m a hs m i hi)).
  - eapply Rle_lt_trans.
    + apply (matrix_survival_antitone m a hs (S i) m i); lia.
    + apply (matrix_progress_strict m a hs hp i hi).
Qed.

(** Iterating the m-step contraction bounds every complete block. Monotone
    survival accounts for any remaining steps after the last complete block. *)
Theorem matrix_survival_blocks m a c : matrix_substochastic m a -> 0 <= c ->
  (forall i, (i < m)%nat -> matrix_survival m a m i <= c) ->
  forall k i, (i < m)%nat -> matrix_survival m a (k * m) i <= c ^ k.
Proof.
  intros hs hc hb k; induction k; intros i hi; cbn [Nat.mul pow]; first (unfold matrix_survival; cbn [matrix_power_apply]; lra).
  unfold matrix_survival; rewrite matrix_power_add_steps.
  eapply Rle_trans.
  - apply (matrix_power_le m a m _ (fun _ => c ^ k) (proj1 hs)); [exact IHk|exact hi].
  - assert (he : matrix_power_apply m a m (fun _ => c ^ k) i =
      c ^ k * matrix_survival m a m i).
    { transitivity (matrix_power_apply m a m (fun _ => c ^ k * 1) i).
      - apply matrix_power_ext; [intros; ring|exact hi].
      - apply matrix_power_scale. }
    rewrite he; pose proof (pow_le c k hc) as hp; specialize (hb i hi); nra.
Qed.

Theorem matrix_survival_geometric m a c : matrix_substochastic m a -> 0 <= c ->
  (forall i, (i < m)%nat -> matrix_survival m a m i <= c) ->
  forall n i, (i < m)%nat -> matrix_survival m a n i <= c ^ (n / m).
Proof.
  intros hs hc hb n i hi; assert (hm : (0 < m)%nat) by lia.
  eapply Rle_trans.
  - apply (matrix_survival_antitone m a hs ((n / m) * m) n i); [|exact hi].
    pose proof (Nat.div_mod n m ltac:(lia)); nia.
  - apply matrix_survival_blocks; assumption.
Qed.

Theorem matrix_survival_tends_zero m a : matrix_substochastic m a ->
  matrix_deficit_progress m a -> forall i, (i < m)%nat ->
  Un_cv (fun n => matrix_survival m a n i) 0.
Proof.
  intros hs hp i hi.
  destruct (matrix_uniform_contraction m a hs hp) as [c [hc hb] ].
  intros eps heps.
  assert (hab : Rabs c < 1) by (rewrite Rabs_pos_eq by lra; lra).
  destruct (pow_lt_1_zero c hab eps heps) as [k hk].
  exists (k * m)%nat; intros n hn.
  pose proof (matrix_survival_antitone m a hs (k * m) n i hn hi) as hmono.
  pose proof (matrix_survival_blocks m a c hs (proj1 hc) hb k i hi) as hbnd.
  pose proof (proj1 (matrix_survival_bounds m a hs n i hi)) as hzero.
  specialize (hk k (Nat.le_refl k)).
  unfold Rdist; rewrite Rminus_0_r, Rabs_pos_eq by assumption.
  pose proof (Rle_abs (c ^ k)); lra.
Qed.

(** Bounded nonnegative residual vectors vanish by comparison with A^n*1. *)
Theorem matrix_residual_tends_zero m a x : matrix_substochastic m a ->
  matrix_deficit_progress m a -> (forall i, (i < m)%nat -> 0 <= x i <= 1) ->
  forall i, (i < m)%nat -> Un_cv (fun n => matrix_power_apply m a n x i) 0.
Proof.
  intros hs hp hx i hi eps heps.
  destruct (matrix_survival_tends_zero m a hs hp i hi eps heps) as [N hN].
  exists N; intros n hn.
  pose proof (matrix_power_nonnegative m a n x (proj1 hs) ltac:(intros; apply hx; assumption) i hi) as h0.
  pose proof (matrix_power_le m a n x (fun _ => 1) (proj1 hs) ltac:(intros; apply hx; assumption) i hi) as h1.
  specialize (hN n hn); unfold Rdist in *.
  rewrite Rminus_0_r, Rabs_pos_eq in hN by (apply matrix_survival_bounds; assumption).
  rewrite Rminus_0_r, Rabs_pos_eq by assumption; exact (Rle_lt_trans _ _ _ h1 hN).
Qed.

(** Any convergent finite-reward upper envelope dominates the proposed
    subsolution in the limit. This is the comparison interface for task 11. *)
Theorem matrix_subsolution_limit_at m a b x i rewards limit :
  matrix_substochastic m a -> matrix_deficit_progress m a ->
  (forall i, (i < m)%nat -> 0 <= x i <= 1) ->
  (forall i, (i < m)%nat -> x i <= b i + matrix_apply m a x i) ->
  (i < m)%nat ->
  (forall n, matrix_rewards m a b n i <= rewards n) ->
  Un_cv rewards limit -> x i <= limit.
Proof.
  intros hs hp hx hsub hi hrew hlim.
  apply Rnot_lt_le; intro hbad.
  set (eps := (x i - limit) / 3).
  assert (heps : 0 < eps) by (unfold eps; lra).
  destruct (matrix_residual_tends_zero m a x hs hp hx i hi eps heps) as [N hN].
  destruct (hlim eps heps) as [M hM].
  specialize (hN (Nat.max N M) (Nat.le_max_l N M)).
  specialize (hM (Nat.max N M) (Nat.le_max_r N M)).
  pose proof (matrix_subsolution_residual m a b x (proj1 hs) hsub (Nat.max N M) i hi) as h.
  specialize (hrew (Nat.max N M)).
  unfold Rdist in hN, hM.
  pose proof (Rle_abs (matrix_power_apply m a (Nat.max N M) x i - 0)).
  pose proof (Rle_abs (rewards (Nat.max N M) - limit)).
  unfold eps in *; lra.
Qed.

Corollary matrix_subsolution_limit m a b x rewards limit :
  matrix_substochastic m a -> matrix_deficit_progress m a ->
  (forall i, (i < m)%nat -> 0 <= x i <= 1) ->
  (forall i, (i < m)%nat -> x i <= b i + matrix_apply m a x i) ->
  (forall n i, (i < m)%nat -> matrix_rewards m a b n i <= rewards n i) ->
  (forall i, (i < m)%nat -> Un_cv (fun n => rewards n i) (limit i)) ->
  forall i, (i < m)%nat -> x i <= limit i.
Proof.
  intros hs hp hx hsub hrew hlim i hi.
  apply (matrix_subsolution_limit_at m a b x i (fun n => rewards n i) (limit i)); auto.
Qed.

(** For an exact bounded solution the residual identity identifies the
    reward-series limit. This is a finite-system theorem, independent of Cmd. *)
Theorem matrix_solution_reward_limit m a b x :
  matrix_substochastic m a -> matrix_deficit_progress m a ->
  (forall i, (i < m)%nat -> 0 <= x i <= 1) ->
  (forall i, (i < m)%nat -> x i = b i + matrix_apply m a x i) ->
  forall i, (i < m)%nat -> Un_cv (fun n => matrix_rewards m a b n i) (x i).
Proof.
  intros hs hp hx heq i hi eps heps.
  destruct (matrix_residual_tends_zero m a x hs hp hx i hi eps heps) as [N hN].
  exists N; intros n hn; specialize (hN n hn).
  pose proof (matrix_solution_residual m a b x heq n i hi) as he.
  unfold Rdist in *; rewrite Rminus_0_r in hN.
  replace (matrix_rewards m a b n i - x i) with (- matrix_power_apply m a n x i) by lra.
  rewrite Rabs_Ropp; exact hN.
Qed.
