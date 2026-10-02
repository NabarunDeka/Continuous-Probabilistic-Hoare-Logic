(** Compatibility between elementary real-sequence limits and the
    MathComp filters used by the command/loop expectation layer. *)
From Stdlib Require Import Reals.
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals topology normedtype sequences.
From mathcomp Require Import Rstruct Rstruct_topology.
Require Import CPHL Soundness.FiniteMatrix Soundness.MatrixDecay.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma real_sequence_cvg (u : nat -> real) (l : real) :
  Un_cv u l <-> u @ \oo --> l.
Proof.
  split.
  - move=> hu; apply/(@cvgrPdist_lt real real^o) => eps /RltP heps.
    have [N hN] := hu eps heps.
    exists N; first exact I.
    move=> n hn; have h := hN n (elimT ssrnat.leP hn).
    move: h; rewrite RdistE distrC; move=> /RltP h; exact h.
  - move/(@cvgrPdist_lt real real^o) => h eps heps.
    have epos : (0 < eps)%R by exact/RltP.
    have [N _ hN] := h eps epos.
    exists N; move=> n hn; apply/RltP.
    rewrite RdistE distrC; apply hN; exact/ssrnat.leP.
Qed.

Corollary matrix_survival_cvg m a : matrix_substochastic m a ->
  matrix_deficit_progress m a -> forall i, Nat.lt i m ->
  (fun n => matrix_survival m a n i) @ \oo --> R0.
Proof.
  move=> hs hp i hi; apply/(proj1 (real_sequence_cvg _ _)).
  exact (matrix_survival_tends_zero m a hs hp i hi).
Qed.
Corollary matrix_residual_cvg m a x : matrix_substochastic m a ->
  matrix_deficit_progress m a ->
  (forall i, Nat.lt i m -> Rle R0 (x i) /\ Rle (x i) R1) ->
  forall i, Nat.lt i m -> (fun n => matrix_power_apply m a n x i) @ \oo --> R0.
Proof.
  move=> hs hp hx i hi; apply/(proj1 (real_sequence_cvg _ _)).
  exact (matrix_residual_tends_zero m a x hs hp hx i hi).
Qed.

(** Accept the same convergence notion as loop_reward_approx_cvg. Only
    real rewards pass through this interface, never arbitrary assertions. *)
Corollary matrix_subsolution_cvg_at m a b x i rewards limit :
  matrix_substochastic m a -> matrix_deficit_progress m a ->
  (forall j, Nat.lt j m -> Rle R0 (x j) /\ Rle (x j) R1) ->
  (forall j, Nat.lt j m -> Rle (x j) (Rplus (b j) (matrix_apply m a x j))) ->
  Nat.lt i m ->
  (forall n, Rle (matrix_rewards m a b n i) (rewards n)) ->
  rewards @ \oo --> limit -> Rle (x i) limit.
Proof.
  move=> hs hp hx hsub hi hr hl.
  apply (matrix_subsolution_limit_at m a b x i rewards limit hs hp hx hsub hi hr).
  exact (proj2 (real_sequence_cvg rewards limit) hl).
Qed.
