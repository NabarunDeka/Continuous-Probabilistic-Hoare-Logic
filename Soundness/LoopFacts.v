(** Finite exits, forward measure iteration, and the least loop solution.
    All equalities of measures are stated on measurable events. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum interval_inference.
From mathcomp Require Import boolp classical_sets functions reals topology.
From mathcomp Require Import ereal normedtype sequences esum measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_integral.
From mathcomp Require Import lebesgue_stieltjes_measure kernel Rstruct Rstruct_topology.
Require Import MeasureIntegration DistributionKernels CPHL Soundness.CommandFacts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports MeasurableR ValuationSpace CommandSemantics.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Partial sums converge in extended reals, before projecting finite
    expectations back to ordinary reals. Countable additivity and kernel
    measurability are supplied by the library's bundled kseries. *)
Lemma loop_event g k v A : loop g k v A = \sum_(n <oo) loop_exit g k n v A.
Proof. reflexivity. Qed.
Lemma loop_measurable g k A : measurable A ->
  measurable_fun [set: Valuation] (loop g k ^~ A).
Proof. exact: measurable_kernel. Qed.
Lemma loop_approx_increasing g k v A : measurable A ->
  nondecreasing_seq (fun n => loop_approx g k n v A).
Proof.
move=> mA; apply/nondecreasing_seqP => n.
rewrite !loop_approx_sum// [leRHS]big_ord_recr.
by apply: leeDl; exact: measure_ge0.
Qed.
Lemma loop_approx_cvg g k v A : measurable A ->
  (fun n => loop_approx g k n v A) @ \oo --> loop g k v A.
Proof.
move=> mA; rewrite loop_event.
have -> : (fun n => loop_approx g k n v A) =
    (fun n => \sum_(0 <= i < n.+1) loop_exit g k i v A).
  by apply/funext => n; rewrite loop_approx_sum// big_mkord.
have hc := is_cvg_ereal_nneg_natsum (m:=0%N)
  (fun i _ => measure_ge0 (loop_exit g k i v) A).
rewrite -cvg_shiftS in hc; exact: hc.
Qed.
Lemma loop_approx_le g k n v A : measurable A ->
  loop_approx g k n v A <= loop g k v A.
Proof.
move=> mA; rewrite loop_approx_sum// loop_event.
have -> : (\sum_(i < n.+1) loop_exit g k i v A) =
    \sum_(0 <= i < n.+1) loop_exit g k i v A by rewrite big_mkord.
by apply: nneseries_lim_ge => i _ _; exact: measure_ge0.
Qed.

(** Splitting off the first exit and moving the remaining nonnegative sum
    through body integration gives the actual unfolding equation. *)
Lemma loop_unfold g k v A : measurable A ->
  loop g k v A = if cformula_eval_bool g v
    then \int[k v]_w loop g k w A else dirac v A.
Proof.
move=> mA; rewrite loop_event (nneseries_split 0%N 1%N)// add0n big_nat1.
rewrite -(@nneseries_addn real (fun n => loop_exit g k n v A) 1%N)//.
under eq_eseriesr do rewrite addn1 loop_exitS.
rewrite loop_exit0; case hg: (cformula_eval_bool g v).
- rewrite add0e; under [RHS]eq_integral do rewrite loop_event.
  rewrite integral_nneseries//; by move=> n; exact: measurable_kernel.
- by rewrite eseries0// adde0.
Qed.

(** Leastness is deliberately stated for any nonnegative measurable kernel,
    without assuming that a competing solution is subprobabilistic. A
    pre-fixed point suffices; every fixed point is therefore above the loop. *)
Lemma loop_least g (k : Kernel) (h : real.-ker Valuation ~> Valuation) :
  (forall (v : Valuation) (A : set Valuation), measurable A ->
    (if cformula_eval_bool g v then \int[k v]_w h w A else dirac v A) <= h v A) ->
  forall v A, measurable A -> loop g k v A <= h v A.
Proof.
move=> hh v A mA.
have ha n w : loop_approx g k n w A <= h w A.
  elim: n w => [w|n ih w].
  - rewrite /loop_approx loop_exit0.
    case hg: (cformula_eval_bool g w); first exact: measure_ge0.
    by move: (hh w A mA); rewrite hg.
  - rewrite loop_approxS; apply: le_trans (hh w A mA).
    case: (cformula_eval_bool g w) => //.
    apply: ge0_le_integral => //; try exact: measurable_kernel.
apply (cvge_to_le (@loop_approx_cvg g k v A mA)).
by apply: nearW => n; exact: ha.
Qed.

Lemma transform_zero_kernel mu A :
  transform [the real.-spker _ ~> _ of CommandSemantics.zero] mu A = 0.
Proof. by rewrite transform_event /CommandSemantics.zero /kzero /mzero integral0. Qed.
Lemma loop_input_subprob g k n mu : Subprob mu -> Subprob (loop_input g k n mu).
Proof.
move=> hm; elim: n => [|n ih] //=.
apply: transform_subprob; exact: ConcreteMeasure.restrict_subprob.
Qed.
Lemma loop_input_shift g k n mu :
  loop_input g k n.+1 mu = loop_input g k n (loop_step g k mu).
Proof. by elim: n => //= n ->. Qed.

(** Each exit kernel agrees with the corresponding forward exit measure.
    This includes non-entry (n=0), and allows the body to discard mass. *)
Lemma transform_loop_exit g k n mu A : Subprob mu -> measurable A ->
  transform (loop_exit g k n) mu A =
    ConcreteMeasure.restrict (loop_input g k n mu)
      (measurableC (measurable_formula_event g)) A.
Proof.
move=> hm mA; elim: n mu hm => [mu hm|n ih mu hm].
- change (transform [the real.-spker _ ~> _ of branch g
    [the real.-spker _ ~> _ of CommandSemantics.zero]
    [the real.-spker _ ~> _ of CommandSemantics.skip] ] mu A =
    ConcreteMeasure.restrict mu (measurableC (measurable_formula_event g)) A).
  by rewrite transform_branch// transform_zero_kernel add0e transform_skip.
- change (transform [the real.-spker _ ~> _ of branch g
    [the real.-spker _ ~> _ of sequence k (loop_exit g k n)]
    [the real.-spker _ ~> _ of CommandSemantics.zero] ] mu A =
    ConcreteMeasure.restrict (loop_input g k n.+1 mu)
      (measurableC (measurable_formula_event g)) A).
  have hmB : Subprob (ConcreteMeasure.restrict mu (measurable_formula_event g))
    by exact: ConcreteMeasure.restrict_subprob.
  have hstep : Subprob (loop_step g k mu) by exact: transform_subprob hmB.
  rewrite transform_branch// transform_zero_kernel adde0.
  rewrite (@transform_sequence k (loop_exit g k n) _ A hmB mA).
  by rewrite (ih _ hstep) loop_input_shift.
Qed.
Lemma transform_loop_approx g k n mu A : Subprob mu -> measurable A ->
  transform (loop_approx g k n) mu A = loop_output g k n mu A.
Proof.
move=> hm mA; rewrite transform_event.
under eq_integral do rewrite loop_approx_sum//.
rewrite ge0_integral_sum//; first by move=> i; exact: measurable_kernel.
rewrite /loop_output /msum; apply: eq_bigr => i _.
exact: transform_loop_exit.
Qed.
Lemma transform_loop_series g k mu A : Subprob mu -> measurable A ->
  transform [the real.-spker _ ~> _ of loop g k] mu A =
  \sum_(n <oo) ConcreteMeasure.restrict (loop_input g k n mu)
    (measurableC (measurable_formula_event g)) A.
Proof.
move=> hm mA; rewrite transform_event.
under eq_integral do rewrite loop_event.
rewrite integral_nneseries//; first by move=> n; exact: measurable_kernel.
apply: eq_eseriesr => n _; exact: transform_loop_exit.
Qed.

(** Exited mass plus the residual guarded mass never exceeds the initial
    mass. This is stronger than bounding output alone and records body loss. *)
Lemma loop_output_event g k n mu A : loop_output g k n mu A =
  \sum_(i < n.+1) loop_input g k i mu (A `&` ~` formula_event g).
Proof. reflexivity. Qed.
Lemma loop_output0 g k mu A : loop_output g k 0 mu A = mu (A `&` ~` formula_event g).
Proof. by rewrite loop_output_event big_ord1. Qed.
Lemma loop_outputS g k n mu A : loop_output g k n.+1 mu A =
  loop_output g k n mu A + loop_input g k n.+1 mu (A `&` ~` formula_event g).
Proof. by rewrite !loop_output_event [LHS]big_ord_recr. Qed.
Lemma guard_mass_partition g (mu : Measure) :
  mu (~` formula_event g) + mu (formula_event g) = mu setT.
Proof.
rewrite (ConcreteMeasure.event_partition mu measurableT (measurable_formula_event g)).
by rewrite setTI setTD addeC.
Qed.
Lemma loop_mass_accounting g k n mu :
  loop_output g k n mu setT + loop_input g k n mu (formula_event g) <= mu setT.
Proof.
elim: n => [|n ih].
- rewrite loop_output0 setTI.
  change (mu (~` formula_event g) + mu (formula_event g) <= mu setT).
  by rewrite guard_mass_partition.
- have step_bound : loop_input g k n.+1 mu setT <= loop_input g k n mu (formula_event g).
    have ht := transform_mass_nonincrease k
      (ConcreteMeasure.restrict (loop_input g k n mu) (measurable_formula_event g)).
    change (is_true (loop_input g k n.+1 mu setT <=
      loop_input g k n mu (setT `&` formula_event g))) in ht.
    by move: ht; rewrite setTI.
  rewrite loop_outputS setTI.
  rewrite -addeA guard_mass_partition.
  apply: le_trans ih; exact: leeD (lexx _) step_bound.
Qed.

Lemma loop_output_increasing g k mu A :
  nondecreasing_seq (fun n => loop_output g k n mu A).
Proof.
apply/nondecreasing_seqP => n.
change ((\sum_(i < n.+1) ConcreteMeasure.restrict (loop_input g k i mu)
  (measurableC (measurable_formula_event g)) A) <=
  \sum_(i < n.+2) ConcreteMeasure.restrict (loop_input g k i mu)
  (measurableC (measurable_formula_event g)) A).
rewrite [leRHS]big_ord_recr.
by apply: leeDl; exact: measure_ge0.
Qed.
Lemma loop_output_cvg g k mu A : Subprob mu -> measurable A ->
  (fun n => loop_output g k n mu A) @ \oo -->
    transform [the real.-spker _ ~> _ of loop g k] mu A.
Proof.
move=> hm mA; rewrite transform_loop_series// /loop_output /msum.
have -> : (fun n => \sum_(i < n.+1)
    ConcreteMeasure.restrict (loop_input g k i mu)
      (measurableC (measurable_formula_event g)) A) =
  (fun n => \sum_(0 <= i < n.+1)
    ConcreteMeasure.restrict (loop_input g k i mu)
      (measurableC (measurable_formula_event g)) A).
  by apply/funext => n; rewrite big_mkord.
have hc := is_cvg_ereal_nneg_natsum (m:=0%N) (fun i _ => measure_ge0
  (ConcreteMeasure.restrict (loop_input g k i mu)
    (measurableC (measurable_formula_event g))) A).
rewrite -cvg_shiftS in hc; exact: hc.
Qed.

(** Exit support concerns output states, independently of the truth of the
    guard in the input. In particular, it does not assert termination. *)
Lemma guard_mem g v : (v \in formula_event g) = cformula_eval_bool g v.
Proof.
apply/idP/idP.
- move/set_mem => h; apply/cformula_eval_bool_spec; exact: h.
- move/cformula_eval_bool_spec => h; exact: (mem_set (h : formula_event g v)).
Qed.
Lemma loop_exit_guard g k n v : loop_exit g k n v (formula_event g) = 0.
Proof.
elim: n v => [v|n ih v].
- rewrite loop_exit0 diracE guard_mem; by case: (cformula_eval_bool g v).
- rewrite loop_exitS; case: (cformula_eval_bool g v) => //.
  by apply: integral0_eq => w _; exact: ih.
Qed.
Lemma loop_guard g k v : loop g k v (formula_event g) = 0.
Proof. rewrite loop_event; by apply: eseries0 => n _ _; exact: loop_exit_guard. Qed.
Lemma transform_loop_guard g k mu :
  transform [the real.-spker _ ~> _ of loop g k] mu (formula_event g) = 0.
Proof. rewrite transform_event; by apply: integral0_eq => v _; exact: loop_guard. Qed.

Lemma loop_nonentry g k (v : Valuation) A : measurable A -> cformula_eval_bool g v = false ->
  loop g k v A = dirac v A.
Proof. by move=> mA hg; rewrite loop_unfold// hg. Qed.
Lemma loop_zero_body g v A : measurable A ->
  loop g [the real.-spker _ ~> _ of CommandSemantics.zero] v A =
    if cformula_eval_bool g v then 0 else dirac v A.
Proof.
move=> mA; rewrite loop_unfold//.
by rewrite /CommandSemantics.zero /kzero integral_measure_zero.
Qed.
Lemma loop_always_guard g k : (forall v, cformula_eval_bool g v = true) ->
  forall v A, loop g k v A = 0.
Proof.
move=> hg v A; rewrite loop_event; apply: eseries0 => n _ _.
elim: n v => [v|n ih v]; first by rewrite loop_exit0 hg.
rewrite loop_exitS hg; by apply: integral0_eq => w _; exact: ih.
Qed.

(** Compatibility keeps the existing non-loop interpreter and its proven
    equations usable without changing the syntax or proof-rule declarations. *)
Lemma denote_nonloop c k : nonloop_kernel c = Some k -> denote c = k.
Proof.
elim: c k => [|x t|b g|b r|x d|a IHa b IHb|g a IHa b IHb|g b IH] k /=;
  try by move=> [<-].
- case ha: (nonloop_kernel a) => [ka|] //.
  case hb: (nonloop_kernel b) => [kb|] // [<-].
  by rewrite (IHa _ ha) (IHb _ hb).
- case ha: (nonloop_kernel a) => [ka|] //.
  case hb: (nonloop_kernel b) => [kb|] // [<-].
  by rewrite (IHa _ ha) (IHb _ hb).
- by [].
Qed.

Lemma loop_countably_additive g k v : sigma_additive (loop g k v).
Proof. exact: measure_sigma_additive. Qed.
Lemma loop_integral_series g k v f : (forall w, 0 <= f w) ->
  measurable_fun [set: Valuation] f ->
  \int[loop g k v]_w f w = \sum_(n <oo) \int[loop_exit g k n v]_w f w.
Proof. exact: integral_kseries. Qed.
Lemma loop_fixed_point g k v A : measurable A ->
  loop g k v A = branch g
    [the real.-spker _ ~> _ of sequence k [the real.-spker _ ~> _ of loop g k] ]
    [the real.-spker _ ~> _ of CommandSemantics.skip] v A.
Proof.
move=> mA; rewrite loop_unfold//.
change ((if cformula_eval_bool g v then \int[k v]_w loop g k w A else dirac v A) =
  (if cformula_eval_bool g v then sequence k [the real.-spker _ ~> _ of loop g k] v
    else CommandSemantics.skip v) A).
by case: (cformula_eval_bool g v).
Qed.

(** A nonterminating body and an invalid sampler have the same loop effect
    when they both return the zero measure: only non-entering inputs survive. *)
Lemma loop_null_body g (k : Kernel) :
  (forall v A, measurable A -> k v A = 0) ->
  forall v A, measurable A -> loop g k v A =
    if cformula_eval_bool g v then 0 else dirac v A.
Proof.
move=> hk v A mA; rewrite loop_unfold//.
case: (cformula_eval_bool g v) => //.
rewrite (eq_measure_integral mzero); first by move=> B mB _; exact: hk.
exact: integral_measure_zero.
Qed.
Lemma loop_skip g v A : measurable A ->
  loop g [the real.-spker _ ~> _ of CommandSemantics.skip] v A =
    loop_exit g [the real.-spker _ ~> _ of CommandSemantics.skip] 0 v A.
Proof.
move=> mA; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: loop_least => // w B mB.
  rewrite /CommandSemantics.skip /kdirac integral_dirac ?diracT ?mul1e //;
    first exact: measurable_kernel.
  rewrite loop_exit0; by case: (cformula_eval_bool g w).
- exact: (@loop_approx_le g [the real.-spker _ ~> _ of CommandSemantics.skip] 0 v A mA).
Qed.
