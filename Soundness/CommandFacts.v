(** Non-loop command equations and rigidity. Equality of measures is stated
    on measurable events, the interface needed by the soundness proof. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum interval_inference.
From mathcomp Require Import boolp classical_sets functions reals topology.
From mathcomp Require Import ereal normedtype sequences esum measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_integral.
From mathcomp Require Import lebesgue_stieltjes_measure kernel Rstruct Rstruct_topology.
From mathcomp Require Import bernoulli_distribution.
Require Import MeasureIntegration DistributionKernels CPHL Soundness.ConstructFacts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports MeasurableR ValuationSpace CommandSemantics.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Lemma transform_event k mu A : transform k mu A = \int[mu]_v k v A.
Proof. reflexivity. Qed.

(** The type of a command kernel already supplies its pointwise mass bound.
    Neither the input measure nor Pstate stores an admissibility certificate. *)
Lemma transform_mass_nonincrease k mu : transform k mu setT <= mu setT.
Proof.
rewrite transform_event -[leRHS]mul1e -integral_cst//.
apply: ge0_le_integral => //.
- exact: measurable_kernel.
- by move=> v _; exact: sprob_kernel_le1.
Qed.
Lemma transform_subprob k mu : Subprob mu -> Subprob (transform k mu).
Proof. exact: le_trans (transform_mass_nonincrease k mu). Qed.
Lemma transform_pstate_admissible k ps : pstate_admissible ps ->
  pstate_admissible (transform_pstate k ps).
Proof. exact: transform_subprob. Qed.
Lemma transform_pstate_external k ps :
  pstate_prob_logic_values (transform_pstate k ps) = pstate_prob_logic_values ps.
Proof. reflexivity. Qed.

(** A finite source is an internal witness used by the library's Fubini
    theorem. It does not change the definition or carrier of transform. *)
Definition finite_source mu (_ : Subprob mu) := constant_kernel mu.
Arguments finite_source mu h : clear implicits.
HB.instance Definition _ mu h := Kernel.on (finite_source mu h).
Lemma finite_source_subprob mu h :
  ereal_sup [set finite_source mu h v setT | v in setT] <= 1.
Proof. by apply: ge_ereal_sup => _ [v _ <-]; exact: h. Qed.
HB.instance Definition _ mu h := Kernel_isSubProbability.Build _ _ _ _ _
  (finite_source mu h) (@finite_source_subprob mu h).

Lemma transform_integral k mu f (hm : Subprob mu) :
  (forall v, 0 <= f v) -> measurable_fun [set: Valuation] f ->
  \int[transform k mu]_w f w = \int[mu]_v (\int[k v]_w f w).
Proof.
move=> f0 mf.
change (\int[mkcomp (finite_source mu hm) (after k) tt]_w f w =
  \int[mu]_v (\int[k v]_w f w)).
exact: integral_kcomp.
Qed.

Lemma bind_integral d (Y : measurableType d)
    (l : real.-spker Valuation ~> Y)
    (k : real.-spker (Valuation * Y) ~> Valuation) v f :
  (forall w, 0 <= f w) -> measurable_fun [set: Valuation] f ->
  \int[bind l k v]_w f w = \int[l v]_y (\int[k (v,y)]_w f w).
Proof. exact: integral_kcomp. Qed.

(** Sampling evaluates its law at v, then updates v with the sample. In
    particular, d may contain TProgVar x: the new sample cannot affect d. *)
Lemma sample_integral x d v f :
  (forall w, 0 <= f w) -> measurable_fun [set: Valuation] f ->
  \int[CommandSemantics.sample x d v]_w f w =
  \int[distribution_measure d v]_z f (update_real v x z).
Proof.
move=> f0 mf; rewrite /CommandSemantics.sample bind_integral//.
by apply: eq_integral => z _; rewrite /real_update /kdirac integral_dirac// diracT mul1e.
Qed.
Lemma toss_integral b r v f :
  (forall w, 0 <= f w) -> measurable_fun [set: Valuation] f ->
  \int[CommandSemantics.toss b r v]_w f w =
  \int[toss_measure (TConst r) v]_z f (update_bool v b z).
Proof.
move=> f0 mf; rewrite /CommandSemantics.toss bind_integral//.
by apply: eq_integral => z _; rewrite /bool_update /kdirac integral_dirac// diracT mul1e.
Qed.
Lemma sample_mass x d v : CommandSemantics.sample x d v setT =
  if distribution_validb d v then 1 else 0.
Proof.
rewrite /CommandSemantics.sample /bind /mkcomp /= /kcomp.
under eq_integral do rewrite /real_update /kdirac /= diracT.
by rewrite integral_cst// mul1e DistributionSemantics.real_law_mass.
Qed.
Lemma toss_mass b r v : CommandSemantics.toss b r v setT =
  if DistributionLaws.toss_valid r then 1 else 0.
Proof.
rewrite /CommandSemantics.toss /bind /mkcomp /= /kcomp.
under eq_integral do rewrite /bool_update /kdirac /= diracT.
by rewrite integral_cst// mul1e DistributionLaws.toss_mass.
Qed.

(** The deterministic transformer is exactly the usual pushforward. *)
Lemma transform_deterministic (f : Valuation -> Valuation)
    (mf : measurable_fun setT f) mu A : measurable A ->
  transform [the real.-spker _ ~> _ of kdirac mf] mu A =
  ConcreteMeasure.push mu mf A.
Proof.
move=> mA; rewrite transform_event /ConcreteMeasure.push /=.
rewrite (eq_integral (fun v => (\1_(f @^-1` A) v)%:E)).
  by move=> v _; rewrite /kdirac /= diracE indicE.
rewrite integral_indic ?setIT//.
by have := mf measurableT A mA; rewrite setTI.
Qed.
Lemma transform_skip mu A : measurable A ->
  transform [the real.-spker _ ~> _ of CommandSemantics.skip] mu A = mu A.
Proof.
by move=> mA; rewrite transform_deterministic.
Qed.
Lemma transform_real_assign x t mu A : measurable A ->
  transform [the real.-spker _ ~> _ of real_assign x t] mu A =
  mu ((fun v => update_real v x (term_eval t v)) @^-1` A).
Proof. exact: transform_deterministic. Qed.
Lemma transform_bool_assign b g mu A : measurable A ->
  transform [the real.-spker _ ~> _ of bool_assign b g] mu A =
  mu ((fun v => update_bool v b (cformula_eval_bool g v)) @^-1` A).
Proof. exact: transform_deterministic. Qed.

Lemma transform_sequence k l mu A : Subprob mu -> measurable A ->
  transform [the real.-spker _ ~> _ of sequence k l] mu A =
  transform l (transform k mu) A.
Proof.
move=> hm mA; rewrite !transform_event (transform_integral _ hm)//.
exact: measurable_kernel.
Qed.

(** Conditional inputs are restricted, not conditioned by division by mass.
    This equation also handles an empty branch and zero input mass. *)
Lemma transform_branch g k l mu A : measurable A ->
  transform [the real.-spker _ ~> _ of branch g k l] mu A =
  transform k (ConcreteMeasure.restrict mu (measurable_formula_event g)) A +
  transform l (ConcreteMeasure.restrict mu (measurableC (measurable_formula_event g))) A.
Proof.
move=> mA; rewrite !transform_event.
rewrite -!/(ConcreteMeasure.integral _ _) !ConcreteMeasure.integral_restrict//;
  try exact: measurable_kernel.
rewrite /ConcreteMeasure.integral.
rewrite -ge0_integralD//.
- by move=> v _; exact: erestrict_ge0.
- apply/(measurable_restrict _ (measurable_formula_event g) measurableT).
  exact: measurable_funS (measurable_kernel k _ mA).
- by move=> v _; exact: erestrict_ge0.
- apply/(measurable_restrict _ (measurableC (measurable_formula_event g)) measurableT).
  exact: measurable_funS (measurable_kernel l _ mA).
- apply: eq_integral => v _.
  change ((if cformula_eval_bool g v then k v else l v) A =
    ((fun w => k w A) \_ (formula_event g)) v +
    ((fun w => l w A) \_ (~` formula_event g)) v).
  rewrite !patchE.
  case: (boolP (v \in formula_event g)) => hv.
  + have -> : cformula_eval_bool g v = true by apply/cformula_eval_bool_spec; exact/set_mem.
    by rewrite in_setC hv /= adde0.
  + have -> : cformula_eval_bool g v = false.
      apply/negbTE; apply/negP => /cformula_eval_bool_spec h.
      by move: hv; rewrite (mem_set (h : formula_event g v)).
    by rewrite in_setC (negbTE hv) /= add0e.
Qed.

(** Linearity checks on primitive inputs expose normalization mistakes. *)
Lemma transform_zero k A : transform k mzero A = 0.
Proof. by rewrite transform_event integral_measure_zero. Qed.
Lemma transform_point k v A : measurable A -> transform k (dirac v) A = k v A.
Proof.
move=> mA; rewrite transform_event integral_dirac ?diracT ?mul1e//.
exact: measurable_kernel.
Qed.
Lemma transform_add k mu nu A : measurable A ->
  transform k (measure_add mu nu) A = transform k mu A + transform k nu A.
Proof.
move=> mA; rewrite !transform_event ge0_integral_measure_add//.
exact: measurable_kernel.
Qed.

(** Bounded real expectations follow from the nonnegative kernel identity.
    Finiteness is proved before projecting an extended integral back to R. *)
Section BoundedExpectation.
Variables (k : Kernel) (f : Valuation -> real).
Hypotheses (mf : measurable_fun setT f)
  (f0 : forall v, (0 <= f v)%R) (f1 : forall v, (f v <= 1)%R).
Definition kernel_expectation v := ConcreteMeasure.expectation (k v) f.
Lemma kernel_expectation_measurable :
  @measurable_fun _ _ [the measurableType _ of Valuation]
    [the measurableType _ of (real : Type)] setT kernel_expectation.
Proof.
apply: measurableT_comp; first exact: fine_measurable.
apply: measurable_fun_integral_kernel.
- exact: measurable_kernel.
- by move=> v; rewrite lee_fin.
- exact/measurable_EFinP.
Qed.
Lemma kernel_expectation_bounds v : (0 <= kernel_expectation v <= 1)%R.
Proof. apply: bounded_real_expectation => //; exact: sprob_kernel_le1. Qed.
Lemma transform_expectation mu : Subprob mu ->
  ConcreteMeasure.expectation (transform k mu) f =
  ConcreteMeasure.expectation mu kernel_expectation.
Proof.
move=> hm.
have fE0 v : 0 <= (f v)%:E by rewrite lee_fin.
have mfE : measurable_fun [set: Valuation] (fun v => (f v)%:E)
  by exact/measurable_EFinP.
rewrite /ConcreteMeasure.expectation /Rintegral
  (@transform_integral k mu (fun v => (f v)%:E) hm fE0 mfE).
congr (fine _); apply: eq_integral => v _; symmetry.
apply: ConcreteMeasure.expectationE; apply: ConcreteMeasure.bounded_integrable => //.
exact: sprob_kernel_le1.
Qed.
End BoundedExpectation.

(** A coordinate is rigid when its changed-value event has zero output mass.
    This formulation permits mass loss without claiming unchanged marginals. *)
Section Rigidity.
Context {T : Type} (obs : Valuation -> T).
Definition changed (v : Valuation) : set Valuation := [set w | obs w <> obs v].
Definition preserves (k : Kernel) := forall v, k v (changed v) = 0.
Hypothesis mchanged : forall v, measurable (changed v).

Lemma deterministic_preserves (f : Valuation -> Valuation)
    (mf : measurable_fun setT f) :
  (forall v, obs (f v) = obs v) ->
  preserves [the real.-spker _ ~> _ of kdirac mf].
Proof.
move=> hf v; rewrite /kdirac /= diracE.
have hn : f v \notin changed v by apply/negP => /set_mem h; exact: h (hf v).
by rewrite (negbTE hn).
Qed.
Lemma sample_preserves x d : (forall v z, obs (update_real v x z) = obs v) ->
  preserves [the real.-spker _ ~> _ of CommandSemantics.sample x d].
Proof.
move=> hf v; rewrite /CommandSemantics.sample /bind /mkcomp /= /kcomp.
apply: integral0_eq => z _; rewrite /real_update /kdirac /= diracE.
have hn : update_real v x z \notin changed v.
  by apply/negP => /set_mem h; exact: h (hf v z).
by rewrite (negbTE hn).
Qed.
Lemma toss_preserves b r : (forall v z, obs (update_bool v b z) = obs v) ->
  preserves [the real.-spker _ ~> _ of CommandSemantics.toss b r].
Proof.
move=> hf v; rewrite /CommandSemantics.toss /bind /mkcomp /= /kcomp.
apply: integral0_eq => z _; rewrite /bool_update /kdirac /= diracE.
have hn : update_bool v b z \notin changed v.
  by apply/negP => /set_mem h; exact: h (hf v z).
by rewrite (negbTE hn).
Qed.
Lemma sequence_preserves k l : preserves k -> preserves l ->
  preserves [the real.-spker _ ~> _ of sequence k l].
Proof.
move=> hk hl v; rewrite /sequence /bind /mkcomp /= /kcomp /after /=.
have ml : measurable_fun setT (l ^~ (changed v)) := measurable_kernel l _ (mchanged v).
rewrite (ge0_negligible_integral (mchanged v) measurableT ml
  (fun w _ => measure_ge0 (l w) (changed v)) (hk v)).
apply: integral0_eq => w [_ hw].
have hwv : obs w = obs v.
  (** The observation type is arbitrary; use MathComp's classical lemma. *)
  exact: (proj1 (boolp.not_notP _) hw).
have -> : changed v = changed w by rewrite /changed hwv.
exact: hl.
Qed.
Lemma branch_preserves g k l : preserves k -> preserves l ->
  preserves [the real.-spker _ ~> _ of branch g k l].
Proof.
move=> hk hl v.
change ((if cformula_eval_bool g v then k v else l v) (changed v) = 0).
by case: (cformula_eval_bool g v); [exact: hk|exact: hl].
Qed.

(** Structural induction uses the same Cmd syntax and the interpreter's
    success equation; it cannot accidentally cover an uninterpreted loop. *)
Lemma nonloop_preserves c k :
  (forall v x z, obs (update_real v x z) = obs v) ->
  (forall v b z, obs (update_bool v b z) = obs v) ->
  nonloop_kernel c = Some k -> preserves k.
Proof.
move=> hr hb; elim: c k => [|x t|b g|b r|x d|a IHa b IHb|g a IHa b IHb|g b IH] k /=.
- move=> [<-]; apply: deterministic_preserves => v; reflexivity.
- move=> [<-]; apply: deterministic_preserves => v; exact: hr.
- move=> [<-]; apply: deterministic_preserves => v; exact: hb.
- move=> [<-]; apply: toss_preserves => v z; exact: hb.
- move=> [<-]; apply: sample_preserves => v z; exact: hr.
- case ha: (nonloop_kernel a) => [ka|] //.
  case hb': (nonloop_kernel b) => [kb|] // [<-].
  apply: sequence_preserves; [exact: IHa ha|exact: IHb hb'].
- case ha: (nonloop_kernel a) => [ka|] //.
  case hb': (nonloop_kernel b) => [kb|] // [<-].
  apply: branch_preserves; [exact: IHa ha|exact: IHb hb'].
- by [].
Qed.
End Rigidity.

Lemma real_logic_changed_measurable x v :
  measurable (changed (fun w => real_logic_values w x) v).
Proof.
change (@measurable _ [the measurableType _ of Valuation] (~` (real_coordinate (inr x) @^-1` [set real_logic_values v x]))).
apply: measurableC.
have hm := measurable_real_coordinate (inr x) measurableT _
  (measurable_set1 (real_logic_values v x : real)).
by move: hm; rewrite setTI.
Qed.
Lemma bool_logic_changed_measurable b v :
  measurable (changed (fun w => bool_logic_values w b) v).
Proof.
change (@measurable _ [the measurableType _ of Valuation] (~` (bool_coordinate (inr b) @^-1` [set bool_logic_values v b]))).
apply: measurableC.
have hm := measurable_bool_coordinate (inr b) measurableT [set bool_logic_values v b] I.
by move: hm; rewrite setTI.
Qed.
Lemma nonloop_real_logic_rigid c k x : nonloop_kernel c = Some k ->
  forall v, k v [set w | real_logic_values w x <> real_logic_values v x] = 0.
Proof.
apply: (@nonloop_preserves _ (fun w => real_logic_values w x)) => //.
exact: real_logic_changed_measurable.
Qed.
Lemma nonloop_bool_logic_rigid c k b : nonloop_kernel c = Some k ->
  forall v, k v [set w | bool_logic_values w b <> bool_logic_values v b] = 0.
Proof.
apply: (@nonloop_preserves _ (fun w => bool_logic_values w b)) => //.
exact: bool_logic_changed_measurable.
Qed.

(** This syntactic characterization checks that every non-loop command is
    interpreted, including nested sequences and conditionals. *)
Fixpoint loop_free (c : Cmd) : bool :=
  match c with
  | CSeq a b | CIf _ a b => loop_free a && loop_free b
  | CWhile _ _ => false
  | _ => true
  end.
Lemma nonloop_kernel_domain c : isSome (nonloop_kernel c) = loop_free c.
Proof.
elim: c => //=.
- move=> a IHa b IHb; rewrite -IHa -IHb.
  by case: (nonloop_kernel a); case: (nonloop_kernel b).
- move=> g a IHa b IHb; rewrite -IHa -IHb.
  by case: (nonloop_kernel a); case: (nonloop_kernel b).
Qed.

Lemma sample_q_eval x d q v :
  ConcreteMeasure.expectation (CommandSemantics.sample x d v) (q_eval q) =
  q_eval (QIntegral x d q) v.
Proof.
rewrite /ConcreteMeasure.expectation /Rintegral sample_integral//.
- by move=> w; rewrite lee_fin; exact: q_eval_nonnegative.
- apply/measurable_EFinP; exact: q_eval_measurable.
Qed.
Lemma transform_sample_q_eval x d q mu : Subprob mu ->
  expectation (transform [the real.-spker _ ~> _ of CommandSemantics.sample x d] mu) (q_eval q) =
  expectation mu (q_eval (QIntegral x d q)).
Proof.
move=> hm; rewrite /expectation
  (@transform_expectation [the real.-spker _ ~> _ of CommandSemantics.sample x d]
    (q_eval q) (q_eval_measurable q) (q_eval_nonnegative q) (q_eval_le_one q) mu hm).
apply: ConcreteMeasure.expectation_ext => v; exact: sample_q_eval.
Qed.

Lemma sample_invalid x d v A : measurable A -> ~ distribution_valid d v ->
  CommandSemantics.sample x d v A = 0.
Proof.
move=> mA hd.
have hn : ~~ distribution_validb d v by apply/negP => /DistributionSemantics.validbP.
have hz : CommandSemantics.sample x d v setT = 0 by rewrite sample_mass (negbTE hn).
exact: subset_measure0 mA measurableT (subsetT A) hz.
Qed.
Lemma toss_invalid b r v A : measurable A -> ~~ DistributionLaws.toss_valid r ->
  CommandSemantics.toss b r v A = 0.
Proof.
move=> mA /negbTE hr.
have hz : CommandSemantics.toss b r v setT = 0 by rewrite toss_mass hr.
exact: subset_measure0 mA measurableT (subsetT A) hz.
Qed.

(** Scaling is linear in the incoming measure, including zero weights. *)
Lemma transform_scale k (c : {nonneg real}) mu A : measurable A ->
  transform k (mscale c mu) A = c%:num%:E * transform k mu A.
Proof.
move=> mA; rewrite !transform_event ge0_integral_mscale//.
exact: measurable_kernel.
Qed.

(** For valid probabilities the toss is exactly the expected two-point law. *)
Lemma toss_integral_valid b r v f : DistributionLaws.toss_valid r ->
  (forall w, 0 <= f w) -> measurable_fun [set: Valuation] f ->
  \int[CommandSemantics.toss b r v]_w f w =
  r%:E * f (update_bool v b true) + (1 - r)%R%:E * f (update_bool v b false).
Proof.
move=> hr f0 mf; rewrite toss_integral// /toss_measure
  /DistributionSemantics.bool_law /= /DistributionLaws.toss hr.
apply: integral_bernoulli_prob => //.
Qed.
