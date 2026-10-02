(** Measurability and finite dependence for the shared classical-state layer.
    Update lemmas re-export the shared proofs needed to construct Cmd kernels.
    These proofs use no CPHL measure, integral, or expectation axiom. *)
From Stdlib Require Import Reals Lists.List FunctionalExtensionality.
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals topology.
From mathcomp Require Import measure measurable_realfun lebesgue_stieltjes_measure.
From mathcomp Require Import Rstruct.
Require Import CPHL.

Import ValuationSpace.
Import numFieldTopology.Exports MeasurableR.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Each generating cylinder is measurable by construction. Both program
    and classical logic projections are covered by the tagged indices. *)
Lemma measurable_real_coordinate i :
  measurable_fun [set: Valuation] (real_coordinate i).
Proof.
move=> _ U mU; rewrite setTI; apply: sub_sigma_algebra.
by left; exists i, U.
Qed.

Lemma measurable_bool_coordinate i :
  measurable_fun [set: Valuation] (bool_coordinate i).
Proof.
move=> _ U mU; rewrite setTI; apply: sub_sigma_algebra.
by right; exists i, U.
Qed.

(** The universal property of the generated sigma-algebra reduces a state
    map's measurability to its real and Boolean coordinate functions. *)
Lemma measurable_into_valuation d (X : measurableType d) (f : X -> Valuation) :
  (forall i, measurable_fun setT (real_coordinate i \o f)) ->
  (forall i, measurable_fun setT (bool_coordinate i \o f)) ->
  measurable_fun setT f.
Proof. exact: CommandSemantics.measurable_into_valuation. Qed.

(** Arithmetic terms are measurable because projections, constants, sums,
    and products of real measurable functions are measurable. *)
Lemma measurable_term (t : Term) :
  @measurable_fun _ _ [the measurableType _ of Valuation]
    [the measurableType _ of (real : Type)] setT (term_eval t).
Proof.
elim: t => [x|x|r|t1 m1 t2 m2|t1 m1 t2 m2] /=.
- exact: measurable_real_coordinate (inl x).
- exact: measurable_real_coordinate (inr x).
- exact: measurable_cst.
- exact: measurable_funD.
- exact: measurable_funM.
Qed.

(** Truth reification agrees with the existing Prop-valued semantics. *)
Lemma cformula_eval_bool_spec gamma v :
  cformula_eval_bool gamma v = true <-> satisfies v gamma.
Proof. exact: CommandSemantics.cformula_eval_bool_spec. Qed.

Lemma measurable_bool_true (f : Valuation -> bool) :
  measurable_fun setT f -> measurable (f @^-1` [set true]).
Proof.
move=> mf; rewrite -[f @^-1` _]setTI.
exact: mf measurableT [set true] I.
Qed.

(** Formula events use complements/unions for implication and the Borel
    comparison relation for <=. This proves only syntactic events measurable. *)
Lemma measurable_formula_event gamma : measurable (formula_event gamma).
Proof.
elim: gamma => [b|b|t1 t2| |g1 m1 g2 m2].
- exact: measurable_bool_true _ (measurable_bool_coordinate (inl b)).
- exact: measurable_bool_true _ (measurable_bool_coordinate (inr b)).
- have -> : formula_event (FLe t1 t2) =
      (fun v : Valuation => (term_eval t1 v <= term_eval t2 v)%R)
        @^-1` [set true].
    apply functional_extensionality; intro v.
    apply propext.
    change (Rle (term_eval t1 v) (term_eval t2 v) <->
            (term_eval t1 v <= term_eval t2 v)%R = true).
    by split=> [/RleP|/RleP].
  apply: measurable_bool_true.
  exact: measurable_fun_ler (measurable_term t1) (measurable_term t2).
- exact: measurable0.
- have -> : formula_event (FImpl g1 g2) =
      (~` formula_event g1) `|` formula_event g2.
    apply functional_extensionality; intro v.
    apply propext.
    change ((satisfies v g1 -> satisfies v g2) <->
            (~ satisfies v g1 \/ satisfies v g2)).
    (** Implication needs only the antecedent's syntax-directed decision. *)
    destruct (cformula_satisfies_dec g1 v); tauto.
  exact: measurableU (measurableC m1) m2.
Qed.

Lemma measurable_cformula_eval_bool gamma :
  measurable_fun [set: Valuation] (cformula_eval_bool gamma).
Proof. exact: CommandSemantics.measurable_cformula_eval_bool. Qed.

(** Joint measurability is needed for sampling: the assigned value is an
    additional input coordinate, not a fixed constant. *)
Lemma measurable_real_update x :
  measurable_fun [set: Valuation * real]
    (fun p => update_real p.1 x p.2 : Valuation).
Proof. exact: CommandSemantics.measurable_real_update. Qed.

Lemma measurable_bool_update b :
  measurable_fun [set: Valuation * bool]
    (fun p => update_bool p.1 b p.2 : Valuation).
Proof. exact: CommandSemantics.measurable_bool_update. Qed.

(** Deterministic assignments evaluate their right-hand sides in the input
    state and then apply the jointly measurable update. *)
Lemma measurable_real_assignment x t :
  measurable_fun [set: Valuation]
    (fun v => update_real v x (term_eval t v) : Valuation).
Proof. exact: CommandSemantics.measurable_real_assignment. Qed.

Lemma measurable_bool_assignment b gamma :
  measurable_fun [set: Valuation]
    (fun v => update_bool v b (cformula_eval_bool gamma v) : Valuation).
Proof. exact: CommandSemantics.measurable_bool_assignment. Qed.
