(** Continuous Probabilistic Hoare Logic: shared syntax, rules, measurable
    states, concrete measures/integrals, and assertion semantics. Construct
    bounds are proved in Soundness/ConstructFacts; capture-avoiding Boolean
    substitution is justified in Soundness/BindingFacts. Command denotations,
    including finite loop exits and their limit, are defined below. *)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Ascii.
From Stdlib Require Import ClassicalDescription.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.

(** Keep analytical notation inside modules so the shared syntax and examples
    retain their Stdlib-facing real-number interface. *)
Require AnalysisPrelude.
Require MeasureIntegration.
Require DistributionKernels.
From HB Require Import structures.
Import MeasureIntegration.
From mathcomp Require boot order ssralg ssrnum boolp classical_sets.
From mathcomp Require reals topology ereal measure measurable_realfun.
From mathcomp Require lebesgue_measure lebesgue_stieltjes_measure Rstruct.
From mathcomp Require functions normedtype sequences esum lebesgue_integral kernel Rstruct_topology.

Open Scope R_scope.
Open Scope string_scope.
Open Scope char_scope.
Import ListNotations.

(** Variable identifiers are nominally distinct even though each is named by
    a string.  This prevents Boolean identifiers from appearing in real terms
    (and conversely), and separates program variables from logic variables. *)
Inductive RealProgramVar : Type :=
  | real_program_var (name : string).

Inductive BoolProgramVar : Type :=
  | bool_program_var (name : string).

Inductive RealLogicVar : Type :=
  | real_logic_var (name : string).

Inductive BoolLogicVar : Type :=
  | bool_logic_var (name : string).

Definition real_program_var_eq_dec :
  forall x y : RealProgramVar, {x = y} + {x <> y}.
Proof.
  decide equality; apply string_dec.
Defined.

Definition bool_program_var_eq_dec :
  forall x y : BoolProgramVar, {x = y} + {x <> y}.
Proof.
  decide equality; apply string_dec.
Defined.

Definition real_logic_var_eq_dec :
  forall x y : RealLogicVar, {x = y} + {x <> y}.
Proof.
  decide equality; apply string_dec.
Defined.

Definition bool_logic_var_eq_dec :
  forall x y : BoolLogicVar, {x = y} + {x <> y}.
Proof.
  decide equality; apply string_dec.
Defined.

(** A valuation assigns values to the four classes of variables in the paper.
    Program execution updates only the program-variable fields. *)
Record valuation : Type := {
  real_program_values : RealProgramVar -> R;
  bool_program_values : BoolProgramVar -> bool;
  real_logic_values : RealLogicVar -> R;
  bool_logic_values : BoolLogicVar -> bool
}.

Definition state : Type := valuation.

(** Real-valued terms: [xm | X | c | t + t | t t]. *)
Inductive Term : Type :=
  | TProgVar (x : RealProgramVar)
  | TLogicVar (x : RealLogicVar)
  | TConst (c : R)
  | TAdd (t1 t2 : Term)
  | TMul (t1 t2 : Term).

(** Classical formulas: [bm | B | t <= t | false | gamma => gamma]. *)
Inductive CFormula : Type :=
  | FProgBool (b : BoolProgramVar)
  | FLogicBool (b : BoolLogicVar)
  | FLe (t1 t2 : Term)
  | FFalse
  | FImpl (gamma1 gamma2 : CFormula).

(** The remaining classical connectives are paper-level abbreviations. *)
Definition c_true : CFormula := FImpl FFalse FFalse.

Definition c_not (gamma : CFormula) : CFormula :=
  FImpl gamma FFalse.

Definition c_and (gamma1 gamma2 : CFormula) : CFormula :=
  c_not (FImpl gamma1 (c_not gamma2)).

Definition c_or (gamma1 gamma2 : CFormula) : CFormula :=
  FImpl (c_not gamma1) gamma2.

Definition c_iff (gamma1 gamma2 : CFormula) : CFormula :=
  c_and (FImpl gamma1 gamma2) (FImpl gamma2 gamma1).

Fixpoint term_eval (t : Term) (v : state) : R :=
  match t with
  | TProgVar x => real_program_values v x
  | TLogicVar x => real_logic_values v x
  | TConst c => c
  | TAdd t1 t2 => term_eval t1 v + term_eval t2 v
  | TMul t1 t2 => term_eval t1 v * term_eval t2 v
  end.

Fixpoint satisfies (v : state) (gamma : CFormula) {struct gamma} : Prop :=
  match gamma with
  | FProgBool b => bool_program_values v b = true
  | FLogicBool b => bool_logic_values v b = true
  | FLe t1 t2 => (term_eval t1 v <= term_eval t2 v)%R
  | FFalse => False
  | FImpl gamma1 gamma2 => satisfies v gamma1 -> satisfies v gamma2
  end.

(** Semantic classical assertions are predicates on valuations. *)
Definition Assertion : Type := state -> Prop.

Definition formula_assertion (gamma : CFormula) : Assertion :=
  fun v => satisfies v gamma.

Theorem formula_assertion_spec :
  forall (gamma : CFormula) (v : state),
    formula_assertion gamma v <-> satisfies v gamma.
Proof.
  intros gamma v.
  split; intro H; exact H.
Qed.

(** Commands need a Boolean truth value for a classical guard. This merely
    reifies [satisfies]; it does not change the existing logical semantics. *)
Definition cformula_eval_bool (gamma : CFormula) (v : state) : bool :=
  if excluded_middle_informative (satisfies v gamma) then true else false.

Module ValuationSpace.

(** Keep analytical notation local to this module. The measurable carrier
    below is definitionally the existing four-map valuation record. *)
Import boot order ssralg ssrnum boolp classical_sets.
Import reals topology measure lebesgue_stieltjes_measure Rstruct.
Import numFieldTopology.Exports MeasurableR.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.

Definition RawValuation := {classic valuation}.
Definition RealCoordinate := (RealProgramVar + RealLogicVar)%type.
Definition BoolCoordinate := (BoolProgramVar + BoolLogicVar)%type.

Definition real_coordinate (i : RealCoordinate) (v : RawValuation) : real :=
  match i with
  | inl x => real_program_values v x
  | inr x => real_logic_values v x
  end.

Definition bool_coordinate (i : BoolCoordinate) (v : RawValuation) : bool :=
  match i with
  | inl b => bool_program_values v b
  | inr b => bool_logic_values v b
  end.

(** Generate the smallest sigma-algebra making every coordinate measurable:
    Borel events for reals and all events for Booleans. Logic coordinates
    remain part of the joint state; no independence or fixed value is imposed. *)
Definition valuation_generators : set_system RawValuation :=
  [set A | (exists i (U : set real), measurable U /\
                       A = real_coordinate i @^-1` U) \/
           (exists i (U : set bool), measurable U /\
                       A = bool_coordinate i @^-1` U)].

Definition Valuation := g_sigma_algebraType valuation_generators.

(** Giving formula events this carrier makes their sigma-algebra explicit.
    This does not assert that arbitrary [Assertion] predicates are measurable. *)
Definition formula_event (gamma : CFormula) : set Valuation :=
  formula_assertion gamma.

(** These foundational facts precede integration to avoid importing
    Soundness/StateSpace back into the shared semantic definitions. *)
Import measurable_realfun.
Local Open Scope ring_scope.

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

Lemma measurable_bool_true (f : Valuation -> bool) :
  measurable_fun setT f -> measurable (f @^-1` [set true]).
Proof.
move=> mf; rewrite -[f @^-1` _]setTI.
exact: mf measurableT [set true] I.
Qed.

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
    destruct (Classical_Prop.classic (satisfies v g1)); tauto.
  exact: measurableU (measurableC m1) m2.
Qed.

End ValuationSpace.

(** Compilation checks for the syntax and semantics above. *)
Definition demo_real_program_var : RealProgramVar :=
  real_program_var "x".

Definition demo_bool_program_var : BoolProgramVar :=
  bool_program_var "b".

Definition demo_real_logic_var : RealLogicVar :=
  real_logic_var "X".

Definition demo_bool_logic_var : BoolLogicVar :=
  bool_logic_var "B".

Definition demo_valuation : valuation :=
  {| real_program_values := fun _ => 2%R;
     bool_program_values := fun _ => true;
     real_logic_values := fun _ => 3%R;
     bool_logic_values := fun _ => true |}.

Example real_program_var_eq_dec_type :
  {demo_real_program_var = demo_real_program_var} +
  {demo_real_program_var <> demo_real_program_var}.
Proof.
  apply real_program_var_eq_dec.
Qed.

Example term_eval_example :
  term_eval
    (TAdd (TProgVar demo_real_program_var)
      (TMul (TLogicVar demo_real_logic_var) (TConst 2%R)))
    demo_valuation = 8%R.
Proof.
  cbn [term_eval demo_valuation real_program_values real_logic_values].
  ring.
Qed.

Example program_bool_satisfaction_example :
  satisfies demo_valuation (FProgBool demo_bool_program_var).
Proof.
  cbn [satisfies demo_valuation bool_program_values].
  reflexivity.
Qed.

Example logic_bool_satisfaction_example :
  satisfies demo_valuation (FLogicBool demo_bool_logic_var).
Proof.
  cbn [satisfies demo_valuation bool_logic_values].
  reflexivity.
Qed.

Example real_comparison_satisfaction_example :
  satisfies demo_valuation
    (FLe (TProgVar demo_real_program_var) (TLogicVar demo_real_logic_var)).
Proof.
  cbn [satisfies term_eval demo_valuation real_program_values real_logic_values].
  lra.
Qed.

Example derived_connectives_satisfaction_example :
  satisfies demo_valuation c_true /\
  satisfies demo_valuation (c_not FFalse) /\
  satisfies demo_valuation (c_and c_true c_true) /\
  satisfies demo_valuation (c_or FFalse c_true) /\
  satisfies demo_valuation (c_iff c_true c_true).
Proof.
  cbn [c_true c_not c_and c_or c_iff satisfies].
  tauto.
Qed.

(** Concrete countably additive measures over the joint valuation space.
    [Subprob] remains separate: Pstate carries no admissibility proof. *)
Module StateMeasure.
Import boot order ssralg ssrnum boolp classical_sets.
Import reals topology measure lebesgue_stieltjes_measure Rstruct.
Import ValuationSpace.
Local Open Scope classical_set_scope.
Definition Space := [the measurableType _ of Valuation].
Definition carrier : Type := @ConcreteMeasure.measure _ Space.
Definition measurable_event (A : Assertion) : Prop :=
  @measurable _ Valuation A.

(** Finite real event masses inherit additivity only on measurable events. *)
Lemma additive (mu : carrier) A B : ConcreteMeasure.Finite mu ->
  measurable_event A -> measurable_event B ->
  (forall v, ~ (A v /\ B v)) ->
  ConcreteMeasure.event_mass mu (fun v => A v \/ B v) =
    (ConcreteMeasure.event_mass mu A + ConcreteMeasure.event_mass mu B)%R.
Proof.
move=> hm mA mB h; apply: ConcreteMeasure.event_additive => //.
apply functional_extensionality => v; apply propext.
split => [hv|hf]; [exact: (h v hv) | contradiction].
Qed.
End StateMeasure.

Definition Measure : Type := StateMeasure.carrier.
Definition Subprob : Measure -> Prop := ConcreteMeasure.Subprob.
Definition FiniteMeasure : Measure -> Prop := ConcreteMeasure.Finite.
Definition measurable_assertion := StateMeasure.measurable_event.
Definition measure_of : Measure -> Assertion -> R := ConcreteMeasure.event_mass.

Lemma measure_additive : forall (mu : Measure) (A B : Assertion),
  FiniteMeasure mu -> measurable_assertion A -> measurable_assertion B ->
  (forall v : state, ~ (A v /\ B v)) ->
  measure_of mu (fun v : state => A v \/ B v) =
    (measure_of mu A + measure_of mu B)%R.
Proof. exact StateMeasure.additive. Qed.

Lemma measure_empty : forall mu : Measure,
  measure_of mu (fun _ : state => False) = 0%R.
Proof. intro mu; apply ConcreteMeasure.event_empty. Qed.

Lemma measure_extensional : forall (mu : Measure) (A B : Assertion),
  (forall v : state, A v <-> B v) -> measure_of mu A = measure_of mu B.
Proof.
  intros mu A B h; assert (A = B) as ->.
  { apply functional_extensionality; intro v; apply boolp.propext; apply h. }
  reflexivity.
Qed.

Lemma measure_nonnegative : forall (mu : Measure) (A : Assertion),
  (0 <= measure_of mu A)%R.
Proof.
  intros mu A; exact (ssrbool.elimT Rstruct.RleP
    (ConcreteMeasure.event_nonnegative mu A)).
Qed.

Lemma measure_subprobability : forall mu : Measure, Subprob mu ->
  (measure_of mu (fun _ : state => True) <= 1)%R.
Proof.
  intros mu hm; exact (ssrbool.elimT Rstruct.RleP
    (ConcreteMeasure.mass_bound hm)).
Qed.

(** Probabilistic logic variables are rigid real-valued variables in the
    probabilistic layer. *)
Inductive ProbLogicVar : Type :=
  | prob_logic_var (name : string).

Definition prob_logic_var_eq_dec :
  forall x y : ProbLogicVar, {x = y} + {x <> y}.
Proof.
  decide equality; apply string_dec.
Defined.

Record Pstate : Type := {
  pstate_measure : Measure;
  pstate_prob_logic_values : ProbLogicVar -> R
}.

(** Admissibility constrains only the measure. The external probabilistic
    assignment is arbitrary, and no proof is stored in the state itself. *)
Definition pstate_admissible (ps : Pstate) : Prop :=
  Subprob (pstate_measure ps).

(** The continuous distributions supported by the assertion language.  Their
    parameters are state-dependent real terms. *)
Inductive Distribution : Type :=
  | Uniform (lower upper : Term)
  | Laplace (location scale : Term)
  | Gaussian (mean standard_deviation : Term).

Definition distribution_valid (d : Distribution) (v : state) : Prop :=
  match d with
  | Uniform lower upper =>
      (term_eval lower v < term_eval upper v)%R
  | Laplace _ scale =>
      (0 < term_eval scale v)%R
  | Gaussian _ standard_deviation =>
      (0 < term_eval standard_deviation v)%R
  end.

(** [real_indicator] is the real-valued characteristic function of a Rocq
    proposition.  Classical excluded middle is used only to choose its value. *)
Definition real_indicator (P : Prop) : R :=
  if excluded_middle_informative P then 1%R else 0%R.

Lemma real_indicator_true :
  forall P : Prop, P -> real_indicator P = 1%R.
Proof.
  intros P HP.
  unfold real_indicator.
  destruct (excluded_middle_informative P); [reflexivity | contradiction].
Qed.

Lemma real_indicator_false :
  forall P : Prop, ~ P -> real_indicator P = 0%R.
Proof.
  intros P HP.
  unfold real_indicator.
  destruct (excluded_middle_informative P); [contradiction | reflexivity].
Qed.

Lemma real_indicator_extensional :
  forall P Q : Prop,
    (P <-> Q) -> real_indicator P = real_indicator Q.
Proof.
  intros P Q Hequiv.
  destruct (excluded_middle_informative P) as [HP | HnP].
  - rewrite (real_indicator_true P HP).
    rewrite (real_indicator_true Q (proj1 Hequiv HP)).
    reflexivity.
  - rewrite (real_indicator_false P HnP).
    rewrite (real_indicator_false Q).
    + reflexivity.
    + intro HQ; apply HnP; apply (proj2 Hequiv); exact HQ.
Qed.

(** These are the standard density expressions.  They are total Rocq
    functions even for invalid parameters; [distribution_valid] is required
    before treating such an expression as a probability density. *)
Definition distribution_density (d : Distribution) (v : state) (z : R) : R :=
  match d with
  | Uniform lower upper =>
      let lower_value := term_eval lower v in
      let upper_value := term_eval upper v in
      real_indicator (lower_value <= z /\ z <= upper_value)%R /
        (upper_value - lower_value)
  | Laplace location scale =>
      let location_value := term_eval location v in
      let scale_value := term_eval scale v in
      (1 / (2 * scale_value)) *
        exp (- Rabs (z - location_value) / scale_value)
  | Gaussian mean standard_deviation =>
      let mean_value := term_eval mean v in
      let deviation_value := term_eval standard_deviation v in
      (1 / (deviation_value * sqrt (2 * PI))) *
        exp (- ((z - mean_value) * (z - mean_value)) /
          (2 * deviation_value * deviation_value))
  end.

(** Parameter expressions are evaluated in the incoming joint valuation.
    These kernels return sampled values; CommandSemantics applies their updates. *)
Module DistributionSemantics.
Import boot order ssralg ssrnum boolp classical_sets functions.
Import reals topology ereal measure measurable_realfun kernel Rstruct.
Import lebesgue_stieltjes_measure.
Import numFieldTopology.Exports MeasurableR.
Import Order.TTheory GRing.Theory Num.Theory.
Import ValuationSpace DistributionKernels.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Definition validb (d : CPHL.Distribution) (v : Valuation) : bool :=
  match d with
  | CPHL.Uniform a b => (term_eval a v < term_eval b v)%R
  | CPHL.Laplace _ s | CPHL.Gaussian _ s => (0 < term_eval s v)%R
  end.

Lemma validbP d v : reflect (distribution_valid d v) (validb d v).
Proof. case: d => a b; exact: RltP. Qed.

Lemma validb_measurable d : measurable_fun [set: Valuation] (validb d).
Proof.
case: d => a b; apply: measurable_fun_ltr => //; exact: measurable_term.
Qed.

Definition real_law (d : CPHL.Distribution) (v : Valuation) :
    {measure set real -> \bar real} :=
  match d with
  | CPHL.Uniform a b => DistributionLaws.uniform (term_eval a v, term_eval b v)
  | CPHL.Laplace m s => DistributionLaws.laplace (term_eval m v, term_eval s v)
  | CPHL.Gaussian m s => DistributionLaws.gaussian (term_eval m v, term_eval s v)
  end.

Lemma real_law_measurable d A : measurable A ->
  measurable_fun [set: Valuation] (real_law d ^~ A).
Proof.
move=> mA.
have mp a b : @measurable_fun _ _ [the measurableType _ of Valuation]
    [the measurableType _ of (real * real)%type] setT
    (fun v => (term_eval a v, term_eval b v)).
  apply: measurable_fun_pair; exact: measurable_term.
case: d => a b.
- exact: measurableT_comp (measurable_kernel DistributionLaws.uniform A mA) (mp a b).
- exact: measurableT_comp (measurable_kernel DistributionLaws.laplace A mA) (mp a b).
- exact: measurableT_comp (measurable_kernel DistributionLaws.gaussian A mA) (mp a b).
Qed.

HB.instance Definition _ d := isKernel.Build _ _ _ _ _
  (real_law d) (real_law_measurable d).

Lemma real_law_mass d v : real_law d v setT = if validb d v then 1 else 0.
Proof.
case: d => a b; rewrite /real_law /validb;
  exact: DistributionLaws.parameter_measure_mass.
Qed.

Lemma real_law_subprob d :
  ereal_sup [set real_law d v setT | v in [set: Valuation]] <= 1.
Proof.
apply: ge_ereal_sup => _ [v _ <-]; rewrite real_law_mass.
by case: (validb d v); [exact: lexx | exact: lee01].
Qed.

HB.instance Definition _ d := Kernel_isSubProbability.Build _ _ _ _ _
  (real_law d) (real_law_subprob d).

(** Toss includes both endpoint probabilities and rejects values outside
    [0,1]; it also leaves the incoming valuation untouched. *)
Definition bool_law (t : Term) (v : Valuation) :
    {measure set bool -> \bar real} := DistributionLaws.toss (term_eval t v).

Lemma bool_law_measurable t A : measurable A ->
  measurable_fun [set: Valuation] (bool_law t ^~ A).
Proof.
move=> mA; exact: measurableT_comp
  (@DistributionLaws.toss_measurable A mA) (measurable_term t).
Qed.

HB.instance Definition _ t := isKernel.Build _ _ _ _ _
  (bool_law t) (bool_law_measurable t).

Lemma bool_law_subprob t :
  ereal_sup [set bool_law t v setT | v in [set: Valuation]] <= 1.
Proof.
apply: ge_ereal_sup => _ [v _ <-]; rewrite /bool_law DistributionLaws.toss_mass.
by case: (DistributionLaws.toss_valid (term_eval t v));
  [exact: lexx | exact: lee01].
Qed.

HB.instance Definition _ t := Kernel_isSubProbability.Build _ _ _ _ _
  (bool_law t) (bool_law_subprob t).
End DistributionSemantics.

Definition distribution_measure := DistributionSemantics.real_law.
Definition distribution_validb := DistributionSemantics.validb.
Definition toss_measure := DistributionSemantics.bool_law.

(** Point update for the real-valued program-variable component of a state.
    It supports the nameless integral binder below. *)
Definition update_real_values
  (values : RealProgramVar -> R) (x : RealProgramVar) (r : R) :
  RealProgramVar -> R :=
  fun y => if real_program_var_eq_dec y x then r else values y.

Definition update_real (v : state) (x : RealProgramVar) (r : R) : state :=
  {| real_program_values := update_real_values (real_program_values v) x r;
     bool_program_values := bool_program_values v;
     real_logic_values := real_logic_values v;
     bool_logic_values := bool_logic_values v |}.

(** Boolean assignment updates only its program coordinate, preserving both
    classical logic maps and every real-valued coordinate. *)
Definition update_bool_values
  (values : BoolProgramVar -> bool) (b : BoolProgramVar) (value : bool) :
  BoolProgramVar -> bool :=
  fun c => if bool_program_var_eq_dec c b then value else values c.

Definition update_bool (v : state) (b : BoolProgramVar) (value : bool) : state :=
  {| real_program_values := real_program_values v;
     bool_program_values := update_bool_values (bool_program_values v) b value;
     real_logic_values := real_logic_values v;
     bool_logic_values := bool_logic_values v |}.

(** Probability constructs.  [QIntegral x d q] denotes the paper's
    [integral q^x_k f(k) dk]; the displayed variable [k] is nameless here and
    hence alpha-equivalent choices have the same representation. *)
Inductive PConstruct : Type :=
  | QIndicator (gamma : CFormula)
  | QIntegral (x : RealProgramVar) (d : Distribution) (q : PConstruct).

(** Real Lebesgue integration on the library's Borel real line. The
    total real projection sends infinities to zero; algebraic use therefore
    requires integrability, and limits use the extended integral instead. *)
Module RealIntegration.
Import boot order ssralg ssrnum reals topology ereal classical_sets.
Import measure lebesgue_measure Rstruct.
Import numFieldTopology.Exports MeasurableR.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Definition Space := [the measurableType _ of (real : Type)].
Definition lebesgue : {measure set real -> \bar real} := lebesgue_measure.
End RealIntegration.

Definition real_integral : (R -> R) -> R :=
  @ConcreteMeasure.expectation _ RealIntegration.Space RealIntegration.lebesgue.
Definition real_integrable : (R -> R) -> Prop :=
  @ConcreteMeasure.Integrable _ RealIntegration.Space RealIntegration.lebesgue.

Lemma real_integral_extensional : forall f g : R -> R,
  (forall x : R, f x = g x) -> real_integral f = real_integral g.
Proof. exact (@ConcreteMeasure.expectation_ext _ RealIntegration.Space RealIntegration.lebesgue). Qed.

Lemma real_integral_add : forall f g : R -> R,
  real_integrable f -> real_integrable g ->
  real_integral (fun x => f x + g x) = (real_integral f + real_integral g)%R.
Proof. exact (@ConcreteMeasure.expectation_add _ RealIntegration.Space RealIntegration.lebesgue). Qed.

Lemma real_integral_scale : forall (c : R) (f : R -> R),
  real_integrable f ->
  real_integral (fun x => c * f x) = (c * real_integral f)%R.
Proof. exact (@ConcreteMeasure.expectation_scale _ RealIntegration.Space RealIntegration.lebesgue). Qed.

Lemma real_integral_zero : real_integral (fun _ : R => 0%R) = 0%R.
Proof. exact (@ConcreteMeasure.expectation_zero _ RealIntegration.Space RealIntegration.lebesgue). Qed.

(** Half-open regions are disjoint; no normalization is built into a region. *)
Definition real_integral_below (a : R) (f : R -> R) : R :=
  real_integral (fun x => real_indicator (x < a)%R * f x).
Definition real_integral_between (a b : R) (f : R -> R) : R :=
  real_integral (fun x => real_indicator (a <= x < b)%R * f x).
Definition real_integral_above (a : R) (f : R -> R) : R :=
  real_integral (fun x => real_indicator (a <= x)%R * f x).

(** Integral binders sample from the incoming state's law, then update only
    their body. Invalid laws already have zero mass. ConstructFacts proves
    the integrand measurable and bounded, justifying this real expectation. *)
Fixpoint q_eval (q : PConstruct) (v : state) : R :=
  match q with
  | QIndicator gamma => real_indicator (satisfies v gamma)
  | QIntegral x d q' =>
      @ConcreteMeasure.expectation _ RealIntegration.Space (distribution_measure d v)
        (fun k => q_eval q' (update_real v x k))
  end.

(** Real expectations are concrete; linearity carries the integrability
    obligations that were absent from the former axioms. *)
Definition expectation : Measure -> (state -> R) -> R :=
  @ConcreteMeasure.expectation _ StateMeasure.Space.
Definition expectation_integrable : Measure -> (state -> R) -> Prop :=
  @ConcreteMeasure.Integrable _ StateMeasure.Space.

Module IndicatorExpectation.
Import boot order ssralg ssrnum boolp classical_sets.
Import reals topology measure measurable_realfun lebesgue_stieltjes_measure Rstruct.
Import ValuationSpace.
Import numFieldTopology.Exports MeasurableR.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** The Prop-valued indicator and the library's measurable indicator agree. *)
Lemma indicatorE {T : Type} (A : T -> Prop) v :
  real_indicator (A v) = numfun.indic A v.
Proof.
rewrite /real_indicator numfun.indicE.
case: (excluded_middle_informative (A v)) => h.
- by rewrite (mem_set h).
- have hn : v \notin (A : set T) by apply/negP => /set_mem; exact: h.
  by rewrite (negbTE hn).
Qed.

Lemma indicator_expectation (mu : StateMeasure.carrier) gamma :
  expectation mu (q_eval (QIndicator gamma)) =
    measure_of mu (formula_assertion gamma).
Proof.
transitivity (ConcreteMeasure.expectation mu (numfun.indic (formula_event gamma))).
- apply: ConcreteMeasure.expectation_ext => v; exact: indicatorE.
- apply: ConcreteMeasure.expectation_indicator.
  exact: measurable_formula_event.
Qed.
End IndicatorExpectation.

Lemma expectation_indicator : forall (mu : Measure) (gamma : CFormula),
  expectation mu (q_eval (QIndicator gamma)) =
    measure_of mu (formula_assertion gamma).
Proof. exact IndicatorExpectation.indicator_expectation. Qed.

(** Constants are handled directly, including zero and infinite measures;
    this identity does not need a general signed-linearity assumption. *)
Lemma expectation_constant : forall (mu : Measure) (c : R),
  expectation mu (fun _ : state => c) =
    (c * expectation mu (q_eval (QIndicator c_true)))%R.
Proof.
  intros mu c; rewrite expectation_indicator.
  transitivity (c * measure_of mu (fun _ => True))%R.
  - exact (@ConcreteMeasure.expectation_constant _ StateMeasure.Space mu c).
  - f_equal; apply measure_extensional; intro v.
    unfold formula_assertion, c_true; cbn [satisfies]; tauto.
Qed.

Lemma expectation_extensional : forall (mu : Measure) (f g : state -> R),
  (forall v : state, f v = g v) -> expectation mu f = expectation mu g.
Proof. intros mu f g h; apply ConcreteMeasure.expectation_ext; exact h. Qed.

Lemma expectation_scale : forall (mu : Measure) (c : R) (f : state -> R),
  expectation_integrable mu f ->
  expectation mu (fun v => c * f v) = (c * expectation mu f)%R.
Proof. intros mu c f h; apply ConcreteMeasure.expectation_scale; exact h. Qed.

Lemma expectation_zero : forall mu : Measure,
  expectation mu (fun _ : state => 0%R) = 0%R.
Proof. intro mu; apply ConcreteMeasure.expectation_zero. Qed.

(** Probabilistic terms: [y | r | E[q] | p + p | p p]. *)
Inductive Pterm : Type :=
  | PVar (y : ProbLogicVar)
  | PConst (r : R)
  | PExpect (q : PConstruct)
  | PAdd (p1 p2 : Pterm)
  | PMul (p1 p2 : Pterm).

Fixpoint pterm_eval (p : Pterm) (ps : Pstate) : R :=
  match p with
  | PVar y => pstate_prob_logic_values ps y
  | PConst r => r
  | PExpect q => expectation (pstate_measure ps) (q_eval q)
  | PAdd p1 p2 => pterm_eval p1 ps + pterm_eval p2 ps
  | PMul p1 p2 => pterm_eval p1 ps * pterm_eval p2 ps
  end.

(** Probabilistic formulas: [p <= p | false | eta => eta]. *)
Inductive PFormula : Type :=
  | PFLe (p1 p2 : Pterm)
  | PFFalse
  | PFImpl (eta1 eta2 : PFormula).

Fixpoint psatisfies (ps : Pstate) (eta : PFormula) {struct eta} : Prop :=
  match eta with
  | PFLe p1 p2 => (pterm_eval p1 ps <= pterm_eval p2 ps)%R
  | PFFalse => False
  | PFImpl eta1 eta2 => psatisfies ps eta1 -> psatisfies ps eta2
  end.

(** Derived probabilistic connectives and comparisons. *)
Definition p_true : PFormula := PFImpl PFFalse PFFalse.

Definition p_not (eta : PFormula) : PFormula :=
  PFImpl eta PFFalse.

Definition p_and (eta1 eta2 : PFormula) : PFormula :=
  p_not (PFImpl eta1 (p_not eta2)).

Definition p_or (eta1 eta2 : PFormula) : PFormula :=
  PFImpl (p_not eta1) eta2.

Definition p_iff (eta1 eta2 : PFormula) : PFormula :=
  p_and (PFImpl eta1 eta2) (PFImpl eta2 eta1).

Definition p_eq (p1 p2 : Pterm) : PFormula :=
  p_and (PFLe p1 p2) (PFLe p2 p1).

Definition p_lt (p1 p2 : Pterm) : PFormula :=
  p_not (PFLe p2 p1).

Definition p_almost_sure (gamma : CFormula) : PFormula :=
  p_eq (PExpect (QIndicator gamma)) (PExpect (QIndicator c_true)).

(** Semantic probabilistic assertions are predicates on probabilistic states. *)
Definition PAssertion : Type := Pstate -> Prop.

Definition pformula_assertion (eta : PFormula) : PAssertion :=
  fun ps => psatisfies ps eta.

Theorem pformula_assertion_spec :
  forall (eta : PFormula) (ps : Pstate),
    pformula_assertion eta ps <-> psatisfies ps eta.
Proof.
  intros eta ps.
  split; intro H; exact H.
Qed.

(** Compilation checks for the probabilistic layer. *)
Section ProbabilisticExamples.
  Variable demo_measure : Measure.

  Definition demo_prob_logic_var : ProbLogicVar :=
    prob_logic_var "y".

  Definition demo_pstate : Pstate :=
    {| pstate_measure := demo_measure;
       pstate_prob_logic_values := fun _ => 7%R |}.

  Example prob_logic_var_eq_dec_type :
    {demo_prob_logic_var = demo_prob_logic_var} +
    {demo_prob_logic_var <> demo_prob_logic_var}.
  Proof.
    apply prob_logic_var_eq_dec.
  Qed.

  Example probabilistic_variable_evaluation_example :
    pterm_eval (PVar demo_prob_logic_var) demo_pstate = 7%R.
  Proof.
    cbn [pterm_eval demo_pstate pstate_prob_logic_values].
    reflexivity.
  Qed.

  Example indicator_expectation_example :
    pterm_eval (PExpect (QIndicator (FProgBool demo_bool_program_var)))
      demo_pstate =
      measure_of demo_measure
        (formula_assertion (FProgBool demo_bool_program_var)).
  Proof.
    cbn [pterm_eval demo_pstate pstate_measure].
    apply expectation_indicator.
  Qed.

  Example probabilistic_term_arithmetic_example :
    pterm_eval
      (PAdd (PConst 2%R) (PMul (PConst 3%R) (PConst 2%R)))
      demo_pstate = 8%R.
  Proof.
    cbn [pterm_eval].
    ring.
  Qed.

  Example probabilistic_formula_satisfaction_example :
    psatisfies demo_pstate (PFLe (PConst 2%R) (PConst 3%R)).
  Proof.
    cbn [psatisfies pterm_eval].
    lra.
  Qed.

  Example derived_probabilistic_connectives_satisfaction_example :
    psatisfies demo_pstate p_true /\
    psatisfies demo_pstate (p_not PFFalse) /\
    psatisfies demo_pstate (p_and p_true p_true) /\
    psatisfies demo_pstate (p_or PFFalse p_true) /\
    psatisfies demo_pstate (p_iff p_true p_true).
  Proof.
    cbn [p_true p_not p_and p_or p_iff psatisfies].
    tauto.
  Qed.

  Example uniform_distribution_validity_example :
    distribution_valid
      (Uniform (TConst 0%R) (TProgVar demo_real_program_var))
      demo_valuation.
  Proof.
    cbn [distribution_valid term_eval demo_valuation real_program_values].
    lra.
  Qed.

  Example laplace_distribution_validity_example :
    distribution_valid (Laplace (TConst 0%R) (TConst 1%R)) demo_valuation.
  Proof.
    cbn [distribution_valid term_eval].
    lra.
  Qed.

  Example gaussian_distribution_validity_example :
    distribution_valid (Gaussian (TConst 0%R) (TConst 1%R)) demo_valuation.
  Proof.
    cbn [distribution_valid term_eval].
    lra.
  Qed.
End ProbabilisticExamples.

(** The continuous probabilistic While-language syntax from
    [paper/cpWhile.tex].  Command nodes are intentionally permissive: toss
    probabilities and distribution parameters have no validity proof stored
    in the AST. Invalid parameters give zero command kernels; sampling
    proof rules retain their validity side conditions. *)
Inductive Cmd : Type :=
  | CSkip
  | CRealAssign (x : RealProgramVar) (t : Term)
  | CBoolAssign (b : BoolProgramVar) (beta : CFormula)
  | CBoolToss (b : BoolProgramVar) (r : R)
  | CRealSample (x : RealProgramVar) (d : Distribution)
  | CSeq (s1 s2 : Cmd)
  | CIf (beta : CFormula) (s1 s2 : Cmd)
  | CWhile (beta : CFormula) (body : Cmd).

(** Command denotations use subprobability kernels internally. Inputs remain
    ordinary measures; the admissibility proof is supplied to theorems only. *)
Module CommandSemantics.
  Import boot order ssralg ssrnum boolp classical_sets functions reals topology.
  Import ereal normedtype sequences esum measure measurable_realfun.
  Import lebesgue_integral lebesgue_stieltjes_measure kernel Rstruct Rstruct_topology.
  Import Order.TTheory GRing.Theory Num.Theory.
  Import numFieldTopology.Exports MeasurableR ValuationSpace DistributionSemantics.
  Local Notation real := [the realType of (Rdefinitions.R : Type)].
  Local Open Scope classical_set_scope.
  Local Open Scope ring_scope.
  Local Open Scope ereal_scope.
  Set Implicit Arguments.
  Unset Strict Implicit.

  (** These measurability witnesses belong in the shared layer because
      constructing a kernel needs them before any supporting file imports CPHL.
      The generated sigma-algebra reduces state maps to their coordinates. *)
  Lemma measurable_into_valuation d (X : measurableType d) (f : X -> Valuation) :
    (forall i, measurable_fun setT (real_coordinate i \o f)) ->
    (forall i, measurable_fun setT (bool_coordinate i \o f)) ->
    measurable_fun setT f.
  Proof.
  move=> mr mb.
  apply: (@measurability d _ X [the measurableType _ of Valuation]
            setT f valuation_generators erefl).
  move=> _ [A [ [i [U [mU ->] ] ]|[i [U [mU ->] ] ] ] <-].
  - exact: mr i measurableT U mU.
  - exact: mb i measurableT U mU.
  Qed.

  Lemma cformula_eval_bool_spec gamma v :
    cformula_eval_bool gamma v = true <-> satisfies v gamma.
  Proof.
  rewrite /cformula_eval_bool.
  case: (excluded_middle_informative (satisfies v gamma)) => h; split=> //.
  Qed.

  Lemma measurable_cformula_eval_bool gamma :
    measurable_fun [set: Valuation] (cformula_eval_bool gamma).
  Proof.
  apply: (measurable_fun_bool true); rewrite setTI.
  have -> : (cformula_eval_bool gamma @^-1` [set true]) = formula_event gamma.
    apply functional_extensionality; intro v.
    apply propext; exact: cformula_eval_bool_spec.
  exact: measurable_formula_event.
  Qed.

  (** Joint measurability is needed for sampling: the assigned value is an
      additional input coordinate, not a fixed constant. *)
  Lemma measurable_real_update x :
    measurable_fun [set: Valuation * real]
      (fun p => update_real p.1 x p.2 : Valuation).
  Proof.
  apply: measurable_into_valuation.
  - case=> y /=; rewrite /comp /real_coordinate /update_real /=.
    + rewrite /update_real_values.
      case: (real_program_var_eq_dec y x) => _.
      * exact: measurable_snd.
      * exact: measurableT_comp (measurable_real_coordinate (inl y)) measurable_fst.
    + exact: measurableT_comp (measurable_real_coordinate (inr y)) measurable_fst.
  - case=> b /=; rewrite /comp /bool_coordinate /update_real /=.
    + exact: measurableT_comp (measurable_bool_coordinate (inl b)) measurable_fst.
    + exact: measurableT_comp (measurable_bool_coordinate (inr b)) measurable_fst.
  Qed.

  Lemma measurable_bool_update b :
    measurable_fun [set: Valuation * bool]
      (fun p => update_bool p.1 b p.2 : Valuation).
  Proof.
  apply: measurable_into_valuation.
  - case=> x /=; rewrite /comp /real_coordinate /update_bool /=.
    + exact: measurableT_comp (measurable_real_coordinate (inl x)) measurable_fst.
    + exact: measurableT_comp (measurable_real_coordinate (inr x)) measurable_fst.
  - case=> c /=; rewrite /comp /bool_coordinate /update_bool /=.
    + rewrite /update_bool_values.
      case: (bool_program_var_eq_dec c b) => _.
      * exact: measurable_snd.
      * exact: measurableT_comp (measurable_bool_coordinate (inl c)) measurable_fst.
    + exact: measurableT_comp (measurable_bool_coordinate (inr c)) measurable_fst.
  Qed.

  (** Deterministic assignments evaluate their right-hand sides in the input
      state and then apply the jointly measurable update. *)
  Lemma measurable_real_assignment x t :
    measurable_fun [set: Valuation]
      (fun v => update_real v x (term_eval t v) : Valuation).
  Proof.
  exact (measurableT_comp (measurable_real_update x)
    (measurable_fun_pair
      (@measurable_id _ [the measurableType _ of Valuation] setT)
      (measurable_term t))).
  Qed.

  Lemma measurable_bool_assignment b gamma :
    measurable_fun [set: Valuation]
      (fun v => update_bool v b (cformula_eval_bool gamma v) : Valuation).
  Proof.
  exact (measurableT_comp (measurable_bool_update b)
    (measurable_fun_pair
      (@measurable_id _ [the measurableType _ of Valuation] setT)
      (measurable_cformula_eval_bool gamma))).
  Qed.

  Definition Kernel := real.-spker Valuation ~> Valuation.

  (** Dirac kernels implement deterministic updates of program coordinates. *)
  Definition skip : Valuation -> StateMeasure.carrier :=
    kdirac (@measurable_id _ [the measurableType _ of Valuation] setT).
  HB.instance Definition _ := ProbabilityKernel.on skip.
  Definition real_assign x t : Valuation -> StateMeasure.carrier :=
    kdirac (measurable_real_assignment x t).
  HB.instance Definition _ x t := ProbabilityKernel.on (real_assign x t).
  Definition bool_assign b gamma : Valuation -> StateMeasure.carrier :=
    kdirac (measurable_bool_assignment b gamma).
  HB.instance Definition _ b gamma := ProbabilityKernel.on (bool_assign b gamma).

  Definition real_update x : (Valuation * real) -> StateMeasure.carrier :=
    kdirac (measurable_real_update x).
  HB.instance Definition _ x := ProbabilityKernel.on (real_update x).
  Definition bool_update b : (Valuation * bool) -> StateMeasure.carrier :=
    kdirac (measurable_bool_update b).
  HB.instance Definition _ b := ProbabilityKernel.on (bool_update b).

  (** Parameterized composition keeps the incoming state available while
      drawing a value, so a distribution may mention the variable it replaces. *)
  Section Bind.
  Context {d} {Y : measurableType d}.
  Variables (l : real.-spker Valuation ~> Y)
            (k : real.-spker (Valuation * Y) ~> Valuation).
  Definition bind := mkcomp l k.
  HB.instance Definition _ := Kernel.on bind.
  Lemma bind_mass v : bind v setT <= 1.
  Proof.
  apply: (@le_trans _ _ (\int[l v]__ 1)); last first.
    by rewrite integral_cst// mul1e; exact: sprob_kernel_le1.
  apply: ge0_le_integral => //.
  - exact: measurableT_comp (measurable_kernel k _ measurableT) _.
  - by move=> y _; exact: sprob_kernel_le1.
  Qed.
  HB.instance Definition _ := Kernel_isSubProbability.Build _ _ _ _ _ bind
    ((sprob_kernelP bind).2 bind_mass).
  End Bind.

  Definition sample x d := bind [the real.-spker _ ~> _ of DistributionSemantics.real_law d]
      [the real.-spker _ ~> _ of real_update x].
  HB.instance Definition _ x d := SubProbabilityKernel.on (sample x d).
  Definition toss b r := bind [the real.-spker _ ~> _ of DistributionSemantics.bool_law (TConst r)]
      [the real.-spker _ ~> _ of bool_update b].
  HB.instance Definition _ b r := SubProbabilityKernel.on (toss b r).

  (** Lift a kernel to ignore an extra parameter. This is shared by sequence
      and the paper's transformer on input measures. *)
  Section After.
  Context {d} {X : measurableType d}.
  Variable k : Kernel.
  Definition after (p : X * Valuation) : StateMeasure.carrier := k p.2.
  Lemma after_measurable A : measurable A ->
    measurable_fun setT (after ^~ A).
  Proof.
  move=> mA; exact: measurableT_comp (measurable_kernel k _ mA) measurable_snd.
  Qed.
  HB.instance Definition _ := isKernel.Build _ _ _ _ _ after after_measurable.
  Lemma after_subprob : ereal_sup [set after p setT | p in setT] <= 1.
  Proof. by apply: ge_ereal_sup => _ [p _ <-]; exact: sprob_kernel_le1. Qed.
  HB.instance Definition _ := Kernel_isSubProbability.Build _ _ _ _ _ after after_subprob.
  End After.

  Definition sequence (k l : Kernel) := bind k [the real.-spker _ ~> _ of after l].
  HB.instance Definition _ k l := SubProbabilityKernel.on (sequence k l).

  (** Branch selection uses the pre-state guard and does not normalize mass. *)
  Definition branch gamma (k l : Kernel) (v : Valuation) : StateMeasure.carrier :=
    if cformula_eval_bool gamma v then k v else l v.
  Lemma branch_measurable gamma k l A : measurable A ->
    measurable_fun setT (branch gamma k l ^~ A).
  Proof.
  move=> mA.
  have -> : (branch gamma k l ^~ A) =
      (fun v => if cformula_eval_bool gamma v then k v A else l v A).
    by apply/funext => v; rewrite /branch; case: (cformula_eval_bool gamma v).
  apply: measurable_fun_ifT.
  - exact: measurable_cformula_eval_bool.
  - exact: measurable_kernel.
  - exact: measurable_kernel.
  Qed.
  HB.instance Definition _ gamma k l := isKernel.Build _ _ _ _ _
    (branch gamma k l) (branch_measurable gamma k l).
  Lemma branch_subprob gamma k l :
    ereal_sup [set branch gamma k l v setT | v in setT] <= 1.
  Proof.
  apply: ge_ereal_sup => _ [v _ <-]; rewrite /branch.
  by case: (cformula_eval_bool gamma v); exact: sprob_kernel_le1.
  Qed.
  HB.instance Definition _ gamma k l := Kernel_isSubProbability.Build _ _ _ _ _
    (branch gamma k l) (branch_subprob gamma k l).

  (** A failed or still-running finite approximation contributes no output. *)
  Definition zero : Valuation -> StateMeasure.carrier :=
    @kzero _ _ [the measurableType _ of Valuation] [the measurableType _ of Valuation] real.
  HB.instance Definition _ := Kernel.on zero.
  Lemma zero_subprob : ereal_sup [set zero v setT | v in setT] <= 1.
  Proof. by apply: ge_ereal_sup => _ [v _ <-]; rewrite /zero /kzero /mzero lee_fin ler01. Qed.
  HB.instance Definition _ := Kernel_isSubProbability.Build _ _ _ _ _ zero zero_subprob.

  (** Exit n counts exactly n completed body executions. Approx n counts
      exits after at most n executions; its recursive construction is already
      subprobabilistic, even when the body loses mass. *)
  Fixpoint loop_exit g (k : Kernel) (n : nat) : Kernel :=
    match n with
    | O => [the real.-spker _ ~> _ of branch g
        [the real.-spker _ ~> _ of zero] [the real.-spker _ ~> _ of skip]]
    | S n => [the real.-spker _ ~> _ of branch g
        [the real.-spker _ ~> _ of sequence k (loop_exit g k n)]
        [the real.-spker _ ~> _ of zero]]
    end.
  Fixpoint loop_approx g (k : Kernel) (n : nat) : Kernel :=
    match n with
    | O => loop_exit g k O
    | S n => [the real.-spker _ ~> _ of branch g
        [the real.-spker _ ~> _ of sequence k (loop_approx g k n)]
        [the real.-spker _ ~> _ of skip]]
    end.

  Lemma sequence_event k l v A : sequence k l v A = \int[k v]_w l w A.
  Proof. reflexivity. Qed.
  Lemma loop_exit0 g k v A : loop_exit g k O v A =
    if cformula_eval_bool g v then 0 else dirac v A.
  Proof.
  change ((if cformula_eval_bool g v then zero v else skip v) A =
    if cformula_eval_bool g v then 0 else dirac v A).
  by case: (cformula_eval_bool g v).
  Qed.
  Lemma loop_exitS g k n v A : loop_exit g k n.+1 v A =
    if cformula_eval_bool g v then \int[k v]_w loop_exit g k n w A else 0.
  Proof.
  change ((if cformula_eval_bool g v then sequence k (loop_exit g k n) v else zero v) A =
    if cformula_eval_bool g v then \int[k v]_w loop_exit g k n w A else 0).
  by case: (cformula_eval_bool g v).
  Qed.
  Lemma loop_approxS g k n v A : loop_approx g k n.+1 v A =
    if cformula_eval_bool g v then \int[k v]_w loop_approx g k n w A else dirac v A.
  Proof.
  change ((if cformula_eval_bool g v then sequence k (loop_approx g k n) v else skip v) A =
    if cformula_eval_bool g v then \int[k v]_w loop_approx g k n w A else dirac v A).
  by case: (cformula_eval_bool g v).
  Qed.

  (** This finite identity supplies the bound needed by the countable sum;
      no accounting hypothesis about an arbitrary exit sequence is assumed. *)
  Lemma loop_approx_sum g k n v A : measurable A ->
    loop_approx g k n v A = \sum_(i < n.+1) loop_exit g k i v A.
  Proof.
  move=> mA; elim: n v => [v|n ih v]; first by rewrite big_ord1.
  rewrite loop_approxS big_ord_recl loop_exit0.
  case hg: (cformula_eval_bool g v).
  - rewrite add0e.
    under eq_integral do rewrite ih.
    rewrite ge0_integral_sum//; first by move=> i; exact: measurable_kernel.
    by apply: eq_bigr => i _; rewrite loop_exitS hg.
  - rewrite (eq_bigr (fun _ => 0)); last by rewrite big1 ?adde0.
    by move=> i _; rewrite loop_exitS hg.
  Qed.

  Definition loop g (k : Kernel) :=
    kseries (fun n => (loop_exit g k n : real.-ker Valuation ~> Valuation)).
  HB.instance Definition _ g k := Kernel.on (loop g k).
  Lemma loop_mass g k v : loop g k v setT <= 1.
  Proof.
  apply: ConcreteMeasure.series_subprob => n.
  case: n => [|n].
  - change ((\sum_(i < 0) loop_exit g k i v setT) <= 1).
    by rewrite big_ord0 lee_fin ler01.
  - change ((\sum_(i < n.+1) loop_exit g k i v setT) <= 1).
    rewrite -loop_approx_sum//; exact: sprob_kernel_le1.
  Qed.
  HB.instance Definition _ g k := Kernel_isSubProbability.Build _ _ _ _ _
    (loop g k) ((sprob_kernelP (loop g k)).2 (loop_mass g k)).

  (** Total denotation on the shared syntax, including nested loops. The
      while branch uses the already-constructed denotation of its body. *)
  Fixpoint denote (c : Cmd) : Kernel :=
    match c with
    | CSkip => [the real.-spker _ ~> _ of skip]
    | CRealAssign x t => [the real.-spker _ ~> _ of real_assign x t]
    | CBoolAssign b g => [the real.-spker _ ~> _ of bool_assign b g]
    | CBoolToss b r => [the real.-spker _ ~> _ of toss b r]
    | CRealSample x d => [the real.-spker _ ~> _ of sample x d]
    | CSeq a b => [the real.-spker _ ~> _ of sequence (denote a) (denote b)]
    | CIf g a b => [the real.-spker _ ~> _ of branch g (denote a) (denote b)]
    | CWhile g body => [the real.-spker _ ~> _ of loop g (denote body)]
    end.

  (** Partial only at the syntax boundary: None reports a while anywhere in
      the command. No zero/identity placeholder is assigned to a loop. *)
  Fixpoint nonloop_kernel (c : Cmd) : option Kernel :=
    match c with
    | CSkip => Some [the real.-spker _ ~> _ of skip]
    | CRealAssign x t => Some [the real.-spker _ ~> _ of real_assign x t]
    | CBoolAssign b g => Some [the real.-spker _ ~> _ of bool_assign b g]
    | CBoolToss b r => Some [the real.-spker _ ~> _ of toss b r]
    | CRealSample x d => Some [the real.-spker _ ~> _ of sample x d]
    | CSeq a b =>
        match nonloop_kernel a, nonloop_kernel b with
        | Some k, Some l => Some [the real.-spker _ ~> _ of sequence k l]
        | _, _ => None
        end
    | CIf g a b =>
        match nonloop_kernel a, nonloop_kernel b with
        | Some k, Some l => Some [the real.-spker _ ~> _ of branch g k l]
        | _, _ => None
        end
    | CWhile _ _ => None
    end.

  Definition constant_kernel (mu : StateMeasure.carrier) (_ : unit) := mu.
  Lemma constant_kernel_measurable mu A : measurable A ->
    measurable_fun setT (constant_kernel mu ^~ A).
  Proof. by move=> _; exact: measurable_cst. Qed.
  HB.instance Definition _ mu := isKernel.Build _ _ _ _ _
    (constant_kernel mu) (constant_kernel_measurable mu).

  Definition transform (k : Kernel) (mu : StateMeasure.carrier) : StateMeasure.carrier :=
    mkcomp (constant_kernel mu) (after k) tt.
  Definition transform_pstate (k : Kernel) (ps : Pstate) : Pstate :=
    {| pstate_measure := transform k (pstate_measure ps);
       pstate_prob_logic_values := pstate_prob_logic_values ps |}.
  Definition run_nonloop (c : Cmd) (ps : Pstate) : option Pstate :=
    option_map (fun k => transform_pstate k ps) (nonloop_kernel c).
  Definition run (c : Cmd) (ps : Pstate) : Pstate := transform_pstate (denote c) ps.

  (** The paper's transformer for every command, including nested loops.
      Its input remains an ordinary measure; admissibility is proved separately. *)
  Definition transform_cmd (c : Cmd) (mu : StateMeasure.carrier) : StateMeasure.carrier :=
    transform (denote c) mu.

  (** The paper's forward iteration: restrict to the guard before executing
      the body. Exit measures remain unnormalized and may overlap as sets. *)
  Definition loop_step g k mu :=
    transform k (ConcreteMeasure.restrict mu (measurable_formula_event g)).
  Fixpoint loop_input g k n (mu : StateMeasure.carrier) : StateMeasure.carrier :=
    match n with
    | O => mu
    | S n => loop_step g k (loop_input g k n mu)
    end.
  Definition loop_output g k n mu : StateMeasure.carrier :=
    msum (fun i => ConcreteMeasure.restrict (loop_input g k i mu)
      (measurableC (measurable_formula_event g))) n.+1.
End CommandSemantics.

(** Compilation checks for each command form.  These are syntax examples
    only; they do not assign a denotation to commands. *)
Definition command_skip_example : Cmd := CSkip.

Definition command_real_assignment_example : Cmd :=
  CRealAssign demo_real_program_var (TConst 1%R).

Definition command_bool_assignment_example : Cmd :=
  CBoolAssign demo_bool_program_var
    (FLe (TProgVar demo_real_program_var) (TConst 0%R)).

Definition command_bool_toss_example : Cmd :=
  CBoolToss demo_bool_program_var (1 / 2)%R.

Definition command_real_sample_example : Cmd :=
  CRealSample demo_real_program_var
    (Gaussian (TConst 0%R) (TConst 1%R)).

Definition command_sequence_example : Cmd :=
  CSeq command_real_assignment_example command_bool_toss_example.

Definition command_conditional_example : Cmd :=
  CIf (FProgBool demo_bool_program_var)
    command_real_sample_example command_skip_example.

Definition command_while_example : Cmd :=
  CWhile (FProgBool demo_bool_program_var) command_real_assignment_example.

Example command_skip_is_well_typed : Cmd := command_skip_example.
Example command_real_assignment_is_well_typed : Cmd :=
  command_real_assignment_example.
Example command_bool_assignment_is_well_typed : Cmd :=
  command_bool_assignment_example.
Example command_bool_toss_is_well_typed : Cmd := command_bool_toss_example.
Example command_real_sample_is_well_typed : Cmd := command_real_sample_example.
Example command_sequence_is_well_typed : Cmd := command_sequence_example.
Example command_conditional_is_well_typed : Cmd := command_conditional_example.
Example command_while_is_well_typed : Cmd := command_while_example.

(** Syntactic support for the Hoare rules. *)

(** Strict comparison is a derived classical formula. *)
Definition c_lt (t1 t2 : Term) : CFormula :=
  c_not (FLe t2 t1).

(** Semantic premises quantify over all admissible joint measures and all
    external probabilistic assignments. Separate EPPL proof-system soundness
    (the assertion-validity interface associated with TAUT) is deferred. *)
Definition pformula_valid (eta : PFormula) : Prop :=
  forall ps : Pstate, pstate_admissible ps -> psatisfies ps eta.

(** Semantic Hoare validity quantifies over all admissible joint measures
    and all external probabilistic assignments. Classical logic coordinates
    may correlate with program coordinates. Divergence gives missing mass;
    even a zero output measure must satisfy the postcondition. No derivability
    or separate parameter-validity condition is built into this definition. *)
Definition hoare_valid (pre : PFormula) (c : Cmd) (post : PFormula) : Prop :=
  forall ps : Pstate, pstate_admissible ps -> psatisfies ps pre ->
    psatisfies (CommandSemantics.run c ps) post.

(** Classical validity interprets the paper's boxed side conditions. *)
Definition cformula_valid (gamma : CFormula) : Prop :=
  forall v : state, satisfies v gamma.

(** Analytical probabilistic syntax contains no expectation term. *)
Fixpoint pterm_analytical (p : Pterm) : Prop :=
  match p with
  | PVar _ | PConst _ => True
  | PExpect _ => False
  | PAdd p1 p2 | PMul p1 p2 =>
      pterm_analytical p1 /\ pterm_analytical p2
  end.

Fixpoint pformula_analytical (eta : PFormula) : Prop :=
  match eta with
  | PFLe p1 p2 => pterm_analytical p1 /\ pterm_analytical p2
  | PFFalse => True
  | PFImpl eta1 eta2 =>
      pformula_analytical eta1 /\ pformula_analytical eta2
  end.

(** Syntactic occurrence tests used by ELIMV. *)
Fixpoint prob_logic_var_occurs_pterm (y : ProbLogicVar) (p : Pterm) : Prop :=
  match p with
  | PVar y' => y = y'
  | PConst _ | PExpect _ => False
  | PAdd p1 p2 | PMul p1 p2 =>
      prob_logic_var_occurs_pterm y p1 \/
      prob_logic_var_occurs_pterm y p2
  end.

Fixpoint prob_logic_var_occurs_pformula
  (y : ProbLogicVar) (eta : PFormula) : Prop :=
  match eta with
  | PFLe p1 p2 =>
      prob_logic_var_occurs_pterm y p1 \/
      prob_logic_var_occurs_pterm y p2
  | PFFalse => False
  | PFImpl eta1 eta2 =>
      prob_logic_var_occurs_pformula y eta1 \/
      prob_logic_var_occurs_pformula y eta2
  end.

(** Real-program-variable occurrence lists.  Integral binders are included in
    [pconstruct_real_program_vars] so a generated name is fresh for both free
    and bound occurrences. *)
Fixpoint term_real_program_vars (t : Term) : list RealProgramVar :=
  match t with
  | TProgVar x => [x]
  | TLogicVar _ | TConst _ => []
  | TAdd t1 t2 | TMul t1 t2 =>
      term_real_program_vars t1 ++ term_real_program_vars t2
  end.

Fixpoint cformula_real_program_vars (gamma : CFormula) :
  list RealProgramVar :=
  match gamma with
  | FProgBool _ | FLogicBool _ | FFalse => []
  | FLe t1 t2 => term_real_program_vars t1 ++ term_real_program_vars t2
  | FImpl gamma1 gamma2 =>
      cformula_real_program_vars gamma1 ++
      cformula_real_program_vars gamma2
  end.

Definition distribution_real_program_vars (d : Distribution) :
  list RealProgramVar :=
  match d with
  | Uniform lower upper =>
      term_real_program_vars lower ++ term_real_program_vars upper
  | Laplace location scale =>
      term_real_program_vars location ++ term_real_program_vars scale
  | Gaussian mean standard_deviation =>
      term_real_program_vars mean ++
      term_real_program_vars standard_deviation
  end.

Fixpoint pconstruct_real_program_vars (q : PConstruct) :
  list RealProgramVar :=
  match q with
  | QIndicator gamma => cformula_real_program_vars gamma
  | QIntegral x d q' =>
      x :: distribution_real_program_vars d ++ pconstruct_real_program_vars q'
  end.

Fixpoint pconstruct_size (q : PConstruct) : nat :=
  match q with
  | QIndicator _ => 1
  | QIntegral _ _ q' => S (pconstruct_size q')
  end.

(** Fresh real-program-variable generation.  A name consisting solely of
    sufficiently many underscores is longer than every avoided identifier. *)
Fixpoint repeated_underscores (n : nat) : string :=
  match n with
  | O => EmptyString
  | S n' => String "_"%char (repeated_underscores n')
  end.

Lemma repeated_underscores_length :
  forall n : nat, String.length (repeated_underscores n) = n.
Proof.
  induction n as [| n IH]; cbn; [reflexivity | now rewrite IH].
Qed.

Definition real_program_var_name (x : RealProgramVar) : string :=
  match x with
  | real_program_var name => name
  end.

Fixpoint maximum_real_program_var_name_length
  (vars : list RealProgramVar) : nat :=
  match vars with
  | [] => O
  | x :: vars' =>
      Nat.max (String.length (real_program_var_name x))
        (maximum_real_program_var_name_length vars')
  end.

Definition fresh_real_program_var
  (avoid : list RealProgramVar) : RealProgramVar :=
  real_program_var
    (repeated_underscores
      (S (maximum_real_program_var_name_length avoid))).

Lemma real_program_var_name_length_le_maximum :
  forall (x : RealProgramVar) (avoid : list RealProgramVar),
    In x avoid ->
    (String.length (real_program_var_name x) <=
      maximum_real_program_var_name_length avoid)%nat.
Proof.
  intros x avoid Hx.
  induction avoid as [| a avoid IH]; cbn in Hx |- *.
  - contradiction.
  - destruct Hx as [Hx | Hx].
    + subst x. apply Nat.le_max_l.
    + eapply Nat.le_trans.
      * apply IH. exact Hx.
      * apply Nat.le_max_r.
Qed.

Lemma fresh_real_program_var_not_in :
  forall avoid : list RealProgramVar,
    ~ In (fresh_real_program_var avoid) avoid.
Proof.
  intros avoid Hfresh.
  pose proof
    (real_program_var_name_length_le_maximum
      (fresh_real_program_var avoid) avoid Hfresh) as Hbound.
  unfold fresh_real_program_var in Hbound.
  cbn in Hbound.
  rewrite repeated_underscores_length in Hbound.
  exact (Nat.nle_succ_diag_l _ Hbound).
Qed.

(** Renaming a real-program variable in terms, formulas, and distribution
    parameters. *)
Fixpoint rename_real_term
  (old fresh : RealProgramVar) (t : Term) : Term :=
  match t with
  | TProgVar x =>
      if real_program_var_eq_dec x old then TProgVar fresh else TProgVar x
  | TLogicVar x => TLogicVar x
  | TConst c => TConst c
  | TAdd t1 t2 =>
      TAdd (rename_real_term old fresh t1) (rename_real_term old fresh t2)
  | TMul t1 t2 =>
      TMul (rename_real_term old fresh t1) (rename_real_term old fresh t2)
  end.

Fixpoint rename_real_cformula
  (old fresh : RealProgramVar) (gamma : CFormula) : CFormula :=
  match gamma with
  | FProgBool b => FProgBool b
  | FLogicBool b => FLogicBool b
  | FLe t1 t2 =>
      FLe (rename_real_term old fresh t1) (rename_real_term old fresh t2)
  | FFalse => FFalse
  | FImpl gamma1 gamma2 =>
      FImpl (rename_real_cformula old fresh gamma1)
        (rename_real_cformula old fresh gamma2)
  end.

Definition rename_real_distribution
  (old fresh : RealProgramVar) (d : Distribution) : Distribution :=
  match d with
  | Uniform lower upper =>
      Uniform (rename_real_term old fresh lower)
        (rename_real_term old fresh upper)
  | Laplace location scale =>
      Laplace (rename_real_term old fresh location)
        (rename_real_term old fresh scale)
  | Gaussian mean standard_deviation =>
      Gaussian (rename_real_term old fresh mean)
        (rename_real_term old fresh standard_deviation)
  end.

(** Rename occurrences bound by an enclosing [QIntegral].  A nested integral
    using the same binder shadows the enclosing binder in its body, but not in
    its distribution parameters, which are evaluated in the outer state. *)
Fixpoint rename_bound_pconstruct
  (old fresh : RealProgramVar) (q : PConstruct) : PConstruct :=
  match q with
  | QIndicator gamma => QIndicator (rename_real_cformula old fresh gamma)
  | QIntegral x d q' =>
      let d' := rename_real_distribution old fresh d in
      if real_program_var_eq_dec x old
      then QIntegral x d' q'
      else QIntegral x d' (rename_bound_pconstruct old fresh q')
  end.

(** Capture-avoiding substitution of a real program variable by a term. *)
Fixpoint subst_real_term
  (x : RealProgramVar) (replacement : Term) (t : Term) : Term :=
  match t with
  | TProgVar x' =>
      if real_program_var_eq_dec x' x then replacement else TProgVar x'
  | TLogicVar y => TLogicVar y
  | TConst c => TConst c
  | TAdd t1 t2 =>
      TAdd (subst_real_term x replacement t1)
        (subst_real_term x replacement t2)
  | TMul t1 t2 =>
      TMul (subst_real_term x replacement t1)
        (subst_real_term x replacement t2)
  end.

Fixpoint subst_real_cformula
  (x : RealProgramVar) (replacement : Term) (gamma : CFormula) : CFormula :=
  match gamma with
  | FProgBool b => FProgBool b
  | FLogicBool b => FLogicBool b
  | FLe t1 t2 =>
      FLe (subst_real_term x replacement t1)
        (subst_real_term x replacement t2)
  | FFalse => FFalse
  | FImpl gamma1 gamma2 =>
      FImpl (subst_real_cformula x replacement gamma1)
        (subst_real_cformula x replacement gamma2)
  end.

Definition subst_real_distribution
  (x : RealProgramVar) (replacement : Term) (d : Distribution) : Distribution :=
  match d with
  | Uniform lower upper =>
      Uniform (subst_real_term x replacement lower)
        (subst_real_term x replacement upper)
  | Laplace location scale =>
      Laplace (subst_real_term x replacement location)
        (subst_real_term x replacement scale)
  | Gaussian mean standard_deviation =>
      Gaussian (subst_real_term x replacement mean)
        (subst_real_term x replacement standard_deviation)
  end.

(** The fuel is only used to make recursive calls after alpha-renaming
    acceptable to Rocq's termination checker; [S (pconstruct_size q)] is
    sufficient. *)
Fixpoint subst_real_pconstruct_fuel
  (fuel : nat) (x : RealProgramVar) (replacement : Term)
  (q : PConstruct) : PConstruct :=
  match fuel with
  | O => q
  | S fuel' =>
      match q with
      | QIndicator gamma => QIndicator (subst_real_cformula x replacement gamma)
      | QIntegral bound d q' =>
          let d' := subst_real_distribution x replacement d in
          if real_program_var_eq_dec bound x then QIntegral bound d' q'
          else if in_dec real_program_var_eq_dec bound
                    (term_real_program_vars replacement)
               then
                 let fresh :=
                   fresh_real_program_var
                     (pconstruct_real_program_vars q' ++
                      distribution_real_program_vars d ++
                      term_real_program_vars replacement ++ [x]) in
                 QIntegral fresh d'
                   (subst_real_pconstruct_fuel fuel' x replacement
                     (rename_bound_pconstruct bound fresh q'))
               else QIntegral bound d'
                      (subst_real_pconstruct_fuel fuel' x replacement q')
      end
  end.

Definition subst_real_pconstruct
  (x : RealProgramVar) (replacement : Term) (q : PConstruct) : PConstruct :=
  subst_real_pconstruct_fuel (S (pconstruct_size q)) x replacement q.

(** Classical formulas have no binders, so Boolean substitution is structural
    here. Its replacement can nevertheless contain real program variables. *)
Fixpoint subst_bool_cformula
  (b : BoolProgramVar) (replacement : CFormula) (gamma : CFormula) : CFormula :=
  match gamma with
  | FProgBool b' =>
      if bool_program_var_eq_dec b' b then replacement else FProgBool b'
  | FLogicBool b' => FLogicBool b'
  | FLe t1 t2 => FLe t1 t2
  | FFalse => FFalse
  | FImpl gamma1 gamma2 =>
      FImpl (subst_bool_cformula b replacement gamma1)
        (subst_bool_cformula b replacement gamma2)
  end.

(** A real binder must not capture the replacement's free real variables.
    Rename only its body; its own distribution is evaluated outside its scope.
    Avoid all body names (including nested binders), parameter names, and
    replacement names. Including [x] also makes the new binder distinct.
    Renaming preserves size, so the public wrapper supplies enough fuel. *)
Fixpoint subst_bool_pconstruct_fuel
  (fuel : nat) (b : BoolProgramVar) (replacement : CFormula)
  (q : PConstruct) : PConstruct :=
  match fuel with
  | O => q
  | S fuel' =>
      match q with
      | QIndicator gamma => QIndicator (subst_bool_cformula b replacement gamma)
      | QIntegral x d q' =>
          if in_dec real_program_var_eq_dec x
               (cformula_real_program_vars replacement)
          then
            let fresh := fresh_real_program_var
              (x :: pconstruct_real_program_vars q' ++
                distribution_real_program_vars d ++
                cformula_real_program_vars replacement) in
            QIntegral fresh d
              (subst_bool_pconstruct_fuel fuel' b replacement
                (rename_bound_pconstruct x fresh q'))
          else QIntegral x d (subst_bool_pconstruct_fuel fuel' b replacement q')
      end
  end.

Definition subst_bool_pconstruct
  (b : BoolProgramVar) (replacement : CFormula) (q : PConstruct) : PConstruct :=
  subst_bool_pconstruct_fuel (S (pconstruct_size q)) b replacement q.

(** Conditioning an expectation must preserve the outer value of a guard.
    Any integral binder occurring in that guard is alpha-renamed before the
    guard is introduced below the binder. *)
Fixpoint condition_pconstruct_fuel
  (fuel : nat) (q : PConstruct) (guard : CFormula) : PConstruct :=
  match fuel with
  | O => q
  | S fuel' =>
      match q with
      | QIndicator gamma => QIndicator (c_and gamma guard)
      | QIntegral x d q' =>
          if in_dec real_program_var_eq_dec x
               (cformula_real_program_vars guard)
          then
            let fresh :=
              fresh_real_program_var
                (pconstruct_real_program_vars q' ++
                 distribution_real_program_vars d ++
                 cformula_real_program_vars guard) in
            QIntegral fresh d
              (condition_pconstruct_fuel fuel'
                (rename_bound_pconstruct x fresh q') guard)
          else QIntegral x d (condition_pconstruct_fuel fuel' q' guard)
      end
  end.

Definition condition_pconstruct
  (q : PConstruct) (guard : CFormula) : PConstruct :=
  condition_pconstruct_fuel (S (pconstruct_size q)) q guard.

Fixpoint subst_real_pterm
  (x : RealProgramVar) (replacement : Term) (p : Pterm) : Pterm :=
  match p with
  | PVar y => PVar y
  | PConst r => PConst r
  | PExpect q => PExpect (subst_real_pconstruct x replacement q)
  | PAdd p1 p2 =>
      PAdd (subst_real_pterm x replacement p1)
        (subst_real_pterm x replacement p2)
  | PMul p1 p2 =>
      PMul (subst_real_pterm x replacement p1)
        (subst_real_pterm x replacement p2)
  end.

Fixpoint subst_real_pformula
  (x : RealProgramVar) (replacement : Term) (eta : PFormula) : PFormula :=
  match eta with
  | PFLe p1 p2 =>
      PFLe (subst_real_pterm x replacement p1)
        (subst_real_pterm x replacement p2)
  | PFFalse => PFFalse
  | PFImpl eta1 eta2 =>
      PFImpl (subst_real_pformula x replacement eta1)
        (subst_real_pformula x replacement eta2)
  end.

Fixpoint subst_bool_pterm
  (b : BoolProgramVar) (replacement : CFormula) (p : Pterm) : Pterm :=
  match p with
  | PVar y => PVar y
  | PConst r => PConst r
  | PExpect q => PExpect (subst_bool_pconstruct b replacement q)
  | PAdd p1 p2 =>
      PAdd (subst_bool_pterm b replacement p1)
        (subst_bool_pterm b replacement p2)
  | PMul p1 p2 =>
      PMul (subst_bool_pterm b replacement p1)
        (subst_bool_pterm b replacement p2)
  end.

Fixpoint subst_bool_pformula
  (b : BoolProgramVar) (replacement : CFormula) (eta : PFormula) : PFormula :=
  match eta with
  | PFLe p1 p2 =>
      PFLe (subst_bool_pterm b replacement p1)
        (subst_bool_pterm b replacement p2)
  | PFFalse => PFFalse
  | PFImpl eta1 eta2 =>
      PFImpl (subst_bool_pformula b replacement eta1)
        (subst_bool_pformula b replacement eta2)
  end.

Fixpoint subst_prob_pterm
  (y : ProbLogicVar) (replacement : Pterm) (p : Pterm) : Pterm :=
  match p with
  | PVar y' => if prob_logic_var_eq_dec y' y then replacement else PVar y'
  | PConst r => PConst r
  | PExpect q => PExpect q
  | PAdd p1 p2 =>
      PAdd (subst_prob_pterm y replacement p1)
        (subst_prob_pterm y replacement p2)
  | PMul p1 p2 =>
      PMul (subst_prob_pterm y replacement p1)
        (subst_prob_pterm y replacement p2)
  end.

Fixpoint subst_prob_pformula
  (y : ProbLogicVar) (replacement : Pterm) (eta : PFormula) : PFormula :=
  match eta with
  | PFLe p1 p2 =>
      PFLe (subst_prob_pterm y replacement p1)
        (subst_prob_pterm y replacement p2)
  | PFFalse => PFFalse
  | PFImpl eta1 eta2 =>
      PFImpl (subst_prob_pformula y replacement eta1)
        (subst_prob_pformula y replacement eta2)
  end.

(** Weakest-precondition syntax transformations for toss and sampling. *)
Fixpoint toss_pterm (b : BoolProgramVar) (r : R) (p : Pterm) : Pterm :=
  match p with
  | PVar y => PVar y
  | PConst c => PConst c
  | PExpect q =>
      PAdd
        (PMul (PConst r) (PExpect (subst_bool_pconstruct b c_true q)))
        (PMul (PConst (1 - r)%R) (PExpect (subst_bool_pconstruct b FFalse q)))
  | PAdd p1 p2 => PAdd (toss_pterm b r p1) (toss_pterm b r p2)
  | PMul p1 p2 => PMul (toss_pterm b r p1) (toss_pterm b r p2)
  end.

Fixpoint toss_pformula (b : BoolProgramVar) (r : R) (eta : PFormula) :
  PFormula :=
  match eta with
  | PFLe p1 p2 => PFLe (toss_pterm b r p1) (toss_pterm b r p2)
  | PFFalse => PFFalse
  | PFImpl eta1 eta2 =>
      PFImpl (toss_pformula b r eta1) (toss_pformula b r eta2)
  end.

Fixpoint sample_pterm (x : RealProgramVar) (d : Distribution) (p : Pterm) :
  Pterm :=
  match p with
  | PVar y => PVar y
  | PConst r => PConst r
  | PExpect q => PExpect (QIntegral x d q)
  | PAdd p1 p2 => PAdd (sample_pterm x d p1) (sample_pterm x d p2)
  | PMul p1 p2 => PMul (sample_pterm x d p1) (sample_pterm x d p2)
  end.

Fixpoint sample_pformula
  (x : RealProgramVar) (d : Distribution) (eta : PFormula) : PFormula :=
  match eta with
  | PFLe p1 p2 => PFLe (sample_pterm x d p1) (sample_pterm x d p2)
  | PFFalse => PFFalse
  | PFImpl eta1 eta2 =>
      PFImpl (sample_pformula x d eta1) (sample_pformula x d eta2)
  end.

Fixpoint condition_pterm (p : Pterm) (guard : CFormula) : Pterm :=
  match p with
  | PVar y => PVar y
  | PConst r => PConst r
  | PExpect q => PExpect (condition_pconstruct q guard)
  | PAdd p1 p2 =>
      PAdd (condition_pterm p1 guard) (condition_pterm p2 guard)
  | PMul p1 p2 =>
      PMul (condition_pterm p1 guard) (condition_pterm p2 guard)
  end.

Fixpoint condition_pformula (eta : PFormula) (guard : CFormula) : PFormula :=
  match eta with
  | PFLe p1 p2 => PFLe (condition_pterm p1 guard) (condition_pterm p2 guard)
  | PFFalse => PFFalse
  | PFImpl eta1 eta2 =>
      PFImpl (condition_pformula eta1 guard) (condition_pformula eta2 guard)
  end.

Definition if_precondition
  (eta1 eta2 : PFormula) (guard : CFormula) : PFormula :=
  p_and (condition_pformula eta1 guard)
    (condition_pformula eta2 (c_not guard)).

(** SUM splits the input into unnormalized restrictions. Coverage is an
    assertion about this input; disjointness is a separate classical premise. *)
Definition sum_precondition
  (eta1 eta2 : PFormula) (gamma1 gamma2 : CFormula) : PFormula :=
  p_and
    (p_and (condition_pformula eta1 gamma1)
      (condition_pformula eta2 gamma2))
    (p_almost_sure (c_or gamma1 gamma2)).

(** Bounded families used by the while rule are total functions on [nat].
    These folds observe exactly the entries with indices below [m]. *)
Fixpoint finite_c_or (m : nat) (formulas : nat -> CFormula) : CFormula :=
  match m with
  | O => FFalse
  | S m' => c_or (finite_c_or m' formulas) (formulas m')
  end.

Fixpoint finite_p_and (m : nat) (formulas : nat -> PFormula) : PFormula :=
  match m with
  | O => p_true
  | S m' => p_and (finite_p_and m' formulas) (formulas m')
  end.

Fixpoint finite_r_sum (m : nat) (terms : nat -> R) : R :=
  match m with
  | O => 0%R
  | S m' => (finite_r_sum m' terms + terms m')%R
  end.

(** All mass is concentrated on [gamma], and its total amount is [mass]. *)
Definition p_concentrated_mass (gamma : CFormula) (mass : Pterm) : PFormula :=
  p_and
    (p_eq (PExpect (QIndicator gamma))
      (PExpect (QIndicator c_true)))
    (p_eq (PExpect (QIndicator c_true)) mass).

(** Concentration is exact even when the total mass is only bounded. These
    formulas admit zero mass and do not normalize the input. *)
Definition p_concentrated_mass_upper
  (gamma : CFormula) (mass : Pterm) : PFormula :=
  p_and (p_almost_sure gamma)
    (PFLe (PExpect (QIndicator c_true)) mass).

Definition p_concentrated_mass_lower
  (gamma : CFormula) (mass : Pterm) : PFormula :=
  p_and (p_almost_sure gamma)
    (PFLe mass (PExpect (QIndicator c_true))).

(** Exact transition masses and exit reward produced by one loop-body step.
    The exit expectation is not generally the total probability of exiting. *)
Definition while_body_post
  (m : nat) (regions : nat -> CFormula) (transition_row : nat -> R)
  (beta : CFormula) (q : PConstruct) (exit : R) : PFormula :=
  p_and
    (finite_p_and m
      (fun j =>
        p_eq (PExpect (QIndicator (regions j)))
          (PConst (transition_row j))))
    (p_eq (PExpect (condition_pconstruct q (c_not beta))) (PConst exit)).

(** One-sided body certificates use the same conditioned reward as [HWhile].
    Bounds apply simultaneously to every region and to the exit reward. *)
Definition while_body_post_upper
  (m : nat) (regions : nat -> CFormula) (transition_row : nat -> R)
  (beta : CFormula) (q : PConstruct) (exit : R) : PFormula :=
  p_and
    (finite_p_and m
      (fun j =>
        PFLe (PExpect (QIndicator (regions j)))
          (PConst (transition_row j))))
    (PFLe (PExpect (condition_pconstruct q (c_not beta))) (PConst exit)).

Definition while_body_post_lower
  (m : nat) (regions : nat -> CFormula) (transition_row : nat -> R)
  (beta : CFormula) (q : PConstruct) (exit : R) : PFormula :=
  p_and
    (finite_p_and m
      (fun j =>
        PFLe (PConst (transition_row j))
          (PExpect (QIndicator (regions j)))))
    (PFLe (PConst exit) (PExpect (condition_pconstruct q (c_not beta)))).

(** Together these three conditions give the partition used by [HWhile].
    The upper rule needs only coverage; the lower rule needs only containment
    and disjointness. All three conditions are globally classically valid. *)
Definition while_regions_cover
  (m : nat) (beta : CFormula) (regions : nat -> CFormula) : Prop :=
  cformula_valid (FImpl beta (finite_c_or m regions)).

Definition while_regions_in_guard
  (m : nat) (beta : CFormula) (regions : nat -> CFormula) : Prop :=
  forall i : nat,
    (i < m)%nat -> cformula_valid (FImpl (regions i) beta).

(** Quantifying only [j < i] checks each unordered pair exactly once. *)
Definition while_regions_disjoint
  (m : nat) (regions : nat -> CFormula) : Prop :=
  forall i j : nat,
    (i < m)%nat -> (j < i)%nat ->
    cformula_valid (c_not (c_and (regions i) (regions j))).

(** Every region has positive exit reward or a positive transition to an
    earlier region. This selects a lower/exact certificate; upper bounds do
    not require progress. It does not assert almost-sure termination. *)
Definition while_progress
  (m : nat) (transitions : nat -> nat -> R) (exits : nat -> R) : Prop :=
  forall i : nat,
    (i < m)%nat ->
    (0 < exits i)%R \/
    exists j : nat, (j < i)%nat /\ (0 < transitions i j)%R.

(** [solution] is a bounded fixed point of the certificate's linear system. *)
Definition while_solution
  (m : nat) (solution : nat -> R) (transitions : nat -> nat -> R)
  (exits : nat -> R) : Prop :=
  forall i : nat,
    (i < m)%nat ->
    solution i =
      (finite_r_sum m (fun j => transitions i j * solution j) + exits i)%R /\
    (0 <= solution i <= 1)%R.

(** Upper certificates satisfy R*x+r <= x; lower certificates satisfy the
    reverse inequality and additionally need [while_progress] in their rule.
    Coefficients remain arbitrary reals, as for [while_solution]. Soundness
    of lower certificates uses their nonnegative parts on nonempty regions;
    empty-region body premises must not be used to infer row bounds. *)
Definition while_upper_solution
  (m : nat) (solution : nat -> R) (transitions : nat -> nat -> R)
  (exits : nat -> R) : Prop :=
  forall i : nat,
    (i < m)%nat ->
    (finite_r_sum m (fun j => transitions i j * solution j) + exits i <=
      solution i)%R /\ (0 <= solution i <= 1)%R.

Definition while_lower_solution
  (m : nat) (solution : nat -> R) (transitions : nat -> nat -> R)
  (exits : nat -> R) : Prop :=
  forall i : nat,
    (i < m)%nat ->
    (solution i <=
      finite_r_sum m (fun j => transitions i j * solution j) + exits i)%R /\
    (0 <= solution i <= 1)%R.

(** A classical formula expressing when a distribution is well formed. *)
Definition distribution_valid_formula (d : Distribution) : CFormula :=
  match d with
  | Uniform lower upper => c_lt lower upper
  | Laplace _ scale => c_lt (TConst 0%R) scale
  | Gaussian _ standard_deviation =>
      c_lt (TConst 0%R) standard_deviation
  end.

Theorem distribution_valid_formula_spec :
  forall (d : Distribution) (v : state),
    satisfies v (distribution_valid_formula d) <-> distribution_valid d v.
Proof.
  intros d v.
  destruct d; cbn [distribution_valid_formula distribution_valid c_lt c_not
    satisfies term_eval].
  all: split; intro H; lra.
Qed.

Definition coin_probability_valid (r : R) : Prop :=
  (0 <= r /\ r <= 1)%R.

(** Scoped surface syntax for the CPHL abstract syntax trees.  The coercions
    below only embed already-typed variables and real constants into the
    corresponding syntax category; strings and semantic assertions remain
    explicit. *)
Coercion TProgVar : RealProgramVar >-> Term.
Coercion TLogicVar : RealLogicVar >-> Term.
Coercion TConst : R >-> Term.
Coercion FProgBool : BoolProgramVar >-> CFormula.
Coercion FLogicBool : BoolLogicVar >-> CFormula.
Coercion PVar : ProbLogicVar >-> Pterm.
Coercion PConst : R >-> Pterm.

Declare Custom Entry cphl_expr.
Declare Custom Entry cphl_prob.
Declare Scope cphl_scope.
Delimit Scope cphl_scope with cphl.

(** [cphl_expr] contains terms, classical formulas, distributions, and
    commands.  [cphl_prob] contains probability constructs, terms, and
    formulas.  The dollar form splices an arbitrary Rocq expression into a
    custom entry. *)
Notation "<{ e }>" := e
  (e custom cphl_expr at level 99) : cphl_scope.
Notation "[[ e ]]" := e
  (e custom cphl_prob at level 99) : cphl_scope.

Notation "( x )" := x
  (in custom cphl_expr at level 0, x at level 99) : cphl_scope.
Notation "x" := x
  (in custom cphl_expr at level 0, x constr at level 0) : cphl_scope.
Notation "'$' ( x )" := x
  (in custom cphl_expr at level 0, x constr at level 200) : cphl_scope.

(** Real terms. *)
Notation "x * y" := (TMul x y)
  (in custom cphl_expr at level 40, left associativity) : cphl_scope.
Notation "x + y" := (TAdd x y)
  (in custom cphl_expr at level 50, left associativity) : cphl_scope.

(** Classical formulas. *)
Notation "'false'" := FFalse
  (in custom cphl_expr at level 0) : cphl_scope.
Notation "'true'" := c_true
  (in custom cphl_expr at level 0) : cphl_scope.
Notation "x <= y" := (FLe x y)
  (in custom cphl_expr at level 60, no associativity) : cphl_scope.
Notation "x < y" := (c_lt x y)
  (in custom cphl_expr at level 60, no associativity) : cphl_scope.
Notation "x = y" := (c_and (FLe x y) (FLe y x))
  (in custom cphl_expr at level 60, no associativity) : cphl_scope.
Notation "x >= y" := (FLe y x)
  (in custom cphl_expr at level 60, no associativity) : cphl_scope.
Notation "x > y" := (c_lt y x)
  (in custom cphl_expr at level 60, no associativity) : cphl_scope.
Notation "'~' x" := (c_not x)
  (in custom cphl_expr at level 70, right associativity) : cphl_scope.
Notation "x /\ y" := (c_and x y)
  (in custom cphl_expr at level 75, right associativity) : cphl_scope.
Notation "x \/ y" := (c_or x y)
  (in custom cphl_expr at level 80, right associativity) : cphl_scope.
Notation "x -> y" := (FImpl x y)
  (in custom cphl_expr at level 85, right associativity) : cphl_scope.
Notation "x <-> y" := (c_iff x y)
  (in custom cphl_expr at level 86, no associativity) : cphl_scope.

(** Continuous distributions. *)
Notation "'uniform' ( lower , upper )" := (Uniform lower upper)
  (in custom cphl_expr at level 0,
   lower custom cphl_expr at level 88,
   upper custom cphl_expr at level 88) : cphl_scope.
Notation "'laplace' ( location , scale )" := (Laplace location scale)
  (in custom cphl_expr at level 0,
   location custom cphl_expr at level 88,
   scale custom cphl_expr at level 88) : cphl_scope.
Notation "'gaussian' ( mean , deviation )" := (Gaussian mean deviation)
  (in custom cphl_expr at level 0,
   mean custom cphl_expr at level 88,
   deviation custom cphl_expr at level 88) : cphl_scope.

(** Commands.  Boolean assignment retains the old formalization's distinct
    [b=] token so real and Boolean assignment remain unambiguous. *)
Notation "'skip'" := CSkip
  (in custom cphl_expr at level 0) : cphl_scope.
Notation "x := t" := (CRealAssign x t)
  (in custom cphl_expr at level 0,
   x constr at level 0, t custom cphl_expr at level 88,
   no associativity) : cphl_scope.
Notation "b 'b=' beta" := (CBoolAssign b beta)
  (in custom cphl_expr at level 0,
   b constr at level 0, beta custom cphl_expr at level 88,
   no associativity) : cphl_scope.
Notation "b 'toss' r" := (CBoolToss b r)
  (in custom cphl_expr at level 0,
   b constr at level 0, r custom cphl_expr at level 0,
   no associativity) : cphl_scope.
Notation "x 'sample' d" := (CRealSample x d)
  (in custom cphl_expr at level 0,
   x constr at level 0, d custom cphl_expr at level 0,
   no associativity) : cphl_scope.
Notation "'if' beta 'then' s1 'else' s2 'end'" := (CIf beta s1 s2)
  (in custom cphl_expr at level 89,
   beta custom cphl_expr at level 88,
   s1 custom cphl_expr at level 99,
   s2 custom cphl_expr at level 99) : cphl_scope.
Notation "'while' beta 'do' body 'end'" := (CWhile beta body)
  (in custom cphl_expr at level 89,
   beta custom cphl_expr at level 88,
   body custom cphl_expr at level 99) : cphl_scope.
Notation "s1 ; s2" := (CSeq s1 s2)
  (in custom cphl_expr at level 90, right associativity) : cphl_scope.

Notation "( x )" := x
  (in custom cphl_prob at level 0, x at level 99) : cphl_scope.
Notation "x" := x
  (in custom cphl_prob at level 0, x constr at level 0) : cphl_scope.
Notation "'$' ( x )" := x
  (in custom cphl_prob at level 0, x constr at level 200) : cphl_scope.

(** Probability constructs and terms. *)
Notation "'indicator' [ gamma ]" := (QIndicator gamma)
  (in custom cphl_prob at level 0,
   gamma custom cphl_expr at level 99) : cphl_scope.
Notation "'integral' x '~' d ',' q" := (QIntegral x d q)
  (in custom cphl_prob at level 90, right associativity,
   x constr at level 0,
   d custom cphl_expr at level 0,
   q custom cphl_prob at level 90) : cphl_scope.
Notation "'E' [ q ]" := (PExpect q)
  (in custom cphl_prob at level 0,
   q custom cphl_prob at level 99) : cphl_scope.
Notation "'Pr' [ gamma ]" := (PExpect (QIndicator gamma))
  (in custom cphl_prob at level 0,
   gamma custom cphl_expr at level 99) : cphl_scope.
Notation "x * y" := (PMul x y)
  (in custom cphl_prob at level 40, left associativity) : cphl_scope.
Notation "x + y" := (PAdd x y)
  (in custom cphl_prob at level 50, left associativity) : cphl_scope.

(** Probabilistic formulas. *)
Notation "'false'" := PFFalse
  (in custom cphl_prob at level 0) : cphl_scope.
Notation "'true'" := p_true
  (in custom cphl_prob at level 0) : cphl_scope.
Notation "x <= y" := (PFLe x y)
  (in custom cphl_prob at level 60, no associativity) : cphl_scope.
Notation "x < y" := (p_lt x y)
  (in custom cphl_prob at level 60, no associativity) : cphl_scope.
Notation "x = y" := (p_eq x y)
  (in custom cphl_prob at level 60, no associativity) : cphl_scope.
Notation "x >= y" := (PFLe y x)
  (in custom cphl_prob at level 60, no associativity) : cphl_scope.
Notation "x > y" := (p_lt y x)
  (in custom cphl_prob at level 60, no associativity) : cphl_scope.
Notation "'almost_sure' [ gamma ]" := (p_almost_sure gamma)
  (in custom cphl_prob at level 0,
   gamma custom cphl_expr at level 99) : cphl_scope.
Notation "'~' x" := (p_not x)
  (in custom cphl_prob at level 70, right associativity) : cphl_scope.
Notation "x /\ y" := (p_and x y)
  (in custom cphl_prob at level 75, right associativity) : cphl_scope.
Notation "x \/ y" := (p_or x y)
  (in custom cphl_prob at level 80, right associativity) : cphl_scope.
Notation "x -> y" := (PFImpl x y)
  (in custom cphl_prob at level 85, right associativity) : cphl_scope.
Notation "x <-> y" := (p_iff x y)
  (in custom cphl_prob at level 86, no associativity) : cphl_scope.

(** The paper's syntactic Hoare calculus, extended with one-sided while
    certificates from the old paper for bounded construct rewards. The
    preconditions and postconditions remain syntactic formulas; semantic
    validity is used only for rule side conditions. *)
Inductive hoare_derivable : PFormula -> Cmd -> PFormula -> Prop :=
  | HFree :
      forall (eta : PFormula) (s : Cmd),
        pformula_analytical eta ->
        hoare_derivable eta s eta
  | HSkip :
      forall eta : PFormula,
        hoare_derivable eta CSkip eta
  | HRealAssign :
      forall (eta : PFormula) (x : RealProgramVar) (t : Term),
        hoare_derivable (subst_real_pformula x t eta)
          (CRealAssign x t) eta
  | HBoolAssign :
      forall (eta : PFormula) (b : BoolProgramVar) (beta : CFormula),
        hoare_derivable (subst_bool_pformula b beta eta)
          (CBoolAssign b beta) eta
  | HBoolToss :
      forall (eta : PFormula) (b : BoolProgramVar) (r : R),
        coin_probability_valid r ->
        hoare_derivable (toss_pformula b r eta) (CBoolToss b r) eta
  | HRealSample :
      forall (pre eta : PFormula) (x : RealProgramVar) (d : Distribution),
        pformula_valid (PFImpl pre (sample_pformula x d eta)) ->
        pformula_valid
          (PFImpl pre
            (p_almost_sure (distribution_valid_formula d))) ->
        hoare_derivable pre (CRealSample x d) eta
  | HIfLe :
      forall (eta1 eta2 : PFormula) (guard gamma : CFormula)
        (y1 y2 : ProbLogicVar) (s1 s2 : Cmd),
        hoare_derivable eta1 s1
          (PFLe (PVar y1) (PExpect (QIndicator gamma))) ->
        hoare_derivable eta2 s2
          (PFLe (PVar y2) (PExpect (QIndicator gamma))) ->
        hoare_derivable (if_precondition eta1 eta2 guard)
          (CIf guard s1 s2)
          (PFLe (PAdd (PVar y1) (PVar y2))
            (PExpect (QIndicator gamma)))
  | HIfGe :
      forall (eta1 eta2 : PFormula) (guard gamma : CFormula)
        (y1 y2 : ProbLogicVar) (s1 s2 : Cmd),
        hoare_derivable eta1 s1
          (PFLe (PExpect (QIndicator gamma)) (PVar y1)) ->
        hoare_derivable eta2 s2
          (PFLe (PExpect (QIndicator gamma)) (PVar y2)) ->
        hoare_derivable (if_precondition eta1 eta2 guard)
          (CIf guard s1 s2)
          (PFLe (PExpect (QIndicator gamma))
            (PAdd (PVar y1) (PVar y2)))
  | HIfEq :
      forall (eta1 eta2 : PFormula) (guard gamma : CFormula)
        (y1 y2 : ProbLogicVar) (s1 s2 : Cmd),
        hoare_derivable eta1 s1
          (p_eq (PVar y1) (PExpect (QIndicator gamma))) ->
        hoare_derivable eta2 s2
          (p_eq (PVar y2) (PExpect (QIndicator gamma))) ->
        hoare_derivable (if_precondition eta1 eta2 guard)
          (CIf guard s1 s2)
          (p_eq (PAdd (PVar y1) (PVar y2))
            (PExpect (QIndicator gamma)))
  | HElimv :
      forall (eta1 eta2 : PFormula) (y : ProbLogicVar) (p : Pterm) (s : Cmd),
        hoare_derivable (p_and eta1 (p_eq (PVar y) p)) s eta2 ->
        ~ prob_logic_var_occurs_pterm y p ->
        ~ prob_logic_var_occurs_pformula y eta2 ->
        hoare_derivable (subst_prob_pformula y p eta1) s eta2
  | HSeq :
      forall (eta1 eta2 eta3 : PFormula) (s1 s2 : Cmd),
        hoare_derivable eta1 s1 eta2 ->
        hoare_derivable eta2 s2 eta3 ->
        hoare_derivable eta1 (CSeq s1 s2) eta3
  | HConseq :
      forall (eta0 eta1 eta2 eta3 : PFormula) (s : Cmd),
        pformula_valid (PFImpl eta0 eta1) ->
        hoare_derivable eta1 s eta2 ->
        pformula_valid (PFImpl eta2 eta3) ->
        hoare_derivable eta0 s eta3
  | HOr :
      forall (eta0 eta1 eta2 : PFormula) (s : Cmd),
        hoare_derivable eta0 s eta2 ->
        hoare_derivable eta1 s eta2 ->
        hoare_derivable (p_or eta0 eta1) s eta2
  | HAnd :
      forall (eta0 eta1 eta2 : PFormula) (s : Cmd),
        hoare_derivable eta0 s eta1 ->
        hoare_derivable eta0 s eta2 ->
        hoare_derivable eta0 s (p_and eta1 eta2)
  (** SUM runs the same command on two disjoint input pieces. As in [HIfLe]
      and [HIfGe], Le/Ge name the comparison with the bound on the left. *)
  | HSumLe :
      forall (eta1 eta2 : PFormula) (gamma1 gamma2 gamma : CFormula)
        (y1 y2 : ProbLogicVar) (s : Cmd),
        cformula_valid (c_not (c_and gamma1 gamma2)) ->
        hoare_derivable (p_and eta1 (p_almost_sure gamma1)) s
          (PFLe (PVar y1) (PExpect (QIndicator gamma))) ->
        hoare_derivable (p_and eta2 (p_almost_sure gamma2)) s
          (PFLe (PVar y2) (PExpect (QIndicator gamma))) ->
        hoare_derivable (sum_precondition eta1 eta2 gamma1 gamma2) s
          (PFLe (PAdd (PVar y1) (PVar y2))
            (PExpect (QIndicator gamma)))
  | HSumGe :
      forall (eta1 eta2 : PFormula) (gamma1 gamma2 gamma : CFormula)
        (y1 y2 : ProbLogicVar) (s : Cmd),
        cformula_valid (c_not (c_and gamma1 gamma2)) ->
        hoare_derivable (p_and eta1 (p_almost_sure gamma1)) s
          (PFLe (PExpect (QIndicator gamma)) (PVar y1)) ->
        hoare_derivable (p_and eta2 (p_almost_sure gamma2)) s
          (PFLe (PExpect (QIndicator gamma)) (PVar y2)) ->
        hoare_derivable (sum_precondition eta1 eta2 gamma1 gamma2) s
          (PFLe (PExpect (QIndicator gamma))
            (PAdd (PVar y1) (PVar y2)))
  | HWhileNot :
      forall (gamma beta : CFormula) (body : Cmd) (y : ProbLogicVar),
        cformula_valid (FImpl gamma (c_not beta)) ->
        hoare_derivable
          (p_concentrated_mass gamma (PVar y))
          (CWhile beta body)
          (p_concentrated_mass gamma (PVar y))
  | HWhile :
      forall (m k : nat) (beta : CFormula) (body : Cmd) (q : PConstruct)
        (regions : nat -> CFormula) (solution exits : nat -> R)
        (transitions : nat -> nat -> R) (y : ProbLogicVar),
        (k < m)%nat ->
        while_regions_cover m beta regions ->
        while_regions_in_guard m beta regions ->
        while_regions_disjoint m regions ->
        while_progress m transitions exits ->
        (forall i : nat,
          (i < m)%nat ->
          hoare_derivable
            (p_concentrated_mass (regions i) (PConst 1%R))
            body
            (while_body_post m regions (transitions i) beta q (exits i))) ->
        while_solution m solution transitions exits ->
        hoare_derivable
          (p_concentrated_mass (regions k) (PVar y))
          (CWhile beta body)
          (p_eq (PExpect (condition_pconstruct q (c_not beta)))
            (PMul (PConst (solution k)) (PVar y)))
  (** Coverage prevents omitted continuing states in an upper bound.
      Regions may overlap or extend outside the guard; the initial input
      must lie in both the guard and region k. No progress premise is needed. *)
  | HWhileUpper :
      forall (m k : nat) (beta : CFormula) (body : Cmd) (q : PConstruct)
        (regions : nat -> CFormula) (solution exits : nat -> R)
        (transitions : nat -> nat -> R) (y : ProbLogicVar),
        (k < m)%nat ->
        while_regions_cover m beta regions ->
        (forall i : nat,
          (i < m)%nat ->
          hoare_derivable
            (p_concentrated_mass (regions i) (PConst 1%R))
            body
            (while_body_post_upper m regions (transitions i) beta q (exits i))) ->
        while_upper_solution m solution transitions exits ->
        hoare_derivable
          (p_concentrated_mass_upper (c_and beta (regions k)) (PVar y))
          (CWhile beta body)
          (PFLe (PExpect (condition_pconstruct q (c_not beta)))
            (PMul (PConst (solution k)) (PVar y)))
  (** Disjoint guarded regions avoid overcounting in a lower bound; they
      need not cover the guard. Progress is essential to exclude certificates
      justified solely by nonterminating circulation. *)
  | HWhileLower :
      forall (m k : nat) (beta : CFormula) (body : Cmd) (q : PConstruct)
        (regions : nat -> CFormula) (solution exits : nat -> R)
        (transitions : nat -> nat -> R) (y : ProbLogicVar),
        (k < m)%nat ->
        while_regions_in_guard m beta regions ->
        while_regions_disjoint m regions ->
        while_progress m transitions exits ->
        (forall i : nat,
          (i < m)%nat ->
          hoare_derivable
            (p_concentrated_mass (regions i) (PConst 1%R))
            body
            (while_body_post_lower m regions (transitions i) beta q (exits i))) ->
        while_lower_solution m solution transitions exits ->
        hoare_derivable
          (p_concentrated_mass_lower (regions k) (PVar y))
          (CWhile beta body)
          (PFLe (PMul (PConst (solution k)) (PVar y))
            (PExpect (condition_pconstruct q (c_not beta)))).

(** Hoare triples use a separate scope so importing this module does not
    activate proof-judgment notation implicitly. *)
Declare Scope cphl_hoare_scope.
Delimit Scope cphl_hoare_scope with cphl_hoare.

Notation "{{ eta }} c {{ theta }}" := (hoare_derivable eta c theta)
  (at level 2,
   eta custom cphl_prob at level 99,
   c custom cphl_expr at level 99,
   theta custom cphl_prob at level 99) : cphl_hoare_scope.

(** A convenient unit-mass consequence of the paper-shaped [HWhileNot]
    constructor. *)
Definition while_not_unit_mass : ProbLogicVar :=
  prob_logic_var "__while_not_unit_mass".

Lemma HWhileNot_unit :
  forall (gamma beta : CFormula) (body : Cmd),
    cformula_valid (FImpl gamma (c_not beta)) ->
    hoare_derivable
      (p_concentrated_mass gamma (PConst 1%R))
      (CWhile beta body)
      (p_concentrated_mass gamma (PConst 1%R)).
Proof.
  intros gamma beta body Houtside.
  set (eta :=
    p_concentrated_mass gamma (PVar while_not_unit_mass)).
  set (rigid :=
    p_eq (PVar while_not_unit_mass) (PConst 1%R)).
  set (desired :=
    p_concentrated_mass gamma (PConst 1%R)).
  assert (Hraw :
    hoare_derivable eta (CWhile beta body) eta).
  {
    unfold eta.
    apply HWhileNot.
    exact Houtside.
  }
  assert (Heta :
    hoare_derivable (p_and eta rigid) (CWhile beta body) eta).
  {
    eapply HConseq with (eta1 := eta) (eta2 := eta).
    - unfold pformula_valid.
      intros ps Hsub; cbn [psatisfies p_and p_not]; tauto.
    - exact Hraw.
    - unfold pformula_valid.
      intros ps Hsub; cbn [psatisfies]; tauto.
  }
  assert (Hrigid :
    hoare_derivable (p_and eta rigid) (CWhile beta body) rigid).
  {
    eapply HConseq with (eta1 := rigid) (eta2 := rigid).
    - unfold pformula_valid.
      intros ps Hsub; cbn [psatisfies p_and p_not]; tauto.
    - apply HFree.
      unfold rigid.
      cbn [p_eq p_and p_not pformula_analytical pterm_analytical].
      tauto.
    - unfold pformula_valid.
      intros ps Hsub; cbn [psatisfies]; tauto.
  }
  change
    (hoare_derivable
      (subst_prob_pformula while_not_unit_mass (PConst 1%R) eta)
      (CWhile beta body) desired).
  eapply HElimv with
    (eta1 := eta) (y := while_not_unit_mass) (p := PConst 1%R).
  - eapply HConseq with
      (eta1 := p_and eta rigid) (eta2 := p_and eta rigid).
    + unfold pformula_valid.
      intros ps Hsub; cbn [psatisfies]; tauto.
    + apply HAnd; assumption.
    + unfold pformula_valid, eta, rigid, desired,
        p_concentrated_mass.
      intros ps Hsub.
      cbn [psatisfies p_and p_not p_eq pterm_eval].
      nra.
  - cbn [prob_logic_var_occurs_pterm]; tauto.
  - unfold desired, p_concentrated_mass.
    cbn [p_eq p_and p_not prob_logic_var_occurs_pformula
      prob_logic_var_occurs_pterm].
    tauto.
Qed.

(** Compilation checks for the Hoare rules. *)
Section HoareRuleExamples.
  Definition demo_hoare_y1 : ProbLogicVar := prob_logic_var "y1".
  Definition demo_hoare_y2 : ProbLogicVar := prob_logic_var "y2".
  Definition demo_hoare_event : CFormula :=
    FProgBool demo_bool_program_var.
  Definition demo_hoare_event_expectation : Pterm :=
    PExpect (QIndicator demo_hoare_event).
  Definition demo_hoare_distribution : Distribution :=
    Gaussian (TConst 0%R) (TConst 1%R).

  Example free_rule_example :
    hoare_derivable p_true command_while_example p_true.
  Proof.
    apply HFree.
    unfold p_true; cbn [pformula_analytical pterm_analytical].
    tauto.
  Qed.

  Example skip_rule_example : hoare_derivable p_true CSkip p_true.
  Proof.
    apply HSkip.
  Qed.

  Example real_assignment_rule_example :
    hoare_derivable
      (subst_real_pformula demo_real_program_var (TConst 1%R) p_true)
      (CRealAssign demo_real_program_var (TConst 1%R)) p_true.
  Proof.
    apply HRealAssign.
  Qed.

  Example bool_assignment_rule_example :
    hoare_derivable
      (subst_bool_pformula demo_bool_program_var c_true p_true)
      (CBoolAssign demo_bool_program_var c_true) p_true.
  Proof.
    apply HBoolAssign.
  Qed.

  Example toss_rule_example :
    hoare_derivable (toss_pformula demo_bool_program_var (1 / 2)%R p_true)
      (CBoolToss demo_bool_program_var (1 / 2)%R) p_true.
  Proof.
    apply HBoolToss.
    unfold coin_probability_valid.
    lra.
  Qed.

  Definition demo_sample_precondition : PFormula :=
    p_and (sample_pformula demo_real_program_var demo_hoare_distribution p_true)
      (p_almost_sure (distribution_valid_formula demo_hoare_distribution)).

  Example sample_rule_example :
    hoare_derivable demo_sample_precondition
      (CRealSample demo_real_program_var demo_hoare_distribution) p_true.
  Proof.
    apply HRealSample.
    - unfold pformula_valid, demo_sample_precondition.
      intros ps Hsub.
      cbn [p_and p_not psatisfies].
      tauto.
    - unfold pformula_valid, demo_sample_precondition.
      intros ps Hsub.
      cbn [p_and p_not psatisfies].
      tauto.
  Qed.

  Definition demo_if_le_branch1 : PFormula :=
    PFLe (PVar demo_hoare_y1) demo_hoare_event_expectation.
  Definition demo_if_le_branch2 : PFormula :=
    PFLe (PVar demo_hoare_y2) demo_hoare_event_expectation.

  Example if_le_rule_example :
    hoare_derivable
      (if_precondition demo_if_le_branch1 demo_if_le_branch2 demo_hoare_event)
      (CIf demo_hoare_event CSkip CSkip)
      (PFLe (PAdd (PVar demo_hoare_y1) (PVar demo_hoare_y2))
        demo_hoare_event_expectation).
  Proof.
    apply HIfLe with
      (eta1 := demo_if_le_branch1) (eta2 := demo_if_le_branch2).
    - apply HSkip.
    - apply HSkip.
  Qed.

  Definition demo_if_ge_branch1 : PFormula :=
    PFLe demo_hoare_event_expectation (PVar demo_hoare_y1).
  Definition demo_if_ge_branch2 : PFormula :=
    PFLe demo_hoare_event_expectation (PVar demo_hoare_y2).

  Example if_ge_rule_example :
    hoare_derivable
      (if_precondition demo_if_ge_branch1 demo_if_ge_branch2 demo_hoare_event)
      (CIf demo_hoare_event CSkip CSkip)
      (PFLe demo_hoare_event_expectation
        (PAdd (PVar demo_hoare_y1) (PVar demo_hoare_y2))).
  Proof.
    apply HIfGe with
      (eta1 := demo_if_ge_branch1) (eta2 := demo_if_ge_branch2).
    - apply HSkip.
    - apply HSkip.
  Qed.

  Definition demo_if_eq_branch1 : PFormula :=
    p_eq (PVar demo_hoare_y1) demo_hoare_event_expectation.
  Definition demo_if_eq_branch2 : PFormula :=
    p_eq (PVar demo_hoare_y2) demo_hoare_event_expectation.

  Example if_eq_rule_example :
    hoare_derivable
      (if_precondition demo_if_eq_branch1 demo_if_eq_branch2 demo_hoare_event)
      (CIf demo_hoare_event CSkip CSkip)
      (p_eq (PAdd (PVar demo_hoare_y1) (PVar demo_hoare_y2))
        demo_hoare_event_expectation).
  Proof.
    apply HIfEq with
      (eta1 := demo_if_eq_branch1) (eta2 := demo_if_eq_branch2).
    - apply HSkip.
    - apply HSkip.
  Qed.

  Example sequence_rule_example :
    hoare_derivable p_true (CSeq CSkip CSkip) p_true.
  Proof.
    eapply HSeq with (eta2 := p_true).
    - apply HSkip.
    - apply HSkip.
  Qed.

  Example consequence_rule_example :
    hoare_derivable p_true CSkip p_true.
  Proof.
    eapply HConseq with (eta1 := p_true) (eta2 := p_true).
    - unfold pformula_valid.
      intros ps Hsub; cbn [p_true psatisfies]; tauto.
    - apply HSkip.
    - unfold pformula_valid.
      intros ps Hsub; cbn [p_true psatisfies]; tauto.
  Qed.

  Example conjunction_rule_example :
    hoare_derivable p_true CSkip (p_and p_true p_true).
  Proof.
    apply HAnd; apply HSkip.
  Qed.

  Example disjunction_rule_example :
    hoare_derivable (p_or p_true p_true) CSkip p_true.
  Proof.
    apply HOr; apply HSkip.
  Qed.

  Example elimv_rule_example :
    hoare_derivable p_true CSkip p_true.
  Proof.
    eapply HElimv with (eta1 := p_true) (y := demo_hoare_y1)
      (p := PConst 0%R).
    - eapply HConseq with
        (eta1 := p_and p_true (p_eq (PVar demo_hoare_y1) (PConst 0%R)))
        (eta2 := p_and p_true (p_eq (PVar demo_hoare_y1) (PConst 0%R))).
      + unfold pformula_valid.
        intros ps Hsub; cbn [p_and p_not p_eq psatisfies]; tauto.
      + apply HSkip.
      + unfold pformula_valid.
        intros ps Hsub; cbn [p_true psatisfies p_and p_not p_eq]; tauto.
    - cbn [prob_logic_var_occurs_pterm]; tauto.
    - cbn [p_true prob_logic_var_occurs_pformula]; tauto.
  Qed.

  (** Reduction checks for the finite-family encodings used by [HWhile]. *)
  Example finite_c_or_two_example (formulas : nat -> CFormula) :
    finite_c_or 2 formulas =
      c_or (c_or FFalse (formulas 0%nat)) (formulas 1%nat).
  Proof.
    reflexivity.
  Qed.

  Example finite_p_and_two_example (formulas : nat -> PFormula) :
    finite_p_and 2 formulas =
      p_and (p_and p_true (formulas 0%nat)) (formulas 1%nat).
  Proof.
    reflexivity.
  Qed.

  Example finite_r_sum_two_example (terms : nat -> R) :
    finite_r_sum 2 terms =
      ((0 + terms 0%nat) + terms 1%nat)%R.
  Proof.
    reflexivity.
  Qed.

  Example p_concentrated_mass_unfold_example
    (gamma : CFormula) (mass : Pterm) :
    p_concentrated_mass gamma mass =
      p_and
        (p_eq (PExpect (QIndicator gamma))
          (PExpect (QIndicator c_true)))
        (p_eq (PExpect (QIndicator c_true)) mass).
  Proof.
    reflexivity.
  Qed.

  Definition demo_while_regions (_ : nat) : CFormula := demo_hoare_event.
  Definition demo_while_solution (_ : nat) : R := 1%R.
  Definition demo_while_exits (_ : nat) : R := 1%R.
  Definition demo_while_transitions (_ _ : nat) : R := 0%R.
  Definition demo_while_q : PConstruct := QIndicator c_true.

  Example while_body_post_one_region_example :
    while_body_post 1 demo_while_regions (demo_while_transitions 0%nat)
      demo_hoare_event demo_while_q (demo_while_exits 0%nat) =
    p_and
      (p_and p_true
        (p_eq (PExpect (QIndicator (demo_while_regions 0%nat)))
          (PConst (demo_while_transitions 0%nat 0%nat))))
      (p_eq
        (PExpect
          (condition_pconstruct demo_while_q (c_not demo_hoare_event)))
        (PConst (demo_while_exits 0%nat))).
  Proof.
    reflexivity.
  Qed.

  Variable demo_while_body : Cmd.
  Hypothesis demo_while_body_step :
    hoare_derivable
      (p_concentrated_mass (demo_while_regions 0%nat) (PConst 1%R))
      demo_while_body
      (while_body_post 1 demo_while_regions (demo_while_transitions 0%nat)
        demo_hoare_event demo_while_q (demo_while_exits 0%nat)).

  Example while_rule_one_region_example :
    hoare_derivable
      (p_concentrated_mass (demo_while_regions 0%nat) (PVar demo_hoare_y1))
      (CWhile demo_hoare_event demo_while_body)
      (p_eq
        (PExpect
          (condition_pconstruct demo_while_q (c_not demo_hoare_event)))
        (PMul (PConst (demo_while_solution 0%nat)) (PVar demo_hoare_y1))).
  Proof.
    eapply HWhile with
      (m := 1%nat) (k := 0%nat) (regions := demo_while_regions)
      (solution := demo_while_solution) (exits := demo_while_exits)
      (transitions := demo_while_transitions).
    - lia.
    - unfold while_regions_cover, cformula_valid, demo_while_regions.
      intro v; cbn [finite_c_or c_or c_not satisfies]; tauto.
    - unfold while_regions_in_guard, cformula_valid, demo_while_regions.
      intros i Hi v; cbn [satisfies]; tauto.
    - unfold while_regions_disjoint.
      intros i j Hi Hj; lia.
    - unfold while_progress, demo_while_exits.
      intros i Hi; left; lra.
    - intros i Hi.
      assert (i = 0)%nat by lia.
      subst i.
      exact demo_while_body_step.
    - unfold while_solution, demo_while_solution, demo_while_transitions,
        demo_while_exits.
      intros i Hi.
      cbn [finite_r_sum].
      split; lra.
  Qed.
End HoareRuleExamples.

(** Focused checks for the scoped surface syntax.  These examples deliberately
    compare notation with constructor trees, so later grammar changes cannot
    silently alter precedence or associativity. *)
Section NotationChecks.
  Local Open Scope cphl_scope.
  Local Open Scope cphl_hoare_scope.

  Variables (notation_x notation_z : RealProgramVar).
  Variable notation_X : RealLogicVar.
  Variable notation_b : BoolProgramVar.
  Variable notation_B : BoolLogicVar.
  Variable notation_y : ProbLogicVar.
  Variable notation_distribution : R -> Distribution.
  Variable notation_pterm : R -> Pterm.

  Example term_notation_expansion :
    <{ notation_x + notation_X * 2 }> =
      TAdd (TProgVar notation_x)
        (TMul (TLogicVar notation_X) (TConst 2%R)).
  Proof.
    reflexivity.
  Qed.

  Example classical_connective_notation_expansion :
    <{ ~ notation_b /\ true \/ false -> notation_B <-> true }> =
      c_iff
        (FImpl
          (c_or (c_and (c_not (FProgBool notation_b)) c_true) FFalse)
          (FLogicBool notation_B))
        c_true.
  Proof.
    reflexivity.
  Qed.

  Example classical_le_notation_expansion :
    <{ notation_x <= notation_X }> =
      FLe (TProgVar notation_x) (TLogicVar notation_X).
  Proof.
    reflexivity.
  Qed.

  Example classical_lt_notation_expansion :
    <{ notation_x < notation_X }> =
      c_lt (TProgVar notation_x) (TLogicVar notation_X).
  Proof.
    reflexivity.
  Qed.

  Example classical_eq_notation_expansion :
    <{ notation_x = notation_X }> =
      c_and
        (FLe (TProgVar notation_x) (TLogicVar notation_X))
        (FLe (TLogicVar notation_X) (TProgVar notation_x)).
  Proof.
    reflexivity.
  Qed.

  Example classical_ge_notation_expansion :
    <{ notation_x >= notation_X }> =
      FLe (TLogicVar notation_X) (TProgVar notation_x).
  Proof.
    reflexivity.
  Qed.

  Example classical_gt_notation_expansion :
    <{ notation_x > notation_X }> =
      c_lt (TLogicVar notation_X) (TProgVar notation_x).
  Proof.
    reflexivity.
  Qed.

  Example uniform_notation_expansion :
    <{ uniform ( notation_x, notation_X + 1 ) }> =
      Uniform (TProgVar notation_x)
        (TAdd (TLogicVar notation_X) (TConst 1%R)).
  Proof.
    reflexivity.
  Qed.

  Example laplace_notation_expansion :
    <{ laplace ( notation_x, 2 ) }> =
      Laplace (TProgVar notation_x) (TConst 2%R).
  Proof.
    reflexivity.
  Qed.

  Example gaussian_notation_expansion :
    <{ gaussian ( notation_X, 3 ) }> =
      Gaussian (TLogicVar notation_X) (TConst 3%R).
  Proof.
    reflexivity.
  Qed.

  Example expression_antiquotation_expansion :
    <{ notation_x sample $(notation_distribution 4%R) }> =
      CRealSample notation_x (notation_distribution 4%R).
  Proof.
    reflexivity.
  Qed.

  Example indicator_notation_expansion :
    [[ indicator[notation_b] ]] =
      QIndicator (FProgBool notation_b).
  Proof.
    reflexivity.
  Qed.

  Example nested_integral_notation_expansion :
    [[ integral notation_x ~ laplace ( 0, 1 ),
       integral notation_z ~ gaussian ( notation_X, 2 ),
       indicator[notation_x <= notation_X] ]] =
      QIntegral notation_x (Laplace (TConst 0%R) (TConst 1%R))
        (QIntegral notation_z
          (Gaussian (TLogicVar notation_X) (TConst 2%R))
          (QIndicator
            (FLe (TProgVar notation_x) (TLogicVar notation_X)))).
  Proof.
    reflexivity.
  Qed.

  Example expectation_and_probability_notation_expansion :
    [[ E[ indicator[notation_b] ] + Pr[notation_B] ]] =
      PAdd
        (PExpect (QIndicator (FProgBool notation_b)))
        (PExpect (QIndicator (FLogicBool notation_B))).
  Proof.
    reflexivity.
  Qed.

  Example probabilistic_antiquotation_expansion :
    [[ $(notation_pterm 5%R) + notation_y ]] =
      PAdd (notation_pterm 5%R) (PVar notation_y).
  Proof.
    reflexivity.
  Qed.

  Example probabilistic_connective_notation_expansion :
    [[ ~ (notation_y <= 0) /\ true \/ false ->
       almost_sure[notation_b] <-> true ]] =
      p_iff
        (PFImpl
          (p_or
            (p_and (p_not (PFLe (PVar notation_y) (PConst 0%R))) p_true)
            PFFalse)
          (p_almost_sure (FProgBool notation_b)))
        p_true.
  Proof.
    reflexivity.
  Qed.

  Example probabilistic_le_notation_expansion :
    [[ notation_y <= 1 ]] = PFLe (PVar notation_y) (PConst 1%R).
  Proof.
    reflexivity.
  Qed.

  Example probabilistic_lt_notation_expansion :
    [[ notation_y < 1 ]] = p_lt (PVar notation_y) (PConst 1%R).
  Proof.
    reflexivity.
  Qed.

  Example probabilistic_eq_notation_expansion :
    [[ notation_y = 1 ]] = p_eq (PVar notation_y) (PConst 1%R).
  Proof.
    reflexivity.
  Qed.

  Example probabilistic_ge_notation_expansion :
    [[ notation_y >= 1 ]] = PFLe (PConst 1%R) (PVar notation_y).
  Proof.
    reflexivity.
  Qed.

  Example probabilistic_gt_notation_expansion :
    [[ notation_y > 1 ]] = p_lt (PConst 1%R) (PVar notation_y).
  Proof.
    reflexivity.
  Qed.

  Example command_notation_expansion :
    <{
      notation_x := notation_X + 1;
      notation_b b= notation_b -> notation_B;
      notation_b toss $((1 / 2)%R);
      notation_z sample uniform ( 0, 1 );
      if notation_b then skip
      else while notation_B do notation_x := 0 end
      end
    }> =
      CSeq
        (CRealAssign notation_x
          (TAdd (TLogicVar notation_X) (TConst 1%R)))
        (CSeq
          (CBoolAssign notation_b
            (FImpl (FProgBool notation_b) (FLogicBool notation_B)))
          (CSeq
            (CBoolToss notation_b (1 / 2)%R)
            (CSeq
              (CRealSample notation_z
                (Uniform (TConst 0%R) (TConst 1%R)))
              (CIf (FProgBool notation_b) CSkip
                (CWhile (FLogicBool notation_B)
                  (CRealAssign notation_x (TConst 0%R))))))).
  Proof.
    reflexivity.
  Qed.

  Example hoare_triple_notation_skip :
    {{ true }} <{ skip }> {{ true }}.
  Proof.
    apply HSkip.
  Qed.
End NotationChecks.
