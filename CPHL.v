(**
  Continuous Probabilistic Hoare Logic (CPHL): classical-state syntax.

  This file formalizes the classical fragment from [paper/cEPPL.tex].
  It deliberately stops before the probabilistic assertion language and the
  programming language.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Ascii.
From Stdlib Require Import ClassicalDescription.
From Stdlib Require Import Lra.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.

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
    Program execution will eventually update only the program-variable fields. *)
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

(** Probabilistic states are modeled abstractly.  [measure_of] may be applied
    to every semantic classical assertion, while the axioms below constrain
    the opaque inhabitants of [Measure] to behave like sub-probability
    measures. *)
Parameter Measure : Type.

Parameter measure_of : Measure -> Assertion -> R.

Axiom measure_empty :
  forall mu : Measure,
    measure_of mu (fun _ : state => False) = 0%R.

Axiom measure_extensional :
  forall (mu : Measure) (A B : Assertion),
    (forall v : state, A v <-> B v) ->
    measure_of mu A = measure_of mu B.

Axiom measure_additive :
  forall (mu : Measure) (A B : Assertion),
    (forall v : state, ~ (A v /\ B v)) ->
    measure_of mu (fun v : state => A v \/ B v) =
      (measure_of mu A + measure_of mu B)%R.

Axiom measure_nonnegative :
  forall (mu : Measure) (A : Assertion),
    (0 <= measure_of mu A)%R.

Axiom measure_subprobability :
  forall mu : Measure,
    (measure_of mu (fun _ : state => True) <= 1)%R.

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

(** Probability constructs.  [QIntegral x d q] denotes the paper's
    [integral q^x_k f(k) dk]; the displayed variable [k] is nameless here and
    hence alpha-equivalent choices have the same representation. *)
Inductive PConstruct : Type :=
  | QIndicator (gamma : CFormula)
  | QIntegral (x : RealProgramVar) (d : Distribution) (q : PConstruct).

(** The real integral and expectation are abstract at this stage. *)
Parameter real_integral : (R -> R) -> R.

(** The abstract integral is equipped with the algebraic laws used by
    continuous-program calculations.  The operator remains total, as in the
    paper's assertion semantics; these axioms record the trusted analytical
    boundary rather than choosing a concrete integration library. *)
Axiom real_integral_extensional :
  forall f g : R -> R,
    (forall x : R, f x = g x) ->
    real_integral f = real_integral g.

Axiom real_integral_add :
  forall f g : R -> R,
    real_integral (fun x => f x + g x) =
      (real_integral f + real_integral g)%R.

Axiom real_integral_scale :
  forall (c : R) (f : R -> R),
    real_integral (fun x => c * f x) = (c * real_integral f)%R.

Lemma real_integral_zero :
  real_integral (fun _ : R => 0%R) = 0%R.
Proof.
  transitivity (real_integral (fun x : R => 0 * (fun _ => 1) x)%R).
  - apply real_integral_extensional; intro x; ring.
  - rewrite real_integral_scale; ring.
Qed.

Lemma real_integral_scale_right :
  forall (c : R) (f : R -> R),
    real_integral (fun x => f x * c) = (real_integral f * c)%R.
Proof.
  intros c f.
  transitivity (real_integral (fun x => c * f x)).
  - apply real_integral_extensional; intro x; ring.
  - rewrite real_integral_scale; ring.
Qed.

(** Half-open regions form a disjoint partition of the real line and avoid
    requiring a separate zero-mass-at-an-endpoint axiom. *)
Definition real_integral_below (a : R) (f : R -> R) : R :=
  real_integral (fun x => real_indicator (x < a)%R * f x).

Definition real_integral_between (a b : R) (f : R -> R) : R :=
  real_integral
    (fun x => real_indicator (a <= x < b)%R * f x).

Definition real_integral_above (a : R) (f : R -> R) : R :=
  real_integral (fun x => real_indicator (a <= x)%R * f x).

Lemma real_integral_below_add :
  forall (a : R) (f g : R -> R),
    real_integral_below a (fun x => f x + g x) =
      (real_integral_below a f + real_integral_below a g)%R.
Proof.
  intros a f g.
  unfold real_integral_below.
  transitivity
    (real_integral
      (fun x =>
        real_indicator (x < a)%R * f x +
        real_indicator (x < a)%R * g x)).
  - apply real_integral_extensional; intro x; ring.
  - apply real_integral_add.
Qed.

Lemma real_integral_between_add :
  forall (a b : R) (f g : R -> R),
    real_integral_between a b (fun x => f x + g x) =
      (real_integral_between a b f + real_integral_between a b g)%R.
Proof.
  intros a b f g.
  unfold real_integral_between.
  transitivity
    (real_integral
      (fun x =>
        real_indicator (a <= x < b)%R * f x +
        real_indicator (a <= x < b)%R * g x)).
  - apply real_integral_extensional; intro x; ring.
  - apply real_integral_add.
Qed.

Lemma real_integral_above_add :
  forall (a : R) (f g : R -> R),
    real_integral_above a (fun x => f x + g x) =
      (real_integral_above a f + real_integral_above a g)%R.
Proof.
  intros a f g.
  unfold real_integral_above.
  transitivity
    (real_integral
      (fun x =>
        real_indicator (a <= x)%R * f x +
        real_indicator (a <= x)%R * g x)).
  - apply real_integral_extensional; intro x; ring.
  - apply real_integral_add.
Qed.

Lemma real_integral_below_scale :
  forall (a c : R) (f : R -> R),
    real_integral_below a (fun x => c * f x) =
      (c * real_integral_below a f)%R.
Proof.
  intros a c f.
  unfold real_integral_below.
  transitivity
    (real_integral (fun x => c * (real_indicator (x < a)%R * f x))).
  - apply real_integral_extensional; intro x; ring.
  - apply real_integral_scale.
Qed.

Lemma real_integral_between_scale :
  forall (a b c : R) (f : R -> R),
    real_integral_between a b (fun x => c * f x) =
      (c * real_integral_between a b f)%R.
Proof.
  intros a b c f.
  unfold real_integral_between.
  transitivity
    (real_integral
      (fun x => c * (real_indicator (a <= x < b)%R * f x))).
  - apply real_integral_extensional; intro x; ring.
  - apply real_integral_scale.
Qed.

Lemma real_integral_above_scale :
  forall (a c : R) (f : R -> R),
    real_integral_above a (fun x => c * f x) =
      (c * real_integral_above a f)%R.
Proof.
  intros a c f.
  unfold real_integral_above.
  transitivity
    (real_integral (fun x => c * (real_indicator (a <= x)%R * f x))).
  - apply real_integral_extensional; intro x; ring.
  - apply real_integral_scale.
Qed.

Lemma real_integral_split_three :
  forall (f : R -> R) (a b : R),
    (a <= b)%R ->
    real_integral f =
      (real_integral_below a f +
       real_integral_between a b f +
       real_integral_above b f)%R.
Proof.
  intros f a b Hab.
  unfold real_integral_below, real_integral_between,
    real_integral_above.
  transitivity
    (real_integral
      (fun x =>
        real_indicator (x < a)%R * f x +
        (real_indicator (a <= x < b)%R * f x +
         real_indicator (b <= x)%R * f x))).
  - apply real_integral_extensional.
    intro x.
    destruct (Rlt_dec x a) as [Hxa | Hnxa].
    + rewrite (real_indicator_true _ Hxa).
      rewrite (real_indicator_false (a <= x < b)%R) by lra.
      rewrite (real_indicator_false (b <= x)%R) by lra.
      ring.
    + destruct (Rlt_dec x b) as [Hxb | Hnxb].
      * rewrite (real_indicator_false (x < a)%R) by lra.
        rewrite (real_indicator_true (a <= x < b)%R) by lra.
        rewrite (real_indicator_false (b <= x)%R) by lra.
        ring.
      * rewrite (real_indicator_false (x < a)%R) by lra.
        rewrite (real_indicator_false (a <= x < b)%R) by lra.
        rewrite (real_indicator_true (b <= x)%R) by lra.
        ring.
  - rewrite real_integral_add, real_integral_add.
    ring.
Qed.

(** Closed forms for the exponential functions needed below. *)
Axiom real_integral_exp_below :
  forall a k : R,
    (0 < k)%R ->
    real_integral_below a (fun x => exp (k * x)) =
      (exp (k * a) / k)%R.

Axiom real_integral_exp_between :
  forall a b k : R,
    (a <= b)%R ->
    k <> 0%R ->
    real_integral_between a b (fun x => exp (k * x)) =
      ((exp (k * b) - exp (k * a)) / k)%R.

Axiom real_integral_exp_above :
  forall a k : R,
    (k < 0)%R ->
    real_integral_above a (fun x => exp (k * x)) =
      (- exp (k * a) / k)%R.

(** The usual Laplace CDF, using the same [(location, scale)] convention as
    [Laplace] and [distribution_density]. *)
Definition laplace_cdf (location scale cutoff : R) : R :=
  if Rle_dec cutoff location
  then ((1 / 2) * exp ((cutoff - location) / scale))%R
  else (1 - (1 / 2) * exp (- (cutoff - location) / scale))%R.

(** Reusable closed forms derived from the exponential-region laws above.
    They are stated at the raw density level so later examples need not expose
    [Distribution] or a program state. *)
Lemma laplace_integral_left_below :
  forall location scale cutoff : R,
    (0 < scale)%R ->
    (cutoff <= location)%R ->
    real_integral_below cutoff
      (fun z =>
        (1 / (2 * scale)) *
          exp (- Rabs (z - location) / scale)) =
      ((1 / 2) * exp ((cutoff - location) / scale))%R.
Proof.
  intros location scale cutoff Hscale Hcutoff.
  transitivity
    (real_integral_below cutoff
      (fun z =>
        ((1 / (2 * scale)) * exp (- location / scale)) *
          exp ((1 / scale) * z))).
  - unfold real_integral_below.
    apply real_integral_extensional.
    intro z.
    destruct (Rlt_dec z cutoff) as [Hz | Hnz].
    + rewrite (real_indicator_true _ Hz).
      rewrite (Rabs_left (z - location)) by lra.
      assert (Hexp :
        (exp (- - (z - location) / scale) =
          exp (- location / scale) * exp ((1 / scale) * z))%R).
      {
        rewrite <- exp_plus.
        f_equal; field; lra.
      }
      rewrite Hexp; ring.
    + rewrite (real_indicator_false (z < cutoff)%R) by exact Hnz.
      ring.
  - rewrite real_integral_below_scale.
    rewrite (real_integral_exp_below cutoff (1 / scale)).
    + assert (Hexp :
        (exp (- location / scale) * exp ((1 / scale) * cutoff) =
          exp ((cutoff - location) / scale))%R).
      {
        rewrite <- exp_plus.
        f_equal; field; lra.
      }
      rewrite <- Hexp.
      field; lra.
    + apply Rdiv_lt_0_compat; lra.
Qed.

Lemma laplace_integral_right_between :
  forall location scale cutoff : R,
    (0 < scale)%R ->
    (location <= cutoff)%R ->
    real_integral_between location cutoff
      (fun z =>
        (1 / (2 * scale)) *
          exp (- Rabs (z - location) / scale)) =
      ((1 / 2) *
        (1 - exp (- (cutoff - location) / scale)))%R.
Proof.
  intros location scale cutoff Hscale Hcutoff.
  transitivity
    (real_integral_between location cutoff
      (fun z =>
        ((1 / (2 * scale)) * exp (location / scale)) *
          exp ((- 1 / scale) * z))).
  - unfold real_integral_between.
    apply real_integral_extensional.
    intro z.
    destruct (excluded_middle_informative (location <= z < cutoff)%R)
      as [Hz | Hnz].
    + rewrite (real_indicator_true _ Hz).
      rewrite (Rabs_right (z - location)) by lra.
      assert (Hexp :
        (exp (- (z - location) / scale) =
          exp (location / scale) * exp ((- 1 / scale) * z))%R).
      {
        rewrite <- exp_plus.
        f_equal; field; lra.
      }
      rewrite Hexp; ring.
    + rewrite (real_indicator_false (location <= z < cutoff)%R) by
        exact Hnz.
      ring.
  - rewrite real_integral_between_scale.
    rewrite (real_integral_exp_between location cutoff (- 1 / scale)).
    2: exact Hcutoff.
    2: unfold Rdiv; apply Rmult_integral_contrapositive_currified;
       [lra | apply Rinv_neq_0_compat; lra].
    assert (Hexp_cutoff :
      (exp (location / scale) * exp ((- 1 / scale) * cutoff) =
        exp (- (cutoff - location) / scale))%R).
    {
      rewrite <- exp_plus.
      f_equal; field; lra.
    }
    assert (Hexp_location :
      (exp (location / scale) * exp ((- 1 / scale) * location) = 1)%R).
    {
      rewrite <- exp_plus.
      replace (location / scale + -1 / scale * location)%R with 0%R by
        (field; lra).
      apply exp_0.
    }
    transitivity
      (((1 / (2 * scale)) *
        (exp (location / scale) * exp ((- 1 / scale) * cutoff) -
         exp (location / scale) * exp ((- 1 / scale) * location))) /
        (- 1 / scale))%R.
    + field; lra.
    + rewrite Hexp_cutoff, Hexp_location.
      field; lra.
Qed.

Lemma laplace_integral_left_between :
  forall location scale cutoff : R,
    (0 < scale)%R ->
    (cutoff <= location)%R ->
    real_integral_between cutoff location
      (fun z =>
        (1 / (2 * scale)) *
          exp (- Rabs (z - location) / scale)) =
      ((1 / 2) *
        (1 - exp ((cutoff - location) / scale)))%R.
Proof.
  intros location scale cutoff Hscale Hcutoff.
  transitivity
    (real_integral_between cutoff location
      (fun z =>
        ((1 / (2 * scale)) * exp (- location / scale)) *
          exp ((1 / scale) * z))).
  - unfold real_integral_between.
    apply real_integral_extensional.
    intro z.
    destruct (excluded_middle_informative (cutoff <= z < location)%R)
      as [Hz | Hnz].
    + rewrite (real_indicator_true _ Hz).
      rewrite (Rabs_left (z - location)) by lra.
      assert (Hexp :
        (exp (- - (z - location) / scale) =
          exp (- location / scale) * exp ((1 / scale) * z))%R).
      {
        rewrite <- exp_plus.
        f_equal; field; lra.
      }
      rewrite Hexp; ring.
    + rewrite (real_indicator_false (cutoff <= z < location)%R) by
        exact Hnz.
      ring.
  - rewrite real_integral_between_scale.
    rewrite (real_integral_exp_between cutoff location (1 / scale)).
    2: exact Hcutoff.
    2: unfold Rdiv; apply Rmult_integral_contrapositive_currified;
       [lra | apply Rinv_neq_0_compat; lra].
    assert (Hexp_cutoff :
      (exp (- location / scale) * exp ((1 / scale) * cutoff) =
        exp ((cutoff - location) / scale))%R).
    {
      rewrite <- exp_plus.
      f_equal; field; lra.
    }
    assert (Hexp_location :
      (exp (- location / scale) * exp ((1 / scale) * location) = 1)%R).
    {
      rewrite <- exp_plus.
      replace (- location / scale + 1 / scale * location)%R with 0%R by
        (field; lra).
      apply exp_0.
    }
    transitivity
      (((1 / (2 * scale)) *
        (exp (- location / scale) * exp ((1 / scale) * location) -
         exp (- location / scale) * exp ((1 / scale) * cutoff))) /
        (1 / scale))%R.
    + field; lra.
    + rewrite Hexp_location, Hexp_cutoff.
      field; lra.
Qed.

Lemma laplace_integral_right_above :
  forall location scale cutoff : R,
    (0 < scale)%R ->
    (location <= cutoff)%R ->
    real_integral_above cutoff
      (fun z =>
        (1 / (2 * scale)) *
          exp (- Rabs (z - location) / scale)) =
      ((1 / 2) * exp (- (cutoff - location) / scale))%R.
Proof.
  intros location scale cutoff Hscale Hcutoff.
  transitivity
    (real_integral_above cutoff
      (fun z =>
        ((1 / (2 * scale)) * exp (location / scale)) *
          exp ((- 1 / scale) * z))).
  - unfold real_integral_above.
    apply real_integral_extensional.
    intro z.
    destruct (Rle_dec cutoff z) as [Hz | Hnz].
    + rewrite (real_indicator_true _ Hz).
      rewrite (Rabs_right (z - location)) by lra.
      assert (Hexp :
        (exp (- (z - location) / scale) =
          exp (location / scale) * exp ((- 1 / scale) * z))%R).
      {
        rewrite <- exp_plus.
        f_equal; field; lra.
      }
      rewrite Hexp; ring.
    + rewrite (real_indicator_false (cutoff <= z)%R) by exact Hnz.
      ring.
  - rewrite real_integral_above_scale.
    rewrite (real_integral_exp_above cutoff (- 1 / scale)).
    2: {
      replace (- 1 / scale)%R with (- (1 / scale))%R by
        (field; lra).
      apply Ropp_lt_gt_0_contravar.
      apply Rdiv_lt_0_compat; lra.
    }
    assert (Hexp :
      (exp (location / scale) * exp ((- 1 / scale) * cutoff) =
        exp (- (cutoff - location) / scale))%R).
    {
      rewrite <- exp_plus.
      f_equal; field; lra.
    }
    transitivity
      ((1 / (2 * scale)) *
        (exp (location / scale) * exp ((- 1 / scale) * cutoff)) *
        scale)%R.
    + field; lra.
    + rewrite Hexp.
      field; lra.
Qed.

Lemma laplace_integral_strict_cdf :
  forall location scale cutoff : R,
    (0 < scale)%R ->
    real_integral
      (fun z =>
        ((1 / (2 * scale)) *
          exp (- Rabs (z - location) / scale)) *
        real_indicator (z < cutoff)%R) =
      laplace_cdf location scale cutoff.
Proof.
  intros location scale cutoff Hscale.
  unfold laplace_cdf.
  destruct (Rle_dec cutoff location) as [Hleft | Hright].
  - transitivity
      (real_integral_below cutoff
        (fun z =>
          (1 / (2 * scale)) *
            exp (- Rabs (z - location) / scale))).
    + unfold real_integral_below.
      apply real_integral_extensional; intro z; ring.
    + apply laplace_integral_left_below; assumption.
  - transitivity
      (real_integral_below location
        (fun z =>
          (1 / (2 * scale)) *
            exp (- Rabs (z - location) / scale)) +
       real_integral_between location cutoff
        (fun z =>
          (1 / (2 * scale)) *
            exp (- Rabs (z - location) / scale)))%R.
    + unfold real_integral_below, real_integral_between.
      rewrite <- real_integral_add.
      apply real_integral_extensional.
      intro z.
      destruct (Rlt_dec z location) as [Hzl | Hnzl].
      * rewrite (real_indicator_true (z < cutoff)%R) by lra.
        rewrite (real_indicator_true (z < location)%R) by exact Hzl.
        rewrite (real_indicator_false (location <= z < cutoff)%R) by lra.
        ring.
      * destruct (Rlt_dec z cutoff) as [Hzc | Hnzc].
        -- rewrite (real_indicator_true (z < cutoff)%R) by exact Hzc.
           rewrite (real_indicator_false (z < location)%R) by exact Hnzl.
           rewrite (real_indicator_true (location <= z < cutoff)%R) by lra.
           ring.
        -- rewrite (real_indicator_false (z < cutoff)%R) by exact Hnzc.
           rewrite (real_indicator_false (z < location)%R) by lra.
           rewrite (real_indicator_false (location <= z < cutoff)%R) by lra.
           ring.
    + rewrite (laplace_integral_left_below location scale location Hscale)
        by lra.
      rewrite (laplace_integral_right_between location scale cutoff Hscale)
        by lra.
      rewrite Rminus_diag.
      cbn.
      rewrite Rdiv_0_l by lra.
      rewrite exp_0.
      lra.
Qed.

Lemma laplace_integral_survival :
  forall location scale cutoff : R,
    (0 < scale)%R ->
    real_integral
      (fun z =>
        ((1 / (2 * scale)) *
          exp (- Rabs (z - location) / scale)) *
        real_indicator (cutoff <= z)%R) =
      (1 - laplace_cdf location scale cutoff)%R.
Proof.
  intros location scale cutoff Hscale.
  unfold laplace_cdf.
  destruct (Rle_dec cutoff location) as [Hleft | Hright].
  - transitivity
      (real_integral_between cutoff location
        (fun z =>
          (1 / (2 * scale)) *
            exp (- Rabs (z - location) / scale)) +
       real_integral_above location
        (fun z =>
          (1 / (2 * scale)) *
            exp (- Rabs (z - location) / scale)))%R.
    + unfold real_integral_between, real_integral_above.
      rewrite <- real_integral_add.
      apply real_integral_extensional.
      intro z.
      destruct (Rlt_dec z location) as [Hzl | Hnzl].
      * destruct (Rle_dec cutoff z) as [Hcz | Hncz].
        -- rewrite (real_indicator_true (cutoff <= z)%R) by exact Hcz.
           rewrite (real_indicator_true (cutoff <= z < location)%R) by
             exact (conj Hcz Hzl).
           rewrite (real_indicator_false (location <= z)%R) by lra.
           ring.
        -- rewrite (real_indicator_false (cutoff <= z)%R) by exact Hncz.
           rewrite (real_indicator_false (cutoff <= z < location)%R) by lra.
           rewrite (real_indicator_false (location <= z)%R) by lra.
           ring.
      * rewrite (real_indicator_true (cutoff <= z)%R) by lra.
        rewrite (real_indicator_false (cutoff <= z < location)%R) by lra.
        rewrite (real_indicator_true (location <= z)%R) by lra.
        ring.
    + rewrite (laplace_integral_left_between location scale cutoff Hscale)
        by lra.
      rewrite (laplace_integral_right_above location scale location Hscale)
        by lra.
      rewrite Rminus_diag.
      cbn.
      rewrite Ropp_0.
      rewrite Rdiv_0_l by lra.
      rewrite exp_0.
      lra.
  - transitivity
      (real_integral_above cutoff
        (fun z =>
          (1 / (2 * scale)) *
            exp (- Rabs (z - location) / scale))).
    + unfold real_integral_above.
      apply real_integral_extensional; intro z; ring.
    + rewrite (laplace_integral_right_above location scale cutoff Hscale)
        by lra.
      ring.
Qed.

Fixpoint q_eval (q : PConstruct) (v : state) : R :=
  match q with
  | QIndicator gamma => real_indicator (satisfies v gamma)
  | QIntegral x d q' =>
      real_integral
        (fun k =>
          distribution_density d v k * q_eval q' (update_real v x k))
  end.

Parameter expectation : Measure -> (state -> R) -> R.

Axiom expectation_extensional :
  forall (mu : Measure) (f g : state -> R),
    (forall v : state, f v = g v) ->
    expectation mu f = expectation mu g.

Axiom expectation_scale :
  forall (mu : Measure) (c : R) (f : state -> R),
    expectation mu (fun v => c * f v) =
      (c * expectation mu f)%R.

Lemma expectation_zero :
  forall mu : Measure,
    expectation mu (fun _ : state => 0%R) = 0%R.
Proof.
  intro mu.
  transitivity
    (expectation mu (fun v : state => 0 * real_indicator (satisfies v c_true))).
  - apply expectation_extensional; intro v; ring.
  - rewrite expectation_scale; ring.
Qed.

Lemma expectation_constant :
  forall (mu : Measure) (c : R),
    expectation mu (fun _ : state => c) =
      (c * expectation mu (q_eval (QIndicator c_true)))%R.
Proof.
  intros mu c.
  transitivity
    (expectation mu
      (fun v : state => c * q_eval (QIndicator c_true) v)).
  - apply expectation_extensional.
    intro v.
    cbn [q_eval].
    rewrite real_indicator_true.
    + ring.
    + cbn [c_true satisfies]; tauto.
  - apply expectation_scale.
Qed.

Axiom expectation_indicator :
  forall (mu : Measure) (gamma : CFormula),
    expectation mu (q_eval (QIndicator gamma)) =
      measure_of mu (formula_assertion gamma).

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
    in the AST.  Future semantics and proof rules will state the required
    validity side conditions. *)
Inductive Cmd : Type :=
  | CSkip
  | CRealAssign (x : RealProgramVar) (t : Term)
  | CBoolAssign (b : BoolProgramVar) (beta : CFormula)
  | CBoolToss (b : BoolProgramVar) (r : R)
  | CRealSample (x : RealProgramVar) (d : Distribution)
  | CSeq (s1 s2 : Cmd)
  | CIf (beta : CFormula) (s1 s2 : Cmd)
  | CWhile (beta : CFormula) (body : Cmd).

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

(** [pformula_valid] is the semantic notion used by CONSEQ.  It is deliberately
    separate from a proof system for probabilistic formulas: TAUT is outside
    the present development. *)
Definition pformula_valid (eta : PFormula) : Prop :=
  forall ps : Pstate, psatisfies ps eta.

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

(** Boolean-program-variable substitution does not cross a binder, because
    [QIntegral] binds only real program variables. *)
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

Fixpoint subst_bool_pconstruct
  (b : BoolProgramVar) (replacement : CFormula) (q : PConstruct) : PConstruct :=
  match q with
  | QIndicator gamma => QIndicator (subst_bool_cformula b replacement gamma)
  | QIntegral x d q' =>
      QIntegral x d (subst_bool_pconstruct b replacement q')
  end.

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

(** The non-while fragment of the paper's Hoare calculus.  The preconditions
    and postconditions remain syntactic formulas; semantic validity is used
    only for the consequence and sampling side conditions. *)
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
        hoare_derivable eta0 s (p_and eta1 eta2).

(** Compilation checks for the non-while Hoare rules. *)
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
      intros ps.
      cbn [p_and p_not psatisfies].
      tauto.
    - unfold pformula_valid, demo_sample_precondition.
      intros ps.
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
      intros ps; cbn [p_true psatisfies]; tauto.
    - apply HSkip.
    - unfold pformula_valid.
      intros ps; cbn [p_true psatisfies]; tauto.
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
        intros ps; cbn [p_and p_not p_eq psatisfies]; tauto.
      + apply HSkip.
      + unfold pformula_valid.
        intros ps; cbn [p_true psatisfies p_and p_not p_eq]; tauto.
    - cbn [prob_logic_var_occurs_pterm]; tauto.
    - cbn [p_true prob_logic_var_occurs_pformula]; tauto.
  Qed.
End HoareRuleExamples.
