(** Library-only foundation: this file must not import CPHL or its supporting
    proofs. CPHL can require it without creating a dependency cycle. *)
From Stdlib Require Import Reals.
From mathcomp Require Import boot order ssralg ssrnum reals.
From mathcomp Require Import normedtype sequences trigonometry_functions.
From mathcomp Require Import Rstruct Rstruct_topology.

(** Load the selected analytical APIs without exporting their notation to
    clients. Later semantic files explicitly import the APIs they use. *)
From mathcomp Require measure lebesgue_integral kernel.

Module StandardReal.

(** Rstruct equips Stdlib R itself with MathComp structures; no conversion
    of program constants or valuations to another real carrier is needed. *)
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope ring_scope.

Lemma add (x y : real) : Rplus x y = x + y.
Proof. reflexivity. Qed.

Lemma sub (x y : real) : Rminus x y = x - y.
Proof. reflexivity. Qed.

Lemma mul (x y : real) : Rmult x y = x * y.
Proof. reflexivity. Qed.

Lemma opp (x : real) : Ropp x = - x.
Proof. reflexivity. Qed.

Lemma inv (x : real) : Rinv x = x^-1.
Proof. reflexivity. Qed.

Lemma div (x y : real) : Rdiv x y = x / y.
Proof. reflexivity. Qed.

(** Reflection connects propositional Stdlib inequalities with MathComp's
    Boolean comparisons; keep this distinction explicit in later proofs. *)
Lemma leP (x y : real) : reflect (Rle x y) (x <= y).
Proof. exact: RleP. Qed.

Lemma ltP (x y : real) : reflect (Rlt x y) (x < y).
Proof. exact: RltP. Qed.

(** These library theorems bridge the transcendental functions used by the
    existing density expressions, without assuming density normalization. *)
Lemma exp (x : real) : Rtrigo_def.exp x = expR x.
Proof. exact: RexpE. Qed.

Lemma sqrt (x : real) : R_sqrt.sqrt x = Num.sqrt x.
Proof. exact: RsqrtE. Qed.

Lemma pi : PI = (trigonometry_functions.pi : real).
Proof. exact: Rtrigo_PIE. Qed.

End StandardReal.
