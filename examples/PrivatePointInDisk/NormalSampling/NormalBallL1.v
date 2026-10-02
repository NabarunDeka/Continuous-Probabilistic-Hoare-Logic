(**
  NormalBallL1.v -- the L1 membership test with the two POINTS perturbed
  normally.  The L1 counterpart of NormalDisk.v, and the companion to
  NormalDistanceL1.v, which perturbs the distance instead.

      n1 <- sample(Gaussian(0, b));   n3 <- sample(Gaussian(0, b));
      n2 <- sample(Gaussian(0, b));   n4 <- sample(Gaussian(0, b));
      ux := (px+n1) - (cx+n3);   if ux < 0 then ux := -ux else skip end;
      uy := (py+n2) - (cy+n4);   if uy < 0 then uy := -uy else skip end;
      inside := (ux + uy < 1)

  NO TRIPLE IS PROVED HERE.  The intended one is [nb_target]:

      { Pr[tt] = 1 }
          nb_prog px py cx cy b
      { Pr[inside] = <the L1-ball probability> }

  stated at the end and deliberately left open.  This file exists to record
  the program, and one geometric fact that makes the L1 case genuinely
  better than the L2 one.

  WHY THE BRANCHES ARE HARDER HERE THAN IN NormalDistanceL1.v.

  There the guards test a CLOSED term -- the coordinates are Rocq reals, so
  after [ax := px - cx] the sign is fixed and one branch carries all the
  mass.  That is what [nl_abs_neg] / [nl_abs_pos] exploit: the branch
  constants are [(r, 0)] or [(0, r)].

  Here the guards test the PERTURBED difference, which is random.  Both
  branches carry mass, and [HIfEq] then needs those two masses.  They can be
  carried symbolically as rigid variables, but they are exactly the
  quantities nobody can evaluate -- so nothing is gained.

  WHAT IS BETTER ABOUT L1, AND IT IS NOT SMALL.

  For the L2 disk the section at a fixed first coordinate is

      |v| < sqrt(1 - u^2)

  whose endpoints are NOT polynomial in [u] -- that is the obstruction
  recorded in flags/FLAGS.md F14, the same one that rules out Marsaglia's
  polar method.  For the L1 ball the section is

      |v| < 1 - |u|

  whose endpoints are PIECEWISE LINEAR.  So the reachability criterion of
  UniformConstructions/TriangularRejection.v -- sections must be intervals
  with polynomial endpoints -- is satisfied, and the inner integral is a
  plain difference of CDFs at linear arguments.

  Consequences, which differ by noise distribution:

    - with LAPLACE noise the outer integrand is then piecewise exponential
      in [u], so the whole thing is ELEMENTARY.  An L1 four-noise mechanism
      with Laplace noise looks genuinely reachable, unlike anything in the
      L2 family;
    - with NORMAL noise the outer integrand is [erf] at linear arguments,
      truncated to [|u| < 1], which is an Owen's-T / bivariate-normal
      quantity and not elementary.

  Either way the 4-to-2 reduction is still blocked by F15, which is
  distribution- and metric-independent.

  So the ordering is: L1 + Laplace is the most promising unbuilt mechanism
  in this directory tree, and it is blocked only by F15.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import ClassicalDescription.
Require Import CPHL.
Require Import SampleBeforeLoop.
Require Import HalfLaplaceRejection.
Require Import GaussianDifference.
Require Import NormalDistance.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * The program *)

Definition nb_n1 : RealProgramVar := real_program_var "nb_n1".
Definition nb_n3 : RealProgramVar := real_program_var "nb_n3".
Definition nb_n2 : RealProgramVar := real_program_var "nb_n2".
Definition nb_n4 : RealProgramVar := real_program_var "nb_n4".
Definition nb_ux : RealProgramVar := real_program_var "nb_ux".
Definition nb_uy : RealProgramVar := real_program_var "nb_uy".
Definition nb_inside : BoolProgramVar := bool_program_var "nb_inside".

Definition nb_minus_one : Term := TConst (-1).

Definition nb_noise (b : R) : Distribution := <{ gaussian(0, b) }>.

Definition nb_dx (px cx : R) : Term :=
  <{ ($(px) + nb_n1) + $(nb_minus_one) * ($(cx) + nb_n3) }>.
Definition nb_dy (py cy : R) : Term :=
  <{ ($(py) + nb_n2) + $(nb_minus_one) * ($(cy) + nb_n4) }>.

Definition nb_abs (x : RealProgramVar) : Cmd :=
  <{ if x < 0 then x := $(nb_minus_one) * x else skip end }>.

Definition nb_test : CFormula := <{ (nb_ux + nb_uy) < 1 }>.

Definition nb_prog (px py cx cy b : R) : Cmd :=
  <{ nb_n1 sample $(nb_noise b);
     nb_n3 sample $(nb_noise b);
     nb_n2 sample $(nb_noise b);
     nb_n4 sample $(nb_noise b);
     nb_ux := $(nb_dx px cx);
     $(nb_abs nb_ux);
     nb_uy := $(nb_dy py cy);
     $(nb_abs nb_uy);
     nb_inside b= $(nb_test) }>.

(** The weakest precondition of the sampling prefix, for the event that the
    rest of the program tests.  Well-formed -- the assertion logic expresses
    it -- which is the same situation as NormalDisk.v. *)
Definition nb_construct (px py cx cy b : R) : PConstruct :=
  [[ integral nb_n1 ~ $(nb_noise b),
     integral nb_n3 ~ $(nb_noise b),
     integral nb_n2 ~ $(nb_noise b),
     integral nb_n4 ~ $(nb_noise b),
     indicator[ ($(nb_dx px cx) < 1) /\ ($(nb_dy py cy) < 1) ] ]].

(** * The open statement

    STATED, NOT PROVED.  [r] is the L1-ball probability; see the header for
    why it is out of reach and for the [L1 + Laplace] variant that is not. *)
Definition nb_target (px py cx cy b r : R) : Prop :=
  {{ Pr[true] = 1 }}
    $(nb_prog px py cx cy b)
  {{ Pr[nb_inside] = $(r) }}.
