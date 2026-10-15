(**
  NormalBallL1.v

  Program ([nb_prog px py cx cy b]):
      nb_n1 <- sample(gaussian(0, b));  nb_n3 <- sample(gaussian(0, b));
      nb_n2 <- sample(gaussian(0, b));  nb_n4 <- sample(gaussian(0, b));
      nb_ux := (px + nb_n1) - (cx + nb_n3);
      if nb_ux < 0 then nb_ux := -1 * nb_ux else skip end;
      nb_uy := (py + nb_n2) - (cy + nb_n4);
      if nb_uy < 0 then nb_uy := -1 * nb_uy else skip end;
      nb_inside := (nb_ux + nb_uy < 1)
  Triple (NOT PROVED; stated as [nb_target], for any precondition eta):
      { eta }
        nb_prog px py cx cy b
      { Pr[nb_inside] = E[ integral nb_z1 ~ gaussian(0, b), integral nb_z3 ~ gaussian(0, b),
                            integral nb_z2 ~ gaussian(0, b), integral nb_z4 ~ gaussian(0, b),
                            indicator[ |dx| + |dy| < 1 ] ] }
      where dx = (px + nb_z1) - (cx + nb_z3), dy = (py + nb_z2) - (cy + nb_z4), and
      |dx| + |dy| < 1 is written as the four linear constraints +-dx +- dy < 1
      ([nb_construct]).
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
Require Import CPHL.

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

Definition nb_z1 : RealProgramVar := real_program_var "nb_z1".
Definition nb_z3 : RealProgramVar := real_program_var "nb_z3".
Definition nb_z2 : RealProgramVar := real_program_var "nb_z2".
Definition nb_z4 : RealProgramVar := real_program_var "nb_z4".

Definition nb_ex (px cx : R) : Term :=
  <{ ($(px) + nb_z1) + $(nb_minus_one) * ($(cx) + nb_z3) }>.
Definition nb_ey (py cy : R) : Term :=
  <{ ($(py) + nb_z2) + $(nb_minus_one) * ($(cy) + nb_z4) }>.

(** The L1-ball probability: [|ex| + |ey| < 1] iff all four sign
    combinations [+-ex +- ey] are below [1]. *)
Definition nb_construct (px py cx cy b : R) : PConstruct :=
  [[ integral nb_z1 ~ $(nb_noise b),
     integral nb_z3 ~ $(nb_noise b),
     integral nb_z2 ~ $(nb_noise b),
     integral nb_z4 ~ $(nb_noise b),
     indicator[ (($(nb_ex px cx) + $(nb_ey py cy)) < 1)
                /\ (($(nb_ex px cx) + $(nb_minus_one) * $(nb_ey py cy)) < 1)
                /\ (($(nb_minus_one) * $(nb_ex px cx) + $(nb_ey py cy)) < 1)
                /\ (($(nb_minus_one) * $(nb_ex px cx)
                     + $(nb_minus_one) * $(nb_ey py cy)) < 1) ] ]].

(** * The open statement (unproved target)

    Both branches of each [if] carry mass here (the guards test the
    perturbed differences), so [HIfEq] produces a sum of two auxiliary
    logic variables, each equal to an expectation; [HElimv] cannot remove
    them while they occur in the postcondition, and CPHL has no other rule
    that eliminates them. *)
Definition nb_target (px py cx cy b : R) (eta : PFormula) : Prop :=
  {{ $(eta) }}
    $(nb_prog px py cx cy b)
  {{ Pr[nb_inside] = E[ $(nb_construct px py cx cy b) ] }}.
