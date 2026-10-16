(** Interfaces for relative completeness. The certificate is indexed by both
    the command C and its expectation transformer T_C. Nothing here assumes
    that a certificate exists, even for a loop-free command. *)
Require Import CPHL.

(** Loop-freedom is purely syntactic. In particular, neither toss probabilities
    nor real distribution parameters are required to be valid. *)
Inductive loop_free : Cmd -> Prop :=
  | LFSkip : loop_free CSkip
  | LFRealAssign : forall x t, loop_free (CRealAssign x t)
  | LFBoolAssign : forall b beta, loop_free (CBoolAssign b beta)
  | LFBoolToss : forall b r, loop_free (CBoolToss b r)
  | LFRealSample : forall x d, loop_free (CRealSample x d)
  | LFSeq : forall C1 C2,
      loop_free C1 -> loop_free C2 -> loop_free (CSeq C1 C2)
  | LFIf : forall guard C1 C2,
      loop_free C1 -> loop_free C2 -> loop_free (CIf guard C1 C2).

Lemma loop_free_while_false guard body : ~ loop_free (CWhile guard body).
Proof. intro H; inversion H. Qed.

(** These are probabilistic logical variables only. Program variables and
    classical logical coordinates may still occur in the transformed reward. *)
Definition expectation_transformer_no_prob_vars
    (T_C : PConstruct -> Pterm) : Prop :=
  forall q y, ~ prob_logic_var_occurs_pterm y (T_C q).

(** T_C(q) is evaluated on the input state; q is integrated against the
    output measure. The external logical assignment is preserved by run. *)
Definition expectation_transformer_correct
    (C : Cmd) (T_C : PConstruct -> Pterm) : Prop :=
  forall ps q, pstate_admissible ps ->
    pterm_eval (T_C q) ps =
    expectation (pstate_measure (CommandSemantics.run C ps)) (q_eval q).

(** The syntactic obligation is separate from semantic correctness. The
    equality triple must be derivable using the existing Hoare calculus. *)
Definition expectation_transformer_derivable
    (C : Cmd) (T_C : PConstruct -> Pterm) : Prop :=
  forall q y,
    hoare_derivable (p_eq (PVar y) (T_C q)) C
      (p_eq (PVar y) (PExpect q)).

(** No loop_free hypothesis belongs in this interface: future loop classes
    may use it if they can discharge these same exactness obligations.
    The full weakest-preterm transformation will later extend T_C through
    constants, logical variables, addition, and multiplication. *)
Record exact_expectation_certificate
    (C : Cmd) (T_C : PConstruct -> Pterm) : Prop := {
  certificate_no_prob_vars : expectation_transformer_no_prob_vars T_C;
  certificate_correct : expectation_transformer_correct C T_C;
  certificate_derivable : expectation_transformer_derivable C T_C
}.
