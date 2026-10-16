(** Assembly only: loop transformers are deliberately outside this construction.
    The underlying certificate and closure results remain general. *)
Require Import CPHL Soundness.HoareSoundness Completeness.Interface
  Completeness.AtomicCertificates Completeness.SamplingCertificates
  Completeness.ConditionalCertificates Completeness.SequentialCertificates
  Completeness.WeakestPreterm Completeness.WeakestPrecondition.

Fixpoint build_expectation_transformer (C : Cmd) : option (PConstruct -> Pterm) :=
  match C with
  | CSkip => Some skip_expectation_transformer
  | CRealAssign x t => Some (real_assign_expectation_transformer x t)
  | CBoolAssign b beta => Some (bool_assign_expectation_transformer b beta)
  | CBoolToss b r => Some (toss_expectation_transformer b r)
  | CRealSample x d => Some (sample_expectation_transformer x d)
  | CSeq C1 C2 =>
      match build_expectation_transformer C1, build_expectation_transformer C2 with
      | Some T1, Some T2 => Some (seq_expectation_transformer C1 T1 T2)
      | _, _ => None
      end
  | CIf guard C1 C2 =>
      match build_expectation_transformer C1, build_expectation_transformer C2 with
      | Some T1, Some T2 => Some (if_expectation_transformer guard T1 T2)
      | _, _ => None
      end
  | CWhile _ _ => None
  end.

Theorem build_expectation_transformer_succeeds C :
  (exists T_C, build_expectation_transformer C = Some T_C) <-> loop_free C.
Proof.
  split.
  - induction C; cbn [build_expectation_transformer]; intros [T HT]; try constructor.
    + destruct (build_expectation_transformer C1) eqn:E1; try discriminate.
      destruct (build_expectation_transformer C2) eqn:E2; try discriminate.
      apply IHC1; eauto.
    + destruct (build_expectation_transformer C1) eqn:E1; try discriminate.
      destruct (build_expectation_transformer C2) eqn:E2; try discriminate.
      apply IHC2; eauto.
    + destruct (build_expectation_transformer C1) eqn:E1; try discriminate.
      destruct (build_expectation_transformer C2) eqn:E2; try discriminate.
      apply IHC1; eauto.
    + destruct (build_expectation_transformer C1) eqn:E1; try discriminate.
      destruct (build_expectation_transformer C2) eqn:E2; try discriminate.
      apply IHC2; eauto.
    + discriminate.
  - intro H; induction H; cbn [build_expectation_transformer]; try (eexists; reflexivity).
    + destruct IHloop_free1 as [T1 E1]; destruct IHloop_free2 as [T2 E2].
      rewrite E1, E2; eexists; reflexivity.
    + destruct IHloop_free1 as [T1 E1]; destruct IHloop_free2 as [T2 E2].
      rewrite E1, E2; eexists; reflexivity.
Qed.

Theorem build_expectation_transformer_certificate C T_C :
  build_expectation_transformer C = Some T_C -> exact_expectation_certificate C T_C.
Proof.
  revert T_C; induction C; intros T HT; cbn [build_expectation_transformer] in HT.
  - inversion HT; subst; apply skip_certificate.
  - inversion HT; subst; apply real_assign_certificate.
  - inversion HT; subst; apply bool_assign_certificate.
  - inversion HT; subst; apply toss_certificate.
  - inversion HT; subst; apply sample_certificate.
  - destruct (build_expectation_transformer C1) eqn:E1; try discriminate.
    destruct (build_expectation_transformer C2) eqn:E2; try discriminate.
    inversion HT; subst; apply seq_certificate; [apply IHC1 | apply IHC2]; reflexivity.
  - destruct (build_expectation_transformer C1) eqn:E1; try discriminate.
    destruct (build_expectation_transformer C2) eqn:E2; try discriminate.
    inversion HT; subst; apply if_certificate; [apply IHC1 | apply IHC2]; reflexivity.
  - discriminate.
Qed.

(** Extract an existing Some result; the impossible None branch uses only
    False elimination, not a choice principle or an assumed transformer. *)
Definition transformer_from_option (o : option (PConstruct -> Pterm))
    (H : exists T, o = Some T) : PConstruct -> Pterm.
Proof.
  destruct o as [T |].
  - exact T.
  - exfalso; destruct H as [T HT]; discriminate.
Defined.

Lemma transformer_from_option_spec o : forall H,
  o = Some (transformer_from_option o H).
Proof.
  destruct o as [T |]; intro H.
  - reflexivity.
  - destruct H as [T HT]; discriminate.
Qed.

Definition loop_free_transformer C (H : loop_free C) : PConstruct -> Pterm :=
  transformer_from_option (build_expectation_transformer C)
    (proj2 (build_expectation_transformer_succeeds C) H).

Lemma loop_free_transformer_spec C H :
  build_expectation_transformer C = Some (loop_free_transformer C H).
Proof. apply transformer_from_option_spec. Qed.

Theorem loop_free_transformer_certificate C H :
  exact_expectation_certificate C (loop_free_transformer C H).
Proof. apply build_expectation_transformer_certificate; apply loop_free_transformer_spec. Qed.

Lemma loop_free_transformer_evidence_independent C (H1 H2 : loop_free C) :
  loop_free_transformer C H1 = loop_free_transformer C H2.
Proof.
  pose proof (loop_free_transformer_spec C H1).
  pose proof (loop_free_transformer_spec C H2); congruence.
Qed.

Definition loop_free_wpt C (H : loop_free C) p := wpt C (loop_free_transformer C H) p.
Definition loop_free_wp C (H : loop_free C) eta := wp C (loop_free_transformer C H) eta.

Theorem loop_free_wpt_correct C H p ps : pstate_admissible ps ->
  pterm_eval (loop_free_wpt C H p) ps = pterm_eval p (CommandSemantics.run C ps).
Proof. apply wpt_correct; apply (certificate_correct _ _ (loop_free_transformer_certificate C H)). Qed.

Theorem loop_free_wp_correct C H eta ps : pstate_admissible ps ->
  (psatisfies ps (loop_free_wp C H eta) <-> psatisfies (CommandSemantics.run C ps) eta).
Proof. apply wp_correct; apply (certificate_correct _ _ (loop_free_transformer_certificate C H)). Qed.

Theorem loop_free_wp_derivable C H eta :
  hoare_derivable (loop_free_wp C H eta) C eta.
Proof. apply wp_derivable; apply loop_free_transformer_certificate. Qed.

Theorem loop_free_relative_complete C pre post :
  loop_free C -> hoare_valid pre C post -> hoare_derivable pre C post.
Proof.
  intro H; exact (certified_relative_complete _ _ (loop_free_transformer_certificate C H) pre post).
Qed.

Theorem loop_free_valid_iff_derivable C pre post : loop_free C ->
  (hoare_valid pre C post <-> hoare_derivable pre C post).
Proof.
  intro H; split; [apply loop_free_relative_complete; exact H | apply hoare_derivable_sound].
Qed.
