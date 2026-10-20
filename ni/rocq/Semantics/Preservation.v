From Stdlib Require Import Morphisms.
From Paco Require Import paco.
From ITree Require Import ITree ITreeFacts Events.State Events.StateFacts.
From Vellvm Require Import Params LLVMEvents Semantics.InterpretationStack Semantics.TopLevel.
From GenLLVMNI.Semantics Require Import Observation MemoryObservation MemoryExecution.
Import ITreeNotations.
Local Open Scope itree_scope.

Lemma erase_lift {O E R} (t : itree E R) :
  erase (@lift O E R t) ≈ t.
Proof.
  unfold erase, lift. rewrite interp_translate.
  change (interp ITree.trigger t ≈ t).
  apply interp_trigger_h.
Qed.

Lemma erase_interp_state {O E F S A}
    (observed : E ~> Monads.stateT S (itree (ObservationE O +' F)))
    (original : E ~> Monads.stateT S (itree F))
    (handlers_agree : forall X (e : E X) s,
      erase (observed _ e s) ≈ original _ e s) :
  forall (t : itree E A) s,
    erase (interp_state observed t s) ≈ interp_state original t s.
Proof.
  unfold erase in *.
  einit. ecofix CIH. intros t s.
  rewrite !unfold_interp_state.
  destruct (observe t) as [value | next | X e k]; cbn [_interp_state].
  - rewrite interp_ret. eret.
  - rewrite interp_tau. etau.
  - rewrite interp_bind.
    ebind. econstructor.
    + apply handlers_agree.
    + intros [s' value] other EQ. subst other. cbn.
      rewrite interp_tau. etau.
Qed.

Lemma erase_deliver {O E} (o : O) :
  erase (@deliver O E o) ≈ Ret tt.
Proof.
  unfold erase, deliver. rewrite interp_trigger.
  cbn. reflexivity.
Qed.

Lemma erase_before {O E R} (payload : option O) (body : unit -> itree E R) :
  erase (before deliver payload (fun _ => lift (body tt))) ≈ body tt.
Proof.
  destruct payload as [o |]; cbn [before].
  - unfold erase at 1. rewrite interp_bind.
    change (erase (@deliver O E o) >>=
      (fun _ => erase (@lift O E R (body tt))) ≈ body tt).
    rewrite erase_deliver, bind_ret_l. apply erase_lift.
  - apply erase_lift.
Qed.

(* This statement includes all original terminal events and the concrete state. *)
Lemma erase_memory_handler {Pa : Params} X (e : MCFGEtop X) s :
  erase (memory_handler deliver _ e s) ≈ interp_vellvm_h e s.
Proof.
  unfold memory_handler.
  exact (erase_before (top_memory_payload e) (fun _ => interp_vellvm_h e s)).
Qed.

Theorem erase_interp_memory_observed {Pa : Params} R (t : MCFGtop R) s :
  erase (interp_memory_observed t s) ≈ interp_mcfg t s.
Proof.
  unfold interp_memory_observed, interp_mcfg.
  apply erase_interp_state. intros. apply erase_memory_handler.
Qed.

Theorem erase_interpreter_memory_gen {Pa : Params} ret_ty entry args prog :
  erase (interpreter_memory_gen ret_ty entry args prog) ≈
    interpreter_gen ret_ty entry args prog.
Proof.
  unfold interpreter_memory_gen, interpreter_gen.
  apply erase_interp_memory_observed.
Qed.
