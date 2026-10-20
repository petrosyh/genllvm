From ITree Require Import ITree Events.State.
From Vellvm Require Import Syntax Semantics Handlers Params.
From Vellvm Require Import Interfaces.Memory Implementations.Memory.
From GenLLVMNI.Semantics Require Import Observation MemoryObservation.
Import ITreeNotations.
Local Open Scope itree_scope.

Section Execution.
  Context {Pa : Params}.

  Definition memory_effects := ObservationE memory_observation +' MCFGEbot.

  (* Reuse the entire stock dispatcher, including its concrete state updates.
     The added action runs before the original request is handled. *)
  Definition memory_handler (send : memory_observation -> itree memory_effects unit)
      : MCFGEtop ~> Monads.stateT FusedS (itree memory_effects) :=
    fun X e s =>
      before send (top_memory_payload e) (fun _ => lift (interp_vellvm_h e s)).

  Definition interp_memory_observed {R} (t : itree MCFGEtop R) (s : FusedS)
      : itree memory_effects (FusedS * R) :=
    interp_state (memory_handler deliver) (interp_intrinsics t) s.

  (* This entry is memory-only: it does not yet observe calls or branches. *)
  Definition interpreter_memory_gen
      (ret_ty : dtyp) (entry : function_id)
      (args : MCFGtop (list dvalue)) (prog : ll_toplevel_entities)
      : itree memory_effects (FusedS * dvalue) :=
    let t :=
      argv <- args ;;
      denote_vellvm ret_ty entry argv
        (convert_types (mcfg_of_tle (link PREDEFINED_FUNCTIONS prog)))
    in
    interp_memory_observed t
      (initial_state, ((Build_stack_frame Maps.empty None None, nil), Maps.empty)).
End Execution.
