From Vellvm Require Import Syntax Params DynamicValues LLVMEvents.
From GenLLVMNI.Semantics Require Import Observation.
From ITree Require Import ITree.

Section Payload.
  Context {Pa : Params}.

  (* Keep the complete request address, including an invalid dvalue. *)
  Inductive memory_observation : Type :=
  | OLoad : dtyp -> dvalue -> memory_observation
  | OStore : dtyp -> dvalue -> memory_observation.

  Definition memory_payload {X} (e : MemoryE X) : option memory_observation :=
    match e with
    | Load ty address => Some (OLoad ty address)
    | Store ty address _ => Some (OStore ty address)
    | _ => None
    end.

  (* Memory requests are still present here, after intrinsic interpretation. *)
  Definition top_memory_payload {X} (e : MCFGEtop X)
      : option memory_observation :=
    match e with
    | inr1 (inr1 (inr1 (inr1 (inl1 request)))) => memory_payload request
    | _ => None
    end.
End Payload.
