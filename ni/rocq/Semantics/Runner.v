From Stdlib Require Import List.
From ITree Require Import ITree.
From Vellvm Require Import Params DynamicValues LLVMEvents.
From GenLLVMNI.Semantics Require Import Observation.

Set Universe Polymorphism.

Inductive event_action (Reason X : Type) : Type :=
| Resume : X -> event_action Reason X
| Stop : Reason -> event_action Reason X.
Arguments Resume {Reason X} _.
Arguments Stop {Reason X} _.

Inductive run_result (O Reason A : Type) : Type :=
| Normal : list O -> A -> run_result O Reason A
| Stopped : list O -> Reason -> run_result O Reason A
| OutOfFuel : list O -> run_result O Reason A.
Arguments Normal {O Reason A} _ _.
Arguments Stopped {O Reason A} _ _.
Arguments OutOfFuel {O Reason A} _.

(* Stdlib.List.rev extracts to append-based reversal. Use the linear variant. *)
Definition finish_trace {O} (rev_trace : list O) : list O :=
  List.rev_append rev_trace nil.

(* The budget is checked before forcing the tree. A positive budget processes
   one Ret, Tau, or Vis. The result itself does not require another step. *)
Fixpoint run {O E Reason A}
    (handle : forall X, E X -> event_action Reason X)
    (fuel : nat) (rev_trace : list O)
    (tree : itree (ObservationE O +' E) A) : run_result O Reason A :=
  match fuel with
  | 0 => OutOfFuel (finish_trace rev_trace)
  | S remaining =>
      match observe tree with
      | RetF value => Normal (finish_trace rev_trace) value
      | TauF next => run handle remaining rev_trace next
      | VisF _ (inl1 obs) k =>
          (* Also avoid evaluating k when the extracted budget is exhausted. *)
          (match obs in ObservationE _ X
             return (X -> itree (ObservationE O +' E) A) -> run_result O Reason A with
           | Observe o => fun next =>
               match remaining with
               | 0 => OutOfFuel (finish_trace (o :: rev_trace))
               | S _ => run handle remaining (o :: rev_trace) (next tt)
               end
           end) k
      | VisF _ (inr1 e) k =>
          match handle _ e with
          | Resume answer =>
              match remaining with
              | 0 => OutOfFuel (finish_trace rev_trace)
              | S _ => run handle remaining rev_trace (k answer)
              end
          | Stop reason => Stopped (finish_trace rev_trace) reason
          end
      end
  end.

Section Residual.
  Context {Pa : Params}.

  Inductive stop_reason :=
  | UB
  | OOM
  | Failure
  | LLVMException : exc -> stop_reason
  | UnsupportedExternalCall
  | ProgramStdout
  | ProgramStderr.

  (* No dummy value is supplied for an external call or a void response. *)
  Definition residual_step : forall X, MCFGEbot X -> event_action stop_reason X.
  Proof.
    intros X [e | [e | [e | [e | [e | e]]]]].
    - destruct e.
      + exact (Stop UnsupportedExternalCall).
      + exact (Stop ProgramStdout).
      + exact (Stop ProgramStderr).
    - destruct e. exact (Stop OOM).
    - destruct e as [value]. exact (Stop (LLVMException value)).
    - destruct e. exact (Stop UB).
    - destruct e. exact (Resume tt).
    - destruct e. exact (Stop Failure).
  Defined.
End Residual.
