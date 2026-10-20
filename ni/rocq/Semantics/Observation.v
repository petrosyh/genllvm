From ITree Require Import ITree InterpFacts Events.State.
Import ITreeNotations.
Local Open Scope itree_scope.

(* The payload type is independent of the event used to deliver it. *)
Variant ObservationE (O : Type) : Type -> Type :=
| Observe : O -> ObservationE O unit.

Arguments Observe {O} _.

Definition deliver {O E} (o : O) : itree (ObservationE O +' E) unit :=
  ITree.trigger (inl1 (Observe o)).

Definition erase_handler {O E} : (ObservationE O +' E) ~> itree E :=
  fun X e =>
    match e with
    | inl1 obs =>
        match obs in ObservationE _ T return itree E T with
        | Observe _ => Ret tt
        end
    | inr1 original => ITree.trigger original
    end.

Definition erase {O E R} (t : itree (ObservationE O +' E) R) : itree E R :=
  interp erase_handler t.

(* No selected observation means no delivery computation. *)
Definition before {O E R} (send : O -> itree E unit)
    (payload : option O) (body : unit -> itree E R) : itree E R :=
  match payload with
  | None => body tt
  | Some o => send o ;; body tt
  end.

Definition lift {O E R} (t : itree E R) : itree (ObservationE O +' E) R :=
  translate inr1 t.
