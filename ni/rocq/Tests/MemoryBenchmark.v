From Stdlib Require Import List ZArith.
From ITree Require Import ITree Events.State.
From Vellvm Require Import Syntax Semantics Params ParamsV IPtrInfinite.
From GenLLVMNI.Semantics Require Import Observation MemoryObservation MemoryExecution Runner.
From GenLLVMNI.Tests Require Import MemoryFixtures.
Import ITreeNotations ListNotations.
Local Open Scope itree_scope.
#[local] Existing Instance test_params.

Fixpoint read_loop (count : nat) (p : dvalue) : MCFGtop dvalue :=
  match count with
  | 0%nat => Ret (word32 7)
  | S n => _ <- load ty32 p ;; read_loop n p
  end.

Fixpoint local_loop (count : nat) : MCFGtop dvalue :=
  match count with
  | 0%nat => Ret (word32 7)
  | S n =>
      lwrite (Anon 0) (word32 7) ;;
      _ <- lread (Anon 0) ;; local_loop n
  end.

Definition workload (memory : bool) (count : nat) : MCFGtop dvalue :=
  if memory then
    p <- alloca ty32 1 None ;;
    store ty32 p (word32 7) ;;
    read_loop count p
  else local_loop count.

(* Measurement controls only. Neither of these is an NI execution oracle. *)
Fixpoint run_stock {A} (fuel : nat) (t : MCFGbot A)
    : run_result memory_observation stop_reason A :=
  match fuel with
  | 0%nat => OutOfFuel []
  | S n =>
      match observe t with
      | RetF value => Normal [] value
      | TauF next => run_stock n next
      | VisF _ e k =>
          match residual_step _ e with
          | Stop reason => Stopped [] reason
          | Resume answer =>
              match n with
              | 0%nat => OutOfFuel []
              | S _ => run_stock n (k answer)
              end
          end
      end
  end.

Fixpoint run_discard {A} (fuel : nat) (t : itree memory_effects A)
    : run_result memory_observation stop_reason A :=
  match fuel with
  | 0%nat => OutOfFuel []
  | S n =>
      match observe t with
      | RetF value => Normal [] value
      | TauF next => run_discard n next
      | VisF _ (inl1 obs) k =>
          (match obs in ObservationE _ X
            return (X -> itree memory_effects A) -> run_result memory_observation stop_reason A with
           | Observe _ => fun next =>
               match n with
               | 0%nat => OutOfFuel []
               | S _ => run_discard n (next tt)
               end
           end) k
      | VisF _ (inr1 e) k =>
          match residual_step _ e with
          | Stop reason => Stopped [] reason
          | Resume answer =>
              match n with
              | 0%nat => OutOfFuel []
              | S _ => run_discard n (k answer)
              end
          end
      end
  end.

Definition benchmark_stock memory count fuel :=
  run_stock fuel (interp_mcfg (workload memory count) test_state).

Definition benchmark_disabled memory count fuel :=
  run residual_step fuel []
    (interp_state (memory_handler (fun _ => Ret tt))
      (interp_intrinsics (workload memory count)) test_state).

Definition benchmark_discard memory count fuel :=
  run_discard fuel (interp_memory_observed (workload memory count) test_state).

Definition benchmark_observed memory count fuel :=
  run residual_step fuel []
    (interp_memory_observed (workload memory count) test_state).
