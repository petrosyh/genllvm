From Stdlib Require Import List.
From ITree Require Import ITree.
From GenLLVMNI.Semantics Require Import Observation Runner.
Import ITreeNotations ListNotations.
Local Open Scope itree_scope.

Variant test_event : Type -> Type := Die : test_event Empty_set.
Definition handle_test : forall X, test_event X -> event_action unit X :=
  fun _ _ => Stop tt.

Definition failing : itree (ObservationE nat +' test_event) unit :=
  deliver 1 ;; deliver 2 ;;
  Vis (inr1 Die) (fun impossible : Empty_set => match impossible with end).

Example zero_before_ret : run handle_test 0 [] (Ret tt) = OutOfFuel (O := nat) [].
Proof. reflexivity. Qed.

Check run handle_test 1 [] (Ret tt).

Example positive_ret : run handle_test 1 [] (Ret tt) = Normal (O := nat) [] tt.
Proof. reflexivity. Qed.

Example terminal_cost : run handle_test 3 [] failing = Stopped [1; 2] tt.
Proof. vm_compute. reflexivity. Qed.

Example cutoff_before_terminal : run handle_test 2 [] failing = OutOfFuel [1; 2].
Proof. vm_compute. reflexivity. Qed.

CoFixpoint spin : itree (ObservationE nat +' test_event) unit := Tau spin.

Example zero_does_not_force : run handle_test 0 [] spin = OutOfFuel [].
Proof. reflexivity. Qed.

Example loop_prefix : run handle_test 5 [] (deliver 1 ;; spin) = OutOfFuel [1].
Proof. vm_compute. reflexivity. Qed.

Example existing_prefix : run handle_test 3 [0] failing = Stopped [0; 1; 2] tt.
Proof. vm_compute. reflexivity. Qed.
