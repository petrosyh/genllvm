From Stdlib Require Import List String ZArith Bool.
From ITree Require Import ITree.
From Vellvm Require Import Syntax Semantics Handlers Params ParamsV IPtrInfinite
  Interfaces.Memory Implementations.Memory Integers.
From GenLLVMNI.Semantics Require Import Observation MemoryObservation MemoryExecution Runner.
Import ITreeNotations ListNotations.
Local Open Scope itree_scope.
Local Open Scope string_scope.
#[local] Existing Instance IPZ.
#[local] Existing Instance IPZTheory.
#[local] Instance test_params : Params := @ParamsV IPZ IPZTheory.

Definition test_state : FusedS :=
  (initial_state, ((Build_stack_frame Maps.empty None None, []), Maps.empty)).
Definition ty32 := DTYPE_I 32%positive.
Definition word32 (z : Z) : dvalue := DVALUE_I 32 (repr z).
Definition bad_address : dvalue := DVALUE_Pointer (4096%Z, None).
Definition same_value := @DynamicValues.dvalue_eqb (@ParamsV IPZ IPZTheory).

Definition execute_memory {A} (t : MCFGtop A) :=
  run residual_step 1000 [] (interp_memory_observed t test_state).

Definition roundtrip : MCFGtop (dvalue * dvalue) :=
  p <- alloca ty32 1 None ;;
  store ty32 p (word32 7) ;;
  value <- load ty32 p ;;
  Ret (p, value).

Definition check_roundtrip (_ : unit) : bool :=
  match execute_memory roundtrip with
  | Normal [OStore (DTYPE_I 32) p; OLoad (DTYPE_I 32) q] (_, (a, value)) =>
      same_value p a && same_value q a && same_value value (word32 7)
  | _ => false
  end.

Definition check_bad_load (_ : unit) : bool :=
  let request : MCFGEtop dvalue :=
    inr1 (inr1 (inr1 (inr1 (inl1 (Load ty32 bad_address))))) in
  (* One step delivers the request but must not execute its failing handler.
     The extraction harness also checks that only the full run prints UB. *)
  match run residual_step 1 []
          (memory_handler deliver _ request test_state),
        execute_memory (load ty32 bad_address) with
  | OutOfFuel [OLoad (DTYPE_I 32) p],
    Stopped [OLoad (DTYPE_I 32) address] UB =>
      same_value p bad_address && same_value address bad_address
  | _, _ => false
  end.

Definition check_bad_store (_ : unit) : bool :=
  match execute_memory (store ty32 bad_address (word32 7)) with
  | Stopped [OStore (DTYPE_I 32) address] UB => same_value address bad_address
  | _ => false
  end.

Definition check_non_pointer (_ : unit) : bool :=
  match execute_memory (load ty32 (word32 9)) with
  | Stopped [OLoad (DTYPE_I 32) address] UB => same_value address (word32 9)
  | _ => false
  end.

Definition check_zero_store (_ : unit) : bool :=
  let ty := DTYPE_Struct true [] in
  let t : MCFGtop dvalue :=
    p <- alloca ty 1 None ;; store ty p (DVALUE_Struct true []) ;; Ret p in
  match execute_memory t with
  | Normal [OStore (DTYPE_Struct true []) address] (_, p) => same_value address p
  | _ => false
  end.

Definition check_failure_prefix (_ : unit) : bool :=
  let t : MCFGtop unit :=
    p <- alloca ty32 1 None ;;
    store ty32 p (word32 7) ;;
    _ <- load ty32 bad_address ;; Ret tt in
  match execute_memory t with
  | Stopped [OStore (DTYPE_I 32) p; OLoad (DTYPE_I 32) q] UB =>
      negb (same_value p q) && same_value q bad_address
  | _ => false
  end.

(* va_start's Store is emitted by the intrinsic interpreter, not the input. *)
Definition check_intrinsic_store (_ : unit) : bool :=
  let t : MCFGtop dvalue :=
    p <- alloca DTYPE_Pointer 1 None ;;
    _ <- LLVMEvents.intrinsic (Pa := test_params) (E := MCFGEtop)
      DTYPE_Void "llvm.va_start" [p] (Some (0%Z, None)) ;;
    Ret p in
  match execute_memory t with
  | Normal [OStore DTYPE_Pointer address] (_, p) => same_value address p
  | _ => false
  end.

(* Rejected before emitting Store: there must be no invented observation. *)
Definition check_poison_intrinsic (_ : unit) : bool :=
  let t : MCFGtop (exc + dvalue) :=
    LLVMEvents.intrinsic (Pa := test_params) (E := MCFGEtop)
      DTYPE_Void "llvm.va_start" [DVALUE_Base (DVALUE_Poison DTYPE_Pointer)]
      (Some (0%Z, None)) in
  match execute_memory t with
  | Stopped [] UB => true
  | _ => false
  end.

Definition marker := OLoad ty32 bad_address.
Definition stop_tree (kind : nat) : itree memory_effects unit :=
  deliver marker ;;
  match kind with
  | 0%nat => raiseUB "NI fixture UB"
  | 1%nat => raiseOOM "NI fixture OOM"
  | _ => raise "NI fixture failure"
  end.

Definition check_ub_boundary (_ : unit) : bool :=
  match run residual_step 1 [] (stop_tree 0),
        run residual_step 2 [] (stop_tree 0) with
  | OutOfFuel [_], Stopped [_] UB => true
  | _, _ => false
  end.

Definition check_oom_prefix (_ : unit) : bool :=
  match run residual_step 2 [] (stop_tree 1) with
  | Stopped [OLoad (DTYPE_I 32) address] OOM => same_value address bad_address
  | _ => false
  end.

Definition check_failure_kind (_ : unit) : bool :=
  match run residual_step 2 [] (stop_tree 2) with
  | Stopped [_] Failure => true
  | _ => false
  end.

Definition check_ret_boundary (_ : unit) : bool :=
  let t : itree memory_effects unit := Ret tt in
  match run residual_step 0 [] t,
        run residual_step 1 [] t with
  | OutOfFuel [], Normal [] tt => true
  | _, _ => false
  end.

CoFixpoint spinning : itree memory_effects unit := Tau spinning.

Definition check_loop_prefix (_ : unit) : bool :=
  match run residual_step 5 [] (deliver marker ;; spinning) with
  | OutOfFuel [OLoad (DTYPE_I 32) address] => same_value address bad_address
  | _ => false
  end.

Definition check_residuals (_ : unit) : bool :=
  let execute (t : itree memory_effects unit) :=
    run residual_step 3 [] (deliver marker ;; t) in
  match execute (io_stdout []), execute (io_stderr []),
        execute (_ <- external_call DTYPE_Void bad_address [] ;; Ret tt),
        execute (raiseLLVM (word32 7)) with
  | Stopped [_] ProgramStdout, Stopped [_] ProgramStderr,
    Stopped [_] UnsupportedExternalCall, Stopped [_] (LLVMException e) =>
      same_value e (word32 7)
  | _, _, _, _ => false
  end.

Definition check_debug_resume (_ : unit) : bool :=
  let t : itree memory_effects unit :=
    deliver marker ;; debug "NI fixture debug" ;; Ret tt in
  (* Debug consumes one step and resumes without adding an observation. *)
  match run residual_step 2 [] t, run residual_step 3 [] t with
  | OutOfFuel [OLoad (DTYPE_I 32) p], Normal [OLoad (DTYPE_I 32) q] tt =>
      same_value p bad_address && same_value q bad_address
  | _, _ => false
  end.

Definition empty_main : ll_toplevel_entities :=
  [TLE_Definition
     {| df_prototype :=
          {| dc_name := Name "main";
             dc_type := TYPE_Function (TYPE_I 32) [] false;
             dc_param_attrs := ([], []); dc_attrs := []; dc_annotations := [] |};
        df_args := [];
        df_instrs :=
          ({| blk_id := Name "entry"; blk_phis := []; blk_code := [];
              blk_term := (IVoid 0, TERM_Ret (TYPE_I 32, EXP_Integer (Z.to_num_int 7)), []);
              blk_comments := None |}, []) |}].

Definition initialized_global : global typ :=
  {| g_ident := Name "g"; g_typ := TYPE_I 32; g_constant := false;
     g_exp := Some (EXP_Integer (Z.to_num_int 5));
     g_externally_initialized := false; g_alias := false; g_annotations := [] |}.

Definition check_preparation (_ : unit) : bool :=
  let prepare : MCFGtop (list dvalue) :=
    p <- alloca ty32 1 None ;; store ty32 p (word32 11) ;; Ret [] in
  match run residual_step 1000 []
      (interpreter_memory_gen ty32 (Name "main") prepare
        (TLE_Global initialized_global :: empty_main)) with
  | Normal [OStore (DTYPE_I 32) p; OStore (DTYPE_I 32) q;
            OStore (DTYPE_Struct true []) _] (_, value) =>
      negb (same_value p q) && same_value value (word32 7)
  | _ => false
  end.

Definition check_access_width (_ : unit) : bool :=
  let ty64 := DTYPE_I 64 in
  let t : MCFGtop dvalue :=
    p <- alloca ty64 1 None ;;
    store ty64 p (DVALUE_I 64 (repr 0)) ;;
    _ <- load ty32 p ;; Ret p in
  match execute_memory t with
  | Normal [OStore (DTYPE_I 64) p; OLoad (DTYPE_I 32) q] (_, a) =>
      same_value p a && same_value q a
  | _ => false
  end.

Definition check_memory_failure (_ : unit) : bool :=
  let t : MCFGtop dvalue :=
    p <- alloca ty32 1 None ;;
    store ty32 p (word32 7) ;;
    conv Addrspacecast DTYPE_Pointer p DTYPE_Pointer in
  match execute_memory t with
  | Stopped [OStore (DTYPE_I 32) _] Failure => true
  | _ => false
  end.

Definition check_entry_frame (_ : unit) : bool :=
  match run residual_step 1000 []
      (interpreter_memory_gen ty32 (Name "main") (Ret []) empty_main) with
  | Normal [OStore (DTYPE_Struct true []) _] (_, value) => same_value value (word32 7)
  | _ => false
  end.

Definition checks : list (string * (unit -> bool)) :=
  [("roundtrip", check_roundtrip); ("bad_load", check_bad_load);
   ("bad_store", check_bad_store); ("non_pointer", check_non_pointer);
   ("zero_store", check_zero_store); ("failure_prefix", check_failure_prefix);
   ("intrinsic_store", check_intrinsic_store); ("poison_intrinsic", check_poison_intrinsic);
   ("ub_boundary", check_ub_boundary); ("oom_prefix", check_oom_prefix);
   ("failure_kind", check_failure_kind); ("ret_boundary", check_ret_boundary);
   ("loop_prefix", check_loop_prefix); ("residuals", check_residuals);
   ("debug_resume", check_debug_resume); ("entry_frame", check_entry_frame);
   ("preparation", check_preparation); ("access_width", check_access_width);
   ("memory_failure", check_memory_failure)].
