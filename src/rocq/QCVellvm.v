 (** Framework for running QC vellvm tests. *)

From QuickChick Require Import QuickChick.
From Stdlib Require Import
  String
  ZArith
  List.
From Vellvm Require Import
  Params
  LLVMAst
  Syntax.ShowAST
  Syntax.ReprAST
  Semantics.LLVMEvents
  Semantics.InterpretationStack
  Semantics.DynamicValues
  ParamsV
  IPtrInfinite.
From GenLLVM Require Import
  GenAST
  QCExtractionFix.
From ITree Require Import
     ITree
     Interp.Recursion
     Events.Exception.

Import ListNotations.
Local Open Scope string_scope.

Extraction Blacklist String List Char Core Z Format int.

(* Useful names *)
Definition llprog := list (toplevel_entity typ (block typ * list (block typ))).

#[global] Instance show_lprog : Show llprog :=
  {| show := showProg |}.

(* Hide show instance... *)
Inductive PROG :=
| Prog : llprog -> PROG
.

#[global] Instance Show_PROG : Show PROG :=
  { show p := "" (* PROG: avoiding inefficient printing in QC, see #253 *) }.

#[global] Instance Show_sum {A B} `{Show A} `{Show B} : Show (A + B) :=
  { show :=  (fun x =>
    match x with
    | inl a => ("inl " ++ show a)%string
    | inr b => ("inr " ++ show b)%string
    end) }.

Definition gen_PROG : GenLLVM PROG
  := fmap Prog gen_llvm.

Axiom to_caml_str : string -> string.
Extract Constant to_caml_str =>
"fun (s: char list) ->
  let r = Bytes.create (List.length s) in
  let rec fill pos = function
  | [] -> r
  | c :: s -> Bytes.set r pos c; fill (pos + 1) s
  in Bytes.to_string (fill 0 s)".

(** Ocaml integers *)
Axiom oint : Type. (* ocaml int type *)
Extract Inlined Constant oint => "int".

Axiom oint_to_Z : oint -> Z.
Extract Inlined Constant oint_to_Z => "Big_int_Z.big_int_of_int".

Axiom oneq : oint -> oint -> bool.
Extract Inlined Constant oneq => "(<>)".

Axiom oeq : oint -> oint -> bool.
Extract Inlined Constant oeq => "(=)".

Axiom ozero : oint.
Extract Inlined Constant ozero => "0".

(** Write our LLVM program to a file ("temporary_vellvm.ll"), and then
    use clang to compile this file to an executable, which we then run in
    order to get the return code. *)
Axiom llc_command_ocaml : string -> oint.
Extract Constant llc_command_ocaml =>
          "fun prog ->
              let llvm_file_name = Filename.(concat (get_temp_dir_name ()) ""temporary_vellvm.ll"") in
              let test_binary = Filename.(concat (get_temp_dir_name ()) ""vellvmqc"") in
              let f = open_out llvm_file_name in
                Printf.fprintf f ""%s"" prog;
                close_out f;
                Sys.command (""clang -lm -Wno-everything "" ^ llvm_file_name ^ "" -o "" ^ test_binary ^ "" && "" ^ test_binary)".

(** Write our LLVM program to a file ("temporary_vellvm.ll"), and then
    use the vellvm binary in the path to interpret this file in order
    to get the return code. *)
Axiom vellvm_binary_command_ocaml : string -> oint.
Extract Constant vellvm_binary_command_ocaml =>
          "fun prog ->
              let vellvm_bin = (try Sys.getenv ""VELLVM_BIN""
                                with Not_found -> ""../vellvm/src/_build/default/ml/main.exe"") in
              let llvm_file_name = Filename.(concat (get_temp_dir_name ()) ""temporary_vellvm.ll"") in
              let f = open_out llvm_file_name in
                Printf.fprintf f ""%s"" prog;
                close_out f;
                Sys.command (vellvm_bin ^ "" -interpret "" ^ llvm_file_name ^ "" | grep terminated | awk '{ exit $NF }'"")".

Definition llc_command (prog : string) : Z
  := oint_to_Z (llc_command_ocaml prog).

Definition vellvm_binary_command (prog : string) : Z
  := oint_to_Z (vellvm_binary_command_ocaml prog).

(** Use the *llc_command* Axiom to run a Vellvm program with clang. *)
Definition run_llc (prog : llprog) : Z
  := llc_command (to_caml_str (show prog)).

(** Use the *vellvm_binary_command* Axiom to run a Vellvm program with
    the vellvm interpreter in the user's path. *)
Definition run_vellvm_binary (prog : llprog) : Z
  := vellvm_binary_command (to_caml_str (show prog)).

(** This version runs the vellvm binary in your path instead...  This
    will be slower (has to read and parse a file), and will not
    guarantee you're running the tests with same version of vellvm, but
    this can be helpful for testing the parser (note the more direct
    vellvm_agrees_with_clang is also helpful in that it bypasses the
    parser for vellvm, but clang parses the file so it can detect bugs
    in the pretty printer for LLVM ASTs), and this can also be helpful
    for skirting around extraction bugs which are easier to patch up
    outside of QC. *)
Definition vellvm_binary_agrees_with_clang (p : string + PROG) : Checker :=
  match p with
  | inl msg => checker false
  | inr (Prog prog) =>
    let clang_res := run_llc prog in
    let vellvm_res := run_vellvm_binary prog in
    if (Z.eqb clang_res vellvm_res)
    then checker true
    else whenFail ("Vellvm: " ++ show vellvm_res ++ " | Clang: " ++ show clang_res ++ " | Ast: " ++ ReprAST.repr prog) false
  end.

(* In-process testing *)

#[local] Instance ParamsQC : Params := @ParamsV IPZ IPZTheory.

Inductive MlResult (a e: Type) :=
| MlOk : a -> MlResult a e
| MlError : e -> MlResult a e.

Extract Inductive MlResult => "result" [ "Ok" "Error" ].

#[global] Instance MlResultShow {a e} `{Show a} `{Show e} : Show (MlResult a e).
Proof.
  split.
  exact
    (fun res =>
       match res with
       | MlOk a => ("Ok " ++ show a)%string
       | MlError e => ("Error " ++ show e)%string
       end).
Defined.

#[global] Instance showdv : Show dvalue.
Proof.
  split.
  apply show_dvalue.
Defined.

Local Notation dvalue := DynamicValues.dvalue.
Local Notation itr := (itree MCFGEbot (Res dvalue)).

Unset Guard Checking.
CoFixpoint step (t : itr) : MlResult dvalue string
  := match observe t with
     | RetF (_, x) => MlOk _ string x
     | TauF t => step t
     | VisF _ (inl1 e) k =>
         MlError _ string "Uninterpreted external call"
     | VisF _ (inr1 (inl1 (ThrowOOM msg))) k =>
         MlError _ string ("OOM")%string
     | VisF _ (inr1 (inr1 (inl1 (LLVMExc _)))) k =>
         MlError _ string ("LLVMException")%string
     | VisF _ (inr1 (inr1 (inr1 (inl1 (ThrowUB _))))) k =>
         MlError _ string ("UB")%string
     | VisF _ (inr1 (inr1 (inr1 (inr1 (inl1 (Debug _)))))) k =>
         MlError _ string ("Debug")%string
     | VisF _ (inr1 (inr1 (inr1 (inr1 (inr1 (LLVMEvents.Throw _)))))) k =>
         MlError _ string ("Failure")%string
     end.
Set Guard Checking.

(** Top level interpreter to run LLVM programs. Yields either a uvalue, or an error string. *)
Definition interpret (prog : llprog) : MlResult dvalue string
  := step (TopLevel.interpreter nil prog).

(** Basic property to make sure that Vellvm and Clang agree when they
    both produce values *)
Definition vellvm_agrees_with_clang (p : string + PROG) : Checker :=
  match p with
  | inl msg => checker false
  | inr (Prog prog) =>
    let clang_res := run_llc prog in
    let vellvm_res := interpret prog in
    match vellvm_res with
    | MlOk (DVALUE_Base (DVALUE_I sz x)) =>
      if ((Pos.eqb sz 8%positive && Z.eqb (Integers.unsigned x) clang_res)%bool)
      then checker true
      else whenFail ("Vellvm: " ++ show (Integers.unsigned x)
                      ++ " | Clang: " ++ show clang_res
                      ++ " | Ast: " ++ ReprAST.repr prog) false
    | _ => whenFail ("Something else went wrong... Vellvm: " ++ show vellvm_res
                      ++ " | Clang: " ++ show clang_res
                      ++ " | Ast: " ++ ReprAST.repr prog) false
    end
  end.

(** Processes *)
Inductive process_status : Type :=
| WEXITED   : oint -> process_status
| WSIGNALED : oint -> process_status
| WSTOPPED  : oint -> process_status
.
Extract Inductive process_status => "Unix.process_status" [ "Unix.WEXITED" "Unix.WSIGNALED" "Unix.WSTOPPED" ].

#[global] Instance Show_process_status : Show process_status.
Proof.
  split.
  intros STATUS. destruct STATUS as [EXIT | SIGNAL | STOPPED].
  - exact ("Exited with " ++ show (oint_to_Z EXIT))%string.
  - exact ("Signaled with " ++ show (oint_to_Z SIGNAL))%string.
  - exact ("Stopped with " ++ show (oint_to_Z STOPPED))%string.
Qed.

Axiom fork : unit -> oint.
Extract Inlined Constant fork => "Unix.fork".

Axiom wait : unit -> (oint * process_status)%type.
Extract Inlined Constant wait => "Unix.wait".

Axiom wait_flag : Type.
Extract Inlined Constant wait_flag => "Unix.wait_flag".

Axiom waitpid : list wait_flag -> oint -> (oint * process_status)%type.
Extract Inlined Constant waitpid => "Unix.waitpid".

Axiom exit : forall {A}, oint -> A.
Extract Inlined Constant exit => "exit".

(** Basic property to make sure that Vellvm and Clang agree when they
    both produce values *)
Definition vellvm_agrees_with_clang_parallel (p : string + PROG) : Checker :=
  match p with
  | inl msg => checker false
  | inr (Prog prog) =>
    let pid := fork tt in
    if oeq pid ozero
    then (* Child *)
      exit (llc_command_ocaml (to_caml_str (show prog)))
    else (* Parent *)
      let vellvm_res := interpret prog in
      let clang_res := snd (waitpid nil pid) in
      match vellvm_res, clang_res with
      | MlOk (DVALUE_Base (DVALUE_I sz x)), (WEXITED ocaml_y) =>
          let y := Integers.repr (oint_to_Z ocaml_y) in
          if Integers.eq x y
          then checker true
          else whenFail ("Vellvm: " ++ show (Integers.unsigned x) ++ " | Clang: " ++ show (Integers.unsigned y) ++ " | Ast: " ++ ReprAST.repr prog) false
      | _, (WSIGNALED ocaml_y) =>
          whenFail ("clang process signaled") false
      | _, (WSTOPPED ocaml_y) =>
          whenFail ("clang process stopped") false
      | _, _ =>
          whenFail ("Something else went wrong... Vellvm: " ++ show vellvm_res ++ " | Clang: " ++ show clang_res) false
      end
  end.

(* Definition agrees := (forAll (run_GenLLVM gen_llvm) vellvm_agrees_with_clang). *)

Extract Constant defNumTests    => "1000".

QuickChick (forAll (run_GenLLVM gen_PROG) vellvm_binary_agrees_with_clang).
(* QuickChick (forAll (run_GenLLVM gen_PROG) vellvm_agrees_with_clang). *)
(* QuickChick (forAll (run_GenLLVM gen_PROG) vellvm_agrees_with_clang_parallel). *)