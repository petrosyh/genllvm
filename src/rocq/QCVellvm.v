 (** Framework for running QC vellvm tests. *)

From QuickChick Require Import QuickChick.
From Stdlib Require Import
  String
  ZArith
  List.
From Vellvm Require Import
  LLVMAst
  Syntax.ShowAST
  Syntax.ReprAST.
From GenLLVM Require Import
  GenAST
  QCExtractionFix.

Import ListNotations.
Local Open Scope string_scope.

Extraction Blacklist String List Char Core Z Format int.

(* Useful names *)
Definition lprog := list (toplevel_entity typ (block typ * list (block typ))).

#[global] Instance show_lprog : Show lprog :=
  {| show := showProg |}.

(* Hide show instance... *)
Inductive PROG :=
| Prog : lprog -> PROG
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
Definition run_llc (prog : lprog) : Z
  := llc_command (to_caml_str (show prog)).

(** Use the *vellvm_binary_command* Axiom to run a Vellvm program with
    the vellvm interpreter in the user's path. *)
Definition run_vellvm_binary (prog : lprog) : Z
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
Definition vellvm_binary_agrees_with_clang (p : string + PROG) : Checker.
  refine
    (match p with
     | inl msg => checker false
     | inr p =>
         (* collect (show prog) *)
         let '(Prog prog) := p in
         let clang_res := run_llc prog in
         let vellvm_res := run_vellvm_binary prog in
         if (Z.eqb clang_res vellvm_res)
         then checker true
         else whenFail ("Vellvm: " ++ show vellvm_res ++ " | Clang: " ++ show clang_res ++ " | Ast: " ++ ReprAST.repr prog) false
     end).
Defined.

(* Definition agrees := (forAll (run_GenLLVM gen_llvm) vellvm_agrees_with_clang). *)

Extract Constant defNumTests    => "1000".

QuickChick (forAll (run_GenLLVM gen_PROG) vellvm_binary_agrees_with_clang).
(*! QuickChick agrees. *)
