(* From src/rocq/Syntax/TypeUtil.v of commit f1ec3588 *)

From Stdlib Require Import
     List
     String.

From Vellvm Require Import
     Syntax.LLVMAst
     Syntax.AstLib
     Syntax.TypToDtyp
     ListUtil.

Require Import Rocqlib.

Import ListNotations.
Open Scope list_scope.

Program Fixpoint normalize_type (env : list (ident * typ)) (t : typ) {measure (List.length env, t) (lex_ord lt typ_order)} : typ :=
  match t with
  | TYPE_Array sz t =>
    let nt := normalize_type env t in
    TYPE_Array sz nt

  | TYPE_Function ret args varargs =>
    let nret := (normalize_type env ret) in
    let nargs := map_In args (fun t _ => normalize_type env t) in
    TYPE_Function nret nargs varargs

  | TYPE_Struct fields =>
    let nfields := map_In fields (fun t _ => normalize_type env t) in
    TYPE_Struct nfields

  | TYPE_Packed_struct fields =>
    let nfields := map_In fields (fun t _ => normalize_type env t) in
    TYPE_Packed_struct nfields

  | TYPE_Vector sz t =>
    let nt := normalize_type env t in
    TYPE_Vector sz nt

  | TYPE_Identified id =>
    match find (fun a => Ident.eq_dec id (fst a)) env with
    | None => TYPE_Identified id
    | Some (_, t) => normalize_type (remove_key Ident.eq_dec id env) t
    end

  | TYPE_I sz => t
  | TYPE_Iptr => t
  | TYPE_Pointer t' => t
  | TYPE_Void => t
  | TYPE_FP fp => t
  | TYPE_Label => t
  | TYPE_Token => t
  | TYPE_Metadata => t
  | TYPE_X86_mmx => t
  | TYPE_Opaque => t
  end.
Next Obligation.
  left.
  symmetry in Heq_anonymous. apply find_some in Heq_anonymous. destruct Heq_anonymous as [Hin Heqb_ident].
  simpl in Heqb_ident.
  destruct (Ident.eq_dec id wildcard'). subst. eapply remove_key_in. apply Hin.
  inversion Heqb_ident.
Defined.
