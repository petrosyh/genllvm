From QuickChick Require Import QuickChick.
From Stdlib Require Import String Number Decimal.

(* Original codes from QuickChick's ExtractionQC.v.cppo

Extract Inductive Hexadecimal.int => "((Obj.t -> Obj.t) -> (Obj.t -> Obj.t) -> Obj.t) (* Hexadecimal.int *)"
  [ "(fun x pos _ -> pos (Obj.magic x))"
    "(fun y _ neg -> neg (Obj.magic y))"
  ] "(fun i pos neg -> Obj.magic i pos neg)".
Extract Inductive Number.int => "((Obj.t -> Obj.t) -> (Obj.t -> Obj.t) -> Obj.t) (* Number.int *)"
  [ "(fun x dec _ -> dec (Obj.magic x))"
    "(fun y _ hex -> hex (Obj.magic y))"
  ] "(fun i dec hex -> Obj.magic i dec hex)".
*)

Extract Inductive Hexadecimal.int => "((Obj.t -> Obj.t) -> (Obj.t -> Obj.t) -> Obj.t) (* Hexadecimal.int *)"
  [ "(fun x pos _ -> pos (Obj.magic x))"
    "(fun y _ neg -> neg (Obj.magic y))"
  ] "(fun pos neg i -> Obj.magic i pos neg)".
Extract Inductive Number.int => "((Obj.t -> Obj.t) -> (Obj.t -> Obj.t) -> Obj.t) (* Number.int *)"
  [ "(fun x dec _ -> dec (Obj.magic x))"
    "(fun y _ hex -> hex (Obj.magic y))"
  ] "(fun dec hex i -> Obj.magic i dec hex)".

