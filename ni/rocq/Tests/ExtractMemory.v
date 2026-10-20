From GenLLVMNI.Tests Require Import MemoryFixtures MemoryBenchmark.
From GenLLVM Require Import QCExtractionFix.
From Vellvm Require Import LLVMEvents AstLib.
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlString ExtrOcamlZBigInt.

Set Extraction AccessOpaque.
Extraction Language OCaml.
Extraction Blacklist String List Nat Z Char Core Format.

(* Keep stock diagnostics separate from program IO_stdout/IO_stderr events.
   The test driver labels each execution and captures this stream. *)
Extract Constant printer_object => "
  let location = ref None in
  let text chars = String.of_seq (List.to_seq chars) in
  { printer_set_loc = (fun fi -> location := fi; []);
    printer_print_msg = (fun msg ->
      Printf.eprintf ""NI_DIAGNOSTIC %s: %s\n%!""
        (text (location_string !location)) (text msg));
    printer_get_loc = (fun () -> location_string !location) }
".

(* These proof-only real-number conversions are not used by the executable
   integer/pointer fixtures. Match the stock extraction's unreachable guards. *)
Extract Inlined Constant Flocq.Core.Defs.F2R => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.IEEE754.Binary.FF2R => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.IEEE754.Binary.B2R => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.IEEE754.BinarySingleNaN.round_mode => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.Calc.Bracket.inbetween_loc => "(fun _ -> assert false)".
Extract Inlined Constant Reals.ClassicalDedekindReals.sig_forall_dec => "(fun _ -> assert false)".
Extract Inlined Constant Reals.ClassicalDedekindReals.sig_not_dec => "false".
Extract Inlined Constant Archi.ppc64 => "false".

Extraction "memory_extracted.ml" location_string checks
  benchmark_stock benchmark_disabled benchmark_discard benchmark_observed.
