open Memory_extracted

let methods =
  [| ("stock", benchmark_stock); ("disabled", benchmark_disabled);
     ("discard", benchmark_discard); ("observed", benchmark_observed) |]

let validate memory count name = function
  | Normal (trace, (_, value)) ->
      let expected = if memory && name = "observed" then count + 1 else 0 in
      if List.length trace <> expected ||
         not (same_value value (word32 (Big_int_Z.big_int_of_int 7)))
      then failwith ("Unexpected result from " ^ name)
  | _ -> failwith ("Workload did not finish in " ^ name)

let () =
  let count = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 2000 in
  let repeats = if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else 5 in
  if count < 1 || count > 1_000_000 || repeats < 1 then invalid_arg "benchmark arguments";
  let fuel = 100 * count + 1000 in
  Printf.printf "workload,method,trial,count,seconds,cpu_seconds,allocated_bytes,minor_gc,major_gc,trace_length\n%!";
  List.iter (fun memory ->
    Array.iter (fun (name, f) -> validate memory count name (f memory count fuel)) methods;
    for trial = 0 to repeats - 1 do
      for offset = 0 to Array.length methods - 1 do
        let name, f = methods.((trial + offset) mod Array.length methods) in
        Gc.full_major ();
        let gc0 = Gc.quick_stat () in
        let allocated0 = Gc.allocated_bytes () in
        let cpu0 = Sys.time () in
        let start = Unix.gettimeofday () in
        let result = f memory count fuel in
        let seconds = Unix.gettimeofday () -. start in
        let cpu_seconds = Sys.time () -. cpu0 in
        let allocated = Gc.allocated_bytes () -. allocated0 in
        let gc1 = Gc.quick_stat () in
        validate memory count name result;
        let trace_length = match result with Normal (trace, _) -> List.length trace | _ -> assert false in
        Printf.printf "%s,%s,%d,%d,%.9f,%.9f,%.0f,%d,%d,%d\n%!"
          (if memory then "memory" else "locals") name trial count seconds cpu_seconds allocated
          (gc1.Gc.minor_collections - gc0.Gc.minor_collections)
          (gc1.Gc.major_collections - gc0.Gc.major_collections)
          trace_length
      done
    done) [true; false]
