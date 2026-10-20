let text chars = String.of_seq (List.to_seq chars)

let () =
  let failed = ref 0 in
  List.iter
    (fun (label, check) ->
      let label = text label in
      Printf.eprintf "NI_BEGIN %s\n%!" label;
      let passed = check () in
      Printf.eprintf "NI_END %s\n%!" label;
      Printf.printf "%s %s\n%!" (if passed then "PASS" else "FAIL") label;
      if not passed then incr failed)
    Memory_extracted.checks;
  if !failed <> 0 then exit 1
