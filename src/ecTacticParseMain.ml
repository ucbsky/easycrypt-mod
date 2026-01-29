(* -------------------------------------------------------------------- *)

let read_all_stdin () =
  let buf = Buffer.create 1024 in
  let tmp = Bytes.create 4096 in
  let rec loop () =
    match input stdin tmp 0 (Bytes.length tmp) with
    | 0 -> ()
    | n ->
        Buffer.add_subbytes buf tmp 0 n;
        loop ()
  in
  loop ();
  Buffer.contents buf

let tactic_input () =
  let argv = Array.to_list Sys.argv |> List.tl in
  match argv with
  | [] ->
      read_all_stdin ()
  | _ ->
      String.concat " " argv

let () =
  let input = String.trim (tactic_input ()) in
  if input = "" then (
    prerr_endline "usage: easycrypt-tactic-names \"<tactic>\"";
    prerr_endline "or:    echo \"<tactic>\" | easycrypt-tactic-names";
    exit 2
  );

  let names =
    try EcLib.EcTacticParse.tactic_names input with
    | EcLib.EcParser.Error ->
        prerr_endline "parse error: invalid tactic";
        exit 1
  in
  List.iter print_endline names
