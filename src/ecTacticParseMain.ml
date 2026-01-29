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

  let split_sentences s =
    let buf = Buffer.create (String.length s) in
    let sentences = ref [] in
    let flush () =
      let chunk = String.trim (Buffer.contents buf) in
      Buffer.clear buf;
      if chunk <> "" then sentences := chunk :: !sentences
    in
    let len = String.length s in
    let is_blank = function
      | ' ' | '\t' | '\r' | '\n' -> true
      | _ -> false
    in
    let rec loop i =
      if i >= len then ()
      else
        let c = s.[i] in
        if c = '.' then
          let next_is_blank = i + 1 >= len || is_blank s.[i + 1] in
          if next_is_blank then (
            flush ();
            loop (i + 1)
          ) else (
            Buffer.add_char buf c;
            loop (i + 1)
          )
        else (
          Buffer.add_char buf c;
          loop (i + 1)
        )
    in
    loop 0;
    flush ();
    List.rev !sentences
  in

  let try_parse_one s =
    try Some (EcLib.EcTacticParse.tactic_names s) with
    | EcLib.EcParser.Error
    | EcLib.EcParsetree.ParseError _ -> None
  in

  let names =
    match try_parse_one input with
    | Some names -> names
    | None ->
        let rec collect acc = function
          | [] -> acc
          | s :: tl ->
              match try_parse_one s with
              | Some names -> collect (List.rev_append names acc) tl
              | None ->
                  prerr_endline ("parse error: skipping sentence: " ^ s);
                  collect acc tl
        in
        collect [] (split_sentences input)
  in
  List.iter print_endline names
