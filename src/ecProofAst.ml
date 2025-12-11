let timed_global_indices : (EcCoreGoal.handle, string) Hashtbl.t = Hashtbl.create 97
open EcUtils
open EcLocation
open EcParsetree
open EcCoreGoal

module Sint = EcMaps.Sint

module Path = BatPathGen.OfString

type completion = [ `Qed | `Admitted | `Aborted ]
type lemma_status = [ `Pending | completion ]

type block = {
  index   : int;
  loc     : EcLocation.t option;
  tactics : ptactic list;
}

type lemma_entry = {
  lemma  : EcDecl.axiom;
  mutable name   : string option;
  mutable path   : string;
  mutable blocks : block list;
  mutable status : lemma_status;
}

type clone_entry = {
  clone_data        : theory_cloning;
  clone_base_path   : string;
  clone_target_path : string;
}

let enabled        = ref false
let current_source = ref None
let working_dir    = ref None
let source_path    = ref None
let lemmas : (EcDecl.axiom, lemma_entry) Hashtbl.t = Hashtbl.create 17
let lemma_order : EcDecl.axiom list ref = ref []
let clones : clone_entry list ref = ref []
let file_cache : (string, string) Hashtbl.t = Hashtbl.create 3

module PtacticTbl = Hashtbl.Make(struct
  type t = ptactic
  let equal = (==)
  let hash = Hashtbl.hash
end)

module IntroTbl = Hashtbl.Make(struct
  type t = ptactic * int
  let equal (t1, i1) (t2, i2) = t1 == t2 && i1 = i2
  let hash = Hashtbl.hash
end)

type intro_token =
  [ `Core of ipcore located list
  | `Dup
  | `Done of [`Default | `Variant] option
  | `Smt of (bool * pprover_infos)
  | `Clear of psymbol list
  | `Case of icasemode * intropattern list
  | `Rw of (rwocc * rwside * (int option) option)
  | `Delta of ((rwside * rwocc) * pformula)
  | `View of ppterm
  | `Subst of (rwside * (int option) option)
  | `SubstTop of (int option * [`LtoR | `RtoL] option)
  | `Simpl of [`Default | `Variant]
  | `Crush of crushmode
  ]

type intro_element =
  | IEPattern of intro_token located
  | IEGen of prevert
  | IEBridge

module IntroElemTbl = Hashtbl.Make(struct
  type t = ptactic * int
  let equal (t1, i1) (t2, i2) = t1 == t2 && i1 = i2
  let hash = Hashtbl.hash
end)

module RewriteTbl = Hashtbl.Make(struct
  type t = ptactic * int
  let equal (t1, i1) (t2, i2) = t1 == t2 && i1 = i2
  let hash = Hashtbl.hash
end)

type tactic_application = {
  ta_local_in   : int list;
  ta_local_out  : int list;
  ta_global_in  : int list;
  ta_global_out : int list;
}

type intro_element_event = {
  ie_element : intro_element;
  ie_app     : tactic_application;
}

type rewrite_event = {
  re_app   : tactic_application;
  re_chosen: string option;
  re_paths : string list;
}

let goal_indices : (handle, int) Hashtbl.t = Hashtbl.create 97
let global_indices : (handle, int) Hashtbl.t = Hashtbl.create 97
let goal_index_freelist : int list ref = ref []
let next_goal_index = ref 0
let next_global_index = ref 0
let tactic_events : tactic_application list PtacticTbl.t = PtacticTbl.create 97
let intro_events : tactic_application list IntroTbl.t = IntroTbl.create 97
let intro_elem_events : intro_element_event list IntroElemTbl.t = IntroElemTbl.create 97
let rewrite_events : rewrite_event list RewriteTbl.t = RewriteTbl.create 97
let trace_active = ref false
let trace_buffer : ptactic list ref = ref []
let intro_trace_buffer : (ptactic * int) list ref = ref []
let intro_elem_trace_buffer : (ptactic * int) list ref = ref []
let rewrite_trace_buffer : (ptactic * int) list ref = ref []

let active_goals : handle list ref = ref []
let current_lemma : EcDecl.axiom option ref = ref None
let include_intros = ref true
let include_emacs_goals = ref true
let include_serialized_goals = ref true

let set_include_intros v = include_intros := v
let set_include_emacs_goals v = include_emacs_goals := v
let set_include_serialized_goals v = include_serialized_goals := v

let rec insert_free_index idx = function
  | [] -> [idx]
  | hd :: tl as lst ->
      if idx <= hd then idx :: lst else hd :: insert_free_index idx tl

let clear_clones () =
  clones := []

let clear_goal_traces () =
  Hashtbl.clear goal_indices;
  Hashtbl.clear global_indices;
  PtacticTbl.clear tactic_events;
  IntroTbl.clear intro_events;
  IntroElemTbl.clear intro_elem_events;
  RewriteTbl.clear rewrite_events;
  goal_index_freelist := [];
  next_goal_index := 0;
  next_global_index := 0;
  trace_active := false;
  trace_buffer := [];
  intro_trace_buffer := [];
  intro_elem_trace_buffer := [];
  rewrite_trace_buffer := [];
  active_goals := [];
  current_lemma := None

let reset_goal_indices () =
  Hashtbl.clear goal_indices;
  Hashtbl.clear global_indices;
  goal_index_freelist := [];
  next_goal_index := 0;
  next_global_index := 0;
  active_goals := []

let allocate_goal_index () =
  match !goal_index_freelist with
  | idx :: rest ->
      goal_index_freelist := rest;
      idx
  | [] ->
      let idx = !next_goal_index in
      incr next_goal_index;
      idx

let goal_index_of_handle hd =
  match Hashtbl.find_opt goal_indices hd with
  | Some idx -> idx
  | None ->
      let idx = allocate_goal_index () in
      Hashtbl.add goal_indices hd idx;
      idx

let global_index_of_handle hd =
  match Hashtbl.find_opt global_indices hd with
  | Some idx -> idx
  | None ->
      let idx = !next_global_index in
      incr next_global_index;
      Hashtbl.add global_indices hd idx;
      idx

let remove_goal_handle hd =
  match Hashtbl.find_opt goal_indices hd with
  | None -> ()
  | Some idx ->
      Hashtbl.remove goal_indices hd;
      goal_index_freelist := insert_free_index idx !goal_index_freelist

let remove_global_handle hd =
  Hashtbl.remove global_indices hd

let update_active_goals handles =
  let rec assign idx = function
    | [] -> ()
    | hd :: tl ->
        Hashtbl.replace goal_indices hd idx;
        assign (idx + 1) tl
  in
  let inactive =
    List.filter (fun hd -> not (List.exists ((=) hd) handles)) !active_goals
  in
  List.iter remove_goal_handle inactive;
  assign 0 handles;
  active_goals := handles

let log_trace_entry tac entry =
  let current =
    match PtacticTbl.find_opt tactic_events tac with
    | None -> []
    | Some events -> events
  in
  PtacticTbl.replace tactic_events tac (entry :: current);
  trace_buffer := tac :: !trace_buffer

let begin_tactic_trace () =
  if !enabled then begin
    trace_active := true;
    trace_buffer := [];
    intro_trace_buffer := [];
    intro_elem_trace_buffer := [];
    rewrite_trace_buffer := []
  end

let rollback_trace () =
  List.iter
    (fun tac ->
       match PtacticTbl.find_opt tactic_events tac with
       | None -> ()
       | Some (_ :: rest) ->
           if rest = [] then PtacticTbl.remove tactic_events tac
           else PtacticTbl.replace tactic_events tac rest
       | Some [] ->
           PtacticTbl.remove tactic_events tac)
    !trace_buffer;
  trace_buffer := [];
  List.iter
    (fun key ->
       match IntroTbl.find_opt intro_events key with
       | None -> ()
       | Some (_ :: rest) ->
           if rest = [] then IntroTbl.remove intro_events key
           else IntroTbl.replace intro_events key rest
       | Some [] ->
           IntroTbl.remove intro_events key)
    !intro_trace_buffer;
  intro_trace_buffer := [];
  List.iter
    (fun key ->
       match IntroElemTbl.find_opt intro_elem_events key with
       | None -> ()
       | Some (_ :: rest) ->
           if rest = [] then IntroElemTbl.remove intro_elem_events key
           else IntroElemTbl.replace intro_elem_events key rest
       | Some [] ->
           IntroElemTbl.remove intro_elem_events key)
    !intro_elem_trace_buffer;
  intro_elem_trace_buffer := [];
  List.iter
    (fun key ->
       match RewriteTbl.find_opt rewrite_events key with
       | None -> ()
       | Some (_ :: rest) ->
           if rest = [] then RewriteTbl.remove rewrite_events key
           else RewriteTbl.replace rewrite_events key rest
       | Some [] ->
           RewriteTbl.remove rewrite_events key)
    !rewrite_trace_buffer;
  rewrite_trace_buffer := []

let end_tactic_trace ~success =
  if !enabled then begin
    if success then trace_buffer := [] else rollback_trace ();
    trace_active := false
  end

let mk_tactic_application goals goals_out =
  let local_in = List.map goal_index_of_handle goals in
  let global_in = List.map global_index_of_handle goals in
  let local_out = List.map goal_index_of_handle goals_out in
  let global_out = List.map global_index_of_handle goals_out in
  {
    ta_local_in   = local_in;
    ta_local_out  = local_out;
    ta_global_in  = global_in;
    ta_global_out = global_out;
  }

let index_counts indices =
  let tbl = Hashtbl.create 13 in
  List.iter
    (fun idx ->
       let count = match Hashtbl.find_opt tbl idx with Some v -> v | None -> 0 in
       Hashtbl.replace tbl idx (count + 1))
    indices;
  tbl

let shared_index_counts indices_in indices_out =
  let ins = index_counts indices_in in
  let outs = index_counts indices_out in
  let shared = Hashtbl.create (Hashtbl.length ins) in
  Hashtbl.iter
    (fun idx count_in ->
       match Hashtbl.find_opt outs idx with
       | Some count_out ->
           Hashtbl.replace shared idx (min count_in count_out)
       | None -> ())
    ins;
  shared

let consume_shared_idx tbl idx =
  match Hashtbl.find_opt tbl idx with
  | Some 1 -> Hashtbl.remove tbl idx; true
  | Some n when n > 1 ->
      Hashtbl.replace tbl idx (n - 1); true
  | _ -> false

let filter_pairs shared pairs =
  let tbl = Hashtbl.copy shared in
  let rec aux acc = function
    | [] -> List.rev acc
    | (local, global) :: rest ->
        if consume_shared_idx tbl global then aux acc rest
        else aux ((local, global) :: acc) rest
  in
  aux [] pairs

let unzip_pairs pairs =
  List.fold_right (fun (l, g) (ls, gs) -> (l :: ls, g :: gs)) pairs ([], [])

let zip_pairs left right =
  let rec aux acc l r =
    match l, r with
    | x :: xs, y :: ys -> aux ((x, y) :: acc) xs ys
    | _ -> List.rev acc
  in
  aux [] left right

let trim_application app =
  let shared = shared_index_counts app.ta_global_in app.ta_global_out in
  if Hashtbl.length shared = 0 then app
  else
    let in_pairs  = filter_pairs shared (zip_pairs app.ta_local_in  app.ta_global_in) in
    let out_pairs = filter_pairs shared (zip_pairs app.ta_local_out app.ta_global_out) in
    let local_in,  global_in  = unzip_pairs in_pairs in
    let local_out, global_out = unzip_pairs out_pairs in
    { ta_local_in  = local_in;
      ta_local_out = local_out;
      ta_global_in = global_in;
      ta_global_out = global_out; }

let log_tactic_application tac goals goals_out =
  if !enabled && !trace_active then
    log_trace_entry tac (mk_tactic_application goals goals_out)

let log_intro_application tac index goals goals_out =
  if !enabled && !trace_active then begin
    let entry = mk_tactic_application goals goals_out in
    let key = (tac, index) in
    let current =
      match IntroTbl.find_opt intro_events key with
      | None -> []
      | Some events -> events
    in
    IntroTbl.replace intro_events key (entry :: current);
    intro_trace_buffer := key :: !intro_trace_buffer
  end

let log_intro_element tac index element goals goals_out =
  if !enabled && !trace_active then begin
    let entry = mk_tactic_application goals goals_out in
    let key = (tac, index) in
    let current =
      match IntroElemTbl.find_opt intro_elem_events key with
      | None -> []
      | Some events -> events
    in
    let event = { ie_element = element; ie_app = entry } in
    IntroElemTbl.replace intro_elem_events key (event :: current);
    intro_elem_trace_buffer := key :: !intro_elem_trace_buffer
  end


let log_rewrite_application tac index chosen paths goals goals_out =
  if !enabled && !trace_active then begin
    let entry = mk_tactic_application goals goals_out |> trim_application in
    let key = (tac, index) in
    let current =
      match RewriteTbl.find_opt rewrite_events key with
      | None -> []
      | Some events -> events
    in
    let event = { re_app = entry; re_chosen = chosen; re_paths = paths } in
    RewriteTbl.replace rewrite_events key (event :: current);
    rewrite_trace_buffer := key :: !rewrite_trace_buffer
  end

let consume_tactic_applications tac =
  match PtacticTbl.find_opt tactic_events tac with
  | None -> []
  | Some apps ->
      PtacticTbl.remove tactic_events tac;
      List.rev apps

let consume_intro_applications tac index =
  match IntroTbl.find_opt intro_events (tac, index) with
  | None -> []
  | Some apps ->
      IntroTbl.remove intro_events (tac, index);
      List.rev apps

let consume_intro_elements tac index =
  match IntroElemTbl.find_opt intro_elem_events (tac, index) with
  | None -> []
  | Some events ->
      IntroElemTbl.remove intro_elem_events (tac, index);
      List.rev events

let consume_rewrite_applications tac index =
  match RewriteTbl.find_opt rewrite_events (tac, index) with
  | None -> []
  | Some apps ->
      RewriteTbl.remove rewrite_events (tac, index);
      List.rev apps

let proofast_filename source =
  Filename.remove_extension source ^ ".proofast.json"

let canonicalize ~root path =
  let full =
    if Filename.is_relative path then Filename.concat root path else path in
  try Path.s (Path.normalize_in_tree (Path.p full))
  with Path.Malformed_path -> full

let canonicalize_input path =
  let root = odfl (Sys.getcwd ()) !working_dir in
  canonicalize ~root path

let enable ~source =
  enabled        := true;
  working_dir    := Some (Sys.getcwd ());
  source_path    := Some (canonicalize_input source);
  current_source := Some source;
  Hashtbl.clear lemmas;
  lemma_order := [];
  clear_clones ();
  Hashtbl.clear file_cache;
  include_intros := true;
  include_emacs_goals := true;
  include_serialized_goals := true;
  clear_goal_traces ()

let reset_run () =
  if !enabled then begin
    Hashtbl.clear lemmas;
    lemma_order := [];
    clear_clones ();
    Hashtbl.clear file_cache;
    clear_goal_traces ()
  end

let is_enabled () = !enabled

let matches_target_file file =
  match !source_path with
  | None -> false
  | Some target ->
      let canon = canonicalize_input file in
      String.equal target canon

let load_file path =
  match Hashtbl.find_opt file_cache path with
  | Some data -> data
  | None ->
      let data =
        try
          let ic = open_in_bin path in
          let len = in_channel_length ic in
          let buf = really_input_string ic len in
          close_in ic; buf
        with Sys_error _ -> ""
      in
      Hashtbl.add file_cache path data; data

let snippet_of_loc loc =
  match !source_path with
  | None -> None
  | Some target ->
      if EcLocation.isdummy loc then None
      else if not (matches_target_file loc.loc_fname) then None
      else
        let text = load_file target in
        let len = String.length text in
        let b = max 0 (min len loc.loc_bchar) in
        let e = max b (min len loc.loc_echar) in
        Some (String.sub text b (e - b))

let json_of_source loc =
  match snippet_of_loc loc with
  | None   -> `Null
  | Some s -> `String s

(* -------------------------------------------------------------------- *)
let json_of_option f = function
  | None   -> `Null
  | Some v -> f v

let json_of_list f xs =
  `List (List.map f xs)

let json_of_pair f (x, y) =
  `List [f x; f y]

let json_of_int_option = function
  | None   -> `Null
  | Some i -> `Int i

let json_of_string_option = function
  | None   -> `Null
  | Some s -> `String s

let fields_of_loc loc =
  [("source", json_of_source loc)]

let json_of_located ?(extra=[]) x =
  `Assoc (fields_of_loc x.pl_loc @ extra)

let json_of_goal_index = function
  | None -> `Null
  | Some idx -> `Int idx

let sort_indices indices =
  List.sort compare indices

let identical_indices left right =
  sort_indices left = sort_indices right

let filter_goal_trace label apps =
  match label with
  | `Emacs -> apps
  | `Serialized ->
      List.filter
        (fun app ->
           not (identical_indices app.ta_global_in app.ta_global_out))
        apps

let json_of_goal_trace label apps =
  let filtered = filter_goal_trace label apps in
  match filtered with
  | [] -> None
  | _  ->
      let entries =
        List.map
          (fun app ->
             let (incoming, outgoing) =
               match label with
               | `Emacs ->
                   (app.ta_local_in, app.ta_local_out)
               | `Serialized ->
                   (app.ta_global_in, app.ta_global_out)
             in
             `Assoc [
               ("in" , `List (List.map (fun idx -> `Int idx) incoming));
               ("out", `List (List.map (fun idx -> `Int idx) outgoing));
             ])
          filtered
      in
      let entry =
        match label with
        | `Emacs      -> ("emacs_goals", `List entries)
        | `Serialized -> ("serialized_goals", `List entries)
      in
      Some entry

let json_fields_of_application app =
  let entry incoming outgoing =
    `Assoc [
      ("in" , `List (List.map (fun idx -> `Int idx) incoming));
      ("out", `List (List.map (fun idx -> `Int idx) outgoing));
    ]
  in
  let fields = [] in
  let fields =
    let emacs = entry app.ta_local_in app.ta_local_out in
    ("emacs_goals", `List [emacs]) :: fields
  in
  let fields =
    if identical_indices app.ta_global_in app.ta_global_out then fields
    else
      let serialized = entry app.ta_global_in app.ta_global_out in
      ("serialized_goals", `List [serialized]) :: fields
  in
  List.rev fields

let mk_json kind fields =
  `Assoc (("kind", `String kind) :: fields)

let json_of_symbol s = `String s
let json_of_pqsymbol qs = `String (EcSymbols.string_of_qsymbol (unloc qs))
let json_of_pqsymbol_list = json_of_list json_of_pqsymbol

let json_of_tuple2 f1 f2 (x1, x2) =
  `List [f1 x1; f2 x2]

let json_of_tuple3 f1 f2 f3 (x1, x2, x3) =
  `List [f1 x1; f2 x2; f3 x3]

let json_of_tuple5 f1 f2 f3 f4 f5 (x1, x2, x3, x4, x5) =
  `List [f1 x1; f2 x2; f3 x3; f4 x4; f5 x5]

let json_of_located_string s =
  json_of_located ~extra:[("value", `String (unloc s))] s

let json_of_psymbol sym = `String (unloc sym)
let json_of_psymbol_list syms = json_of_list json_of_psymbol syms

let json_of_psymbol_option =
  json_of_option json_of_psymbol

let json_of_osymbol_r = function
  | None      -> `Null
  | Some symb -> json_of_psymbol symb

let json_of_osymbol os =
  json_of_located ~extra:[("value", json_of_osymbol_r os.pl_desc)] os

let json_of_osymbol_list = json_of_list json_of_osymbol

let rec json_of_pmsymbol (ms : pmsymbol) =
  `List (List.map json_of_pmsymbol_entry ms)

and json_of_pmsymbol_entry (sym, args) =
  let args_json =
    match args with
    | None     -> `Null
    | Some sub -> json_of_list json_of_pmsymbol_located sub
  in
  `Assoc [
    ("symbol", json_of_psymbol sym);
    ("args"  , args_json);
  ]

and json_of_pmsymbol_located m =
  json_of_located ~extra:[("segments", json_of_pmsymbol (unloc m))] m

let json_of_pgamepath path =
  let (m, s) = unloc path in
  json_of_located
    ~extra:[
      ("module", json_of_pmsymbol m);
      ("symbol", json_of_psymbol s);
    ]
    path

let json_of_side = function
  | `Left  -> `String "left"
  | `Right -> `String "right"

let json_of_oside = function
  | None      -> `Null
  | Some side -> json_of_side side

let json_of_trepeat (mode, count) =
  `Assoc [
    ("mode" , `String (match mode with `All -> "all" | `Maybe -> "maybe"));
    ("count", json_of_int_option count);
  ]

let json_of_ppgoptions options =
  let json_of_ppg = function
    | `Delta None         -> "delta"
    | `Delta (Some `Case) -> "delta-case"
    | `Delta (Some `Split)-> "delta-split"
    | `Split              -> "split"
    | `Solve              -> "solve"
    | `Subst              -> "subst"
    | `Disjunctive        -> "disjunctive"
  in
  json_of_list
    (fun (flag, opt) ->
       `Assoc [("enabled", `Bool flag); ("option", `String (json_of_ppg opt))])
    options

let json_of_pcaseoptions options =
  json_of_list
    (fun (flag, opt) ->
       let kind =
         match opt with
         | `Ambient -> "ambient"
       in
       `Assoc [("enabled", `Bool flag); ("option", `String kind)])
    options

let json_of_tfoc1 (a, b) =
  json_of_pair json_of_int_option (a, b)

let json_of_tfoc_list_opt = function
  | None      -> `Null
  | Some list -> json_of_list json_of_tfoc1 list

let json_of_tfocus (left, right) =
  json_of_pair json_of_tfoc_list_opt (left, right)

let string_of_logtactic = function
  | Preflexivity    -> "reflexivity"
  | Passumption     -> "assumption"
  | Psmt _          -> "smt"
  | Psplit None     -> "split"
  | Psplit (Some n) -> Printf.sprintf "split %d" n
  | Pfield _        -> "field"
  | Pring _         -> "ring"
  | Palg_norm       -> "algebraic_norm"
  | Pexists fs      -> Printf.sprintf "exists %d" (List.length fs)
  | Pleft           -> "left"
  | Pright          -> "right"
  | Ptrivial        -> "trivial"
  | Pcongr          -> "congruence"
  | Pelim _         -> "elim"
  | Papply _        -> "apply"
  | Pcut _          -> "cut"
  | Pcutdef _       -> "cutdef"
  | Pmove _         -> "move"
  | Pclear _        -> "clear"
  | Prewrite _      -> "rewrite"
  | Prwnormal _     -> "rwnormal"
  | Psubst _        -> "subst"
  | Psimplify _     -> "simplify"
  | Pcbv _          -> "cbv"
  | Pchange _       -> "change"
  | Ppose _         -> "pose"
  | Pmemory _       -> "memory"
  | Pgenhave _      -> "genhave"
  | Pwlog _         -> "wlog"
  | Pcoq _          -> "coq"

let string_of_phltactic = function
  | Pskip                  -> "skip"
  | Prepl_stmt _           -> "repl_stmt"
  | Pfun `Def              -> "fun_def"
  | Pfun (`Abs _)          -> "fun_abs"
  | Pfun (`Upto _)         -> "fun_upto"
  | Pfun `Code             -> "fun_code"
  | Papp _                 -> "app"
  | Pwp _                  -> "wp"
  | Psp _                  -> "sp"
  | Pwhile _               -> "while"
  | Pasyncwhile _          -> "asyncwhile"
  | Pfission _             -> "fission"
  | Pfusion _              -> "fusion"
  | Punroll _              -> "unroll"
  | Psplitwhile _          -> "splitwhile"
  | Pcall _                -> "call"
  | Pcallconcave _         -> "call_concave"
  | Prcond _               -> "rcond"
  | Prmatch _              -> "rmatch"
  | Pcond _                -> "cond"
  | Pmatch _               -> "match"
  | Pswap _                -> "swap"
  | Pcfold _               -> "cfold"
  | Pinline _              -> "inline"
  | Poutline _             -> "outline"
  | Pinterleave _          -> "interleave"
  | Pkill _                -> "kill"
  | Pasgncase _            -> "asgncase"
  | Prnd _                 -> "rnd"
  | Prndsem _              -> "rndsem"
  | Palias _               -> "alias"
  | Pweakmem _             -> "weakmem"
  | Pset _                 -> "set"
  | Psetmatch _            -> "setmatch"
  | Pconseq _              -> "conseq"
  | Pconseqauto _          -> "conseqauto"
  | Pconcave _             -> "concave"
  | Phrex_elim             -> "hrex_elim"
  | Phrex_intro _          -> "hrex_intro"
  | Phecall _              -> "hecall"
  | Pexfalso               -> "exfalso"
  | Pbydeno _              -> "bydeno"
  | PPr _                  -> "ppr"
  | Pbyupto                -> "byupto"
  | Pfel _                 -> "fel"
  | Phoare                 -> "phoare"
  | Pprbounded             -> "prbounded"
  | Psim _                 -> "sim"
  | Ptrans_stmt _          -> "trans_stmt"
  | Prw_equiv _            -> "rw_equiv"
  | Psymmetry              -> "symmetry"
  | Pbdhoare_split _       -> "bdhoare_split"
  | Pprocchange _          -> "procchange"
  | Pprocrewrite _         -> "procrewrite"
  | Peager_seq _           -> "eager_seq"
  | Peager_if              -> "eager_if"
  | Peager_while _         -> "eager_while"
  | Peager_fun_def         -> "eager_fun_def"
  | Peager_fun_abs _       -> "eager_fun_abs"
  | Peager_call _          -> "eager_call"
  | Peager _               -> "eager"
  | Pbd_equiv _            -> "bd_equiv"
  | Pauto                  -> "auto"
  | Plossless              -> "lossless"

let json_of_prevert pr =
  `Assoc [
    ("clear", json_of_psymbol_list pr.pr_clear);
    ("generators", `Int (List.length pr.pr_genp));
  ]

let json_of_prevertv pr =
  `Assoc [
    ("rev" , json_of_prevert pr.pr_rev);
    ("view", `Int (List.length pr.pr_view));
  ]

let trimmed_source_of_loc loc =
  match snippet_of_loc loc with
  | None -> None
  | Some src ->
      let trimmed = String.trim src in
      if trimmed = "" then None else Some trimmed

let snippet_field loc =
  match json_of_source loc with
  | `Null -> []
  | json  -> [("snippet", json)]

let string_of_ipdone = function
  | None -> "//"
  | Some `Default -> "//="
  | Some `Variant -> "//~="

let string_of_ipsimplify = function
  | `Default -> "/="
  | `Variant -> "/~="

let string_of_ipsmt loud =
  if loud then "//#" else "/#"

let string_of_crushmode mode =
  match mode.cm_simplify, mode.cm_solve with
  | false, false -> "|>"
  | true , false -> "/>"
  | false, true  -> "||>"
  | true , true  -> "//>"

let ensure_slash s =
  if s = "" then "/" else if s.[0] = '/' then s else "/" ^ s

let view_source loc =
  match trimmed_source_of_loc loc with
  | Some s -> ensure_slash s
  | None -> "/"

let resolved_source ?fallback loc =
  match trimmed_source_of_loc loc with
  | Some s when s <> "" -> s
  | _ -> odfl "" fallback

let rec json_of_intropattern ip =
  json_of_list json_of_intropattern1 ip

and json_of_intropattern1 p =
  let emit kind ?fallback ?(force=false) extras =
    let source =
      if force then odfl "" fallback else resolved_source ?fallback p.pl_loc
    in
    let base =
      ("kind", `String kind)
      :: ("source", `String source)
      :: snippet_field p.pl_loc
    in
    `Assoc (base @ extras)
  in
  match p.pl_desc with
  | IPCore `Revert ->
      emit "revert" []
  | IPCore `Clear ->
      emit "clear" []
  | IPCore (`Named s) ->
      emit "named" [("name", `String s)]
  | IPCore (`Anonymous _) ->
      emit "anonymous" ~fallback:"?" []
  | IPDup ->
      emit "dup" []
  | IPCase (_, pats) ->
      begin
        match pats with
        | [single] ->
            emit "case" [("patterns", `List [json_of_intropattern single])]
        | _ ->
            `List []
      end
  | IPView _ ->
      emit "view" ~fallback:(view_source p.pl_loc) ~force:true []
  | IPRw (_, side, _) ->
      let direction =
        match side with
        | `LtoR -> "ltr"
        | `RtoL -> "rtl"
      in
      emit "rw" [("direction", `String direction)]
  | IPDelta _ ->
      emit "delta" []
  | IPSubst _ ->
      emit "subst" []
  | IPClear names ->
      emit "clear-names" [("names", json_of_psymbol_list names)]
  | IPDone mode ->
      let attrs =
        match mode with
        | None -> []
        | Some `Default -> [("variant", `String "default")]
        | Some `Variant -> [("variant", `String "variant")]
      in
      emit "done" ~fallback:(string_of_ipdone mode) ~force:true attrs
  | IPSmt (loud, _) ->
      emit "smt" ~fallback:(string_of_ipsmt loud) ~force:true [("loud", `Bool loud)]
  | IPSubstTop _ ->
      emit "subst-top" []
  | IPSimplify mode ->
      let variant =
        match mode with
        | `Default -> "default"
        | `Variant -> "variant"
      in
      emit "simplify" ~fallback:(string_of_ipsimplify mode) ~force:true [("variant", `String variant)]
  | IPCrush cm ->
      emit "crush" ~fallback:(string_of_crushmode cm) ~force:true [
        ("simplify", `Bool cm.cm_simplify);
        ("solve"   , `Bool cm.cm_solve);
      ]
  | IPBreak ->
      emit "break" ~fallback:"-" []

let intropattern_of_token token =
  match token.pl_desc with
  | `Core cores ->
      List.map
        (fun ip ->
           mk_loc ip.pl_loc (IPCore (unloc ip)))
        cores
  | `Dup ->
      [mk_loc token.pl_loc IPDup]
  | `Done mode ->
      [mk_loc token.pl_loc (IPDone mode)]
  | `Smt info ->
      [mk_loc token.pl_loc (IPSmt info)]
  | `Clear xs ->
      [mk_loc token.pl_loc (IPClear xs)]
  | `Case (mode, branches) ->
      [mk_loc token.pl_loc (IPCase (mode, branches))]
  | `Rw args ->
      [mk_loc token.pl_loc (IPRw args)]
  | `Delta args ->
      [mk_loc token.pl_loc (IPDelta args)]
  | `View pe ->
      [mk_loc token.pl_loc (IPView pe)]
  | `Subst args ->
      [mk_loc token.pl_loc (IPSubst args)]
  | `SubstTop args ->
      [mk_loc token.pl_loc (IPSubstTop args)]
  | `Simpl mode ->
      [mk_loc token.pl_loc (IPSimplify mode)]
  | `Crush cm ->
      [mk_loc token.pl_loc (IPCrush cm)]

let flatten_json_list = function
  | `List xs -> xs
  | json -> [json]

let sint_of_list =
  List.fold_left (fun set v -> Sint.add v set) Sint.empty

let synthesize_intro_tail_bridges
    (events : intro_element_event list)
    (apps : tactic_application list) =
  match apps with
  | [] -> []
  | app :: _ ->
      let block_outs = app.ta_global_out in
      if List.is_empty block_outs then []
      else
        let relevant =
          List.filter
            (fun event ->
               match event.ie_element with
               | IEBridge -> false
               | _ -> true)
            events
        in
        if List.is_empty relevant then []
        else
          let arr = Array.of_list relevant in
          let len = Array.length arr in
          let future_inputs = Array.make len Sint.empty in
          let seen = ref Sint.empty in
          for idx = len - 1 downto 0 do
            future_inputs.(idx) <- !seen;
            let inputs = sint_of_list arr.(idx).ie_app.ta_global_in in
            seen := Sint.union inputs !seen
          done;
          let tails = ref [] in
          for idx = 0 to len - 1 do
            let outs = arr.(idx).ie_app.ta_global_out in
            let future = future_inputs.(idx) in
            List.iter
              (fun out ->
                 if not (Sint.mem out future) then
                   tails := !tails @ [out])
              outs
          done;
          let rec pair olds news acc =
            match olds, news with
            | (old :: olds', new_goal :: new_goals') ->
                let acc =
                  if old = new_goal then acc
                  else
                    let app = {
                      ta_local_in = [old];
                      ta_local_out = [new_goal];
                      ta_global_in = [old];
                      ta_global_out = [new_goal];
                    } in
                    { ie_element = IEBridge; ie_app = app } :: acc
                in
                pair olds' new_goals' acc
            | _ -> List.rev acc
          in
          pair !tails block_outs []

let json_entries_of_intro_element event =
  let base_entries =
    match event.ie_element with
    | IEPattern tok ->
        let patt = intropattern_of_token tok in
        flatten_json_list (json_of_intropattern patt)
    | IEGen pr ->
        [`Assoc [
            ("kind"  , `String "generalize");
            ("revert", json_of_prevert pr);
          ]]
    | IEBridge ->
        [`Assoc [("kind", `String "bridge")]]
  in
  let goal_fields = json_fields_of_application event.ie_app in
  let add_fields entry =
    match entry with
    | `Assoc fields -> `Assoc (fields @ goal_fields)
    | json -> json
  in
  List.map add_fields base_entries

let json_of_introgenpattern = function
  | `Ip ip  ->
      `Assoc [
        ("kind"    , `String "intros");
        ("pattern" , json_of_intropattern ip);
      ]
  | `Gen pr ->
      `Assoc [
        ("kind" , `String "generalize");
        ("revert", json_of_prevert pr);
      ]

(* Detailed AST helpers for tactic argument serialization ------------------ *)

let json_of_pformula (pf : pformula) =
  json_of_located pf

let json_of_pformula_option =
  json_of_option json_of_pformula

let json_of_pformula_list =
  json_of_list json_of_pformula

let json_of_pformula_pair =
  json_of_pair json_of_pformula

let json_of_pformula_option_pair =
  json_of_pair json_of_pformula_option

let json_of_pformula_tuple3 =
  json_of_tuple3 json_of_pformula json_of_pformula json_of_pformula

let json_of_pformula_option_tuple3 =
  json_of_tuple3 json_of_pformula_option json_of_pformula_option json_of_pformula_option

let json_of_pexpr expr =
  match expr.pl_desc with
  | Expr pf ->
      json_of_located
        ~extra:[("formula", json_of_pformula pf)]
        expr

let json_of_pexpr_list =
  json_of_list json_of_pexpr

let json_of_plpattern lp =
  json_of_located lp

let merge_locs acc loc =
  if EcLocation.isdummy loc then acc
  else
    match acc with
    | None   -> Some loc
    | Some l -> Some (EcLocation.merge l loc)

let loc_of_pinstr_list stmt =
  List.fold_left
    (fun acc instr -> merge_locs acc instr.pl_loc)
    None stmt

let json_of_pstmt stmt =
  let loc = loc_of_pinstr_list stmt in
  match loc with
  | None ->
      `Assoc [
        ("length", `Int (List.length stmt));
        ("source", `Null);
      ]
  | Some loc ->
      `Assoc [
        ("length", `Int (List.length stmt));
        ("source", json_of_source loc);
      ]

let json_of_ptactics_ref :
  (ptactics -> Yojson.Basic.t) ref = ref (fun _ -> `List [])

let json_of_ptactics_located = function
  | None -> `Null
  | Some located ->
      json_of_located
        ~extra:[
          ("tactics", (!json_of_ptactics_ref) (unloc located));
        ]
        located

let json_of_ppt_head :
  type a. (a -> Yojson.Basic.t) -> a ppt_head -> Yojson.Basic.t =
  fun json_of_cut -> function
  | FPNamed (qs, annot) ->
      `Assoc [
        ("kind" , `String "named");
        ("name" , json_of_pqsymbol qs);
        ("annot", json_of_option json_of_located annot);
      ]
  | FPCut cut ->
      `Assoc [
        ("kind" , `String "cut");
        ("value", json_of_cut cut);
      ]

let rec json_of_gppterm :
  type a. (a -> Yojson.Basic.t) -> a gppterm -> Yojson.Basic.t =
  fun json_of_cut term ->
  `Assoc [
    ("mode",
     `String (match term.fp_mode with `Implicit -> "implicit" | `Explicit -> "explicit"));
    ("head", json_of_ppt_head json_of_cut term.fp_head);
    ("args", json_of_list json_of_ppt_arg term.fp_args);
  ]

and json_of_ppt_arg arg =
  match arg.pl_desc with
  | EA_none ->
      json_of_located ~extra:[("kind", `String "none")] arg
  | EA_form pf ->
      json_of_located
        ~extra:[
          ("kind"   , `String "formula");
          ("formula", json_of_pformula pf);
        ]
        arg
  | EA_mem mem ->
      json_of_located
        ~extra:[
          ("kind" , `String "memory");
          ("value", json_of_psymbol mem);
        ]
        arg
  | EA_mod ms ->
      json_of_located
        ~extra:[
          ("kind" , `String "module");
          ("value", json_of_pmsymbol_located ms);
        ]
        arg
  | EA_proof proof ->
      json_of_located
        ~extra:[
          ("kind" , `String "proof");
          ("term" , json_of_gppterm json_of_pformula_option proof);
        ]
        arg
  | EA_tactic mode ->
      let name =
        match mode with
        | `Done    -> "done"
        | `Smt     -> "smt"
        | `DoneSmt -> "done-smt"
      in
      json_of_located
        ~extra:[
          ("kind" , `String "tactic");
          ("value", `String name);
        ]
        arg

let json_of_ppterm term =
  json_of_gppterm json_of_pformula_option term

let json_of_ppterm_list =
  json_of_list json_of_ppterm

let json_of_call_info = function
  | CI_spec (pre, post) ->
      `Assoc [
        ("kind" , `String "spec");
        ("pre"  , json_of_pformula pre);
        ("post" , json_of_pformula post);
      ]
  | CI_inv inv ->
      `Assoc [
        ("kind", `String "inv");
        ("formula", json_of_pformula inv);
      ]
  | CI_upto (pre, post, bound) ->
      `Assoc [
        ("kind" , `String "upto");
        ("pre"  , json_of_pformula pre);
        ("post" , json_of_pformula post);
        ("bound", json_of_pformula_option bound);
      ]

let json_of_call_term term =
  let info =
    match term.fp_head with
    | FPCut info -> json_of_call_info info
    | FPNamed (qs, annot) ->
        `Assoc [
          ("kind" , `String "named");
          ("name" , json_of_pqsymbol qs);
          ("annot", json_of_option json_of_located annot);
        ]
  in
  let assoc = [
    ("mode",
     `String (match term.fp_mode with `Implicit -> "implicit" | `Explicit -> "explicit"));
    ("info", info);
  ] in
  let assoc =
    if term.fp_args = [] then assoc
    else assoc @ [("args", json_of_list json_of_ppt_arg term.fp_args)]
  in
  `Assoc assoc

let json_of_apply_info = function
  | `ApplyIn (ppterm, sym) ->
      `Assoc [
        ("kind" , `String "apply-in");
        ("term" , json_of_ppterm ppterm);
        ("target", json_of_psymbol sym);
      ]
  | `Apply (terms, mode) ->
      let mode =
        match mode with
        | `Apply -> "apply"
        | `Exact -> "exact"
        | `Alpha -> "alpha"
      in
      `Assoc [
        ("kind" , `String "apply");
        ("mode" , `String mode);
        ("terms", json_of_ppterm_list terms);
      ]
  | `Top mode ->
      let mode =
        match mode with
        | `Apply -> "apply"
        | `Exact -> "exact"
        | `Alpha -> "alpha"
      in
      `Assoc [
        ("kind", `String "top");
        ("mode", `String mode);
      ]
  | `Alpha term ->
      `Assoc [
        ("kind", `String "alpha");
        ("term", json_of_ppterm term);
      ]
  | `ExactType sym ->
      `Assoc [
        ("kind", `String "exact-type");
        ("name", json_of_pqsymbol sym);
      ]

let json_of_pcutdef def =
  `Assoc [
    ("name" , json_of_pqsymbol def.ptcd_name);
    ("types", json_of_option json_of_located def.ptcd_tys);
    ("args" , json_of_list json_of_ppt_arg def.ptcd_args);
  ]

let json_of_clear_info = function
  | `Exclude names ->
      `Assoc [
        ("kind" , `String "exclude");
        ("names", json_of_psymbol_list names);
      ]
  | `Include names ->
      `Assoc [
        ("kind" , `String "include");
        ("names", json_of_psymbol_list names);
      ]

let json_of_include_exclude = function
  | `Include -> `String "include"
  | `Exclude -> `String "exclude"

let json_of_pdbmap1 entry =
  `Assoc [
    ("flag", json_of_include_exclude entry.pht_flag);
    ("kind",
     `String (match entry.pht_kind with `Theory -> "theory" | `Lemma -> "lemma"));
    ("name", json_of_pqsymbol entry.pht_name);
  ]

let json_of_pdbhint hint =
  json_of_list json_of_pdbmap1 hint

let json_of_pprover_list plist =
  `Assoc [
    ("use_only", json_of_list json_of_located_string plist.pp_use_only);
    ("add_rm",
     json_of_list
       (fun (flag, name) ->
          `Assoc [
            ("flag", json_of_include_exclude flag);
            ("name", json_of_located_string name);
          ])
       plist.pp_add_rm);
  ]

let json_of_pprover_infos info =
  `Assoc [
    ("max"       , json_of_int_option info.pprov_max);
    ("timeout"   , json_of_int_option info.pprov_timeout);
    ("cpufactor" , json_of_int_option info.pprov_cpufactor);
    ("names"     , json_of_option json_of_pprover_list info.pprov_names);
    ("quorum"    , json_of_int_option info.pprov_quorum);
    ("verbose"   , json_of_option json_of_int_option info.pprov_verbose);
    ("version"   ,
     match info.pprov_version with
     | None       -> `Null
     | Some `Lazy -> `String "lazy"
     | Some `Full -> `String "full");
    ("lem_all"   , json_of_option (fun b -> `Bool b) info.plem_all);
    ("lem_max"   ,
     match info.plem_max with
     | None       -> `Null
     | Some inner -> json_of_int_option inner);
    ("lem_iterate", json_of_option (fun b -> `Bool b) info.plem_iterate);
    ("wanted"    , json_of_option json_of_pdbhint info.plem_wanted);
    ("unwanted"  , json_of_option json_of_pdbhint info.plem_unwanted);
    ("dumpin"    , json_of_option json_of_located_string info.plem_dumpin);
    ("selected"  , json_of_option (fun b -> `Bool b) info.plem_selected);
    ("smt_debug" , json_of_option (fun b -> `Bool b) info.psmt_debug);
  ]

let json_of_rwside = function
  | `LtoR -> `String "l-to-r"
  | `RtoL -> `String "r-to-l"

let json_of_rwocci = function
  | `Inclusive set ->
      `Assoc [
        ("kind"    , `String "inclusive");
        ("indexes" , `List (List.map (fun i -> `Int i) (Sint.elements set)));
      ]
  | `Exclusive set ->
      `Assoc [
        ("kind"    , `String "exclusive");
        ("indexes" , `List (List.map (fun i -> `Int i) (Sint.elements set)));
      ]
  | `All ->
      `Assoc [("kind", `String "all")]

let json_of_rwocc = function
  | None      -> `Null
  | Some occi -> json_of_rwocci occi

let json_of_rwoptions (side, repeat, occ, pf) =
  `Assoc [
    ("side"   , json_of_rwside side);
    ("repeat" , json_of_option json_of_trepeat repeat);
    ("occurs" , json_of_rwocc occ);
    ("guard"  , json_of_pformula_option pf);
  ]

let json_of_rwarg1 arg =
  let extra =
    match arg.pl_desc with
    | RWSimpl variant ->
        [("variant",
          `String (match variant with `Default -> "default" | `Variant -> "variant"))]
    | RWDelta (options, formula) ->
        [ ("options", json_of_rwoptions options);
          ("formula", json_of_pformula formula) ]
    | RWRw (options, entries) ->
        let convert (side, term) =
          `Assoc [
            ("side", json_of_rwside side);
            ("term", json_of_ppterm term);
          ]
        in
        [ ("options", json_of_rwoptions options);
          ("entries", json_of_list convert entries) ]
    | RWPr (sym, formula) ->
        [ ("symbol" , json_of_psymbol sym);
          ("formula", json_of_pformula_option formula) ]
    | RWDone variant ->
        [ ("mode",
            match variant with
            | None       -> `String "default"
            | Some `Default -> `String "default"
            | Some `Variant -> `String "variant") ]
    | RWSmt (flag, info) ->
        [ ("interactive", `Bool flag);
          ("info"       , json_of_pprover_infos info) ]
    | RWApp term ->
        [ ("term", json_of_ppterm term) ]
    | RWTactic tac ->
        let name =
          match tac with
          | `Ring  -> "ring"
          | `Field -> "field"
        in
        [ ("mode", `String name) ]
  in
  json_of_located ~extra:(("kind", `String "rw") :: extra) arg

let json_of_rwarg (focus, arg) =
  `Assoc [
    ("focus",
     match focus with
     | None      -> `Null
     | Some foc  ->
         json_of_located
           ~extra:[("value", json_of_tfocus (unloc foc))]
           foc);
    ("argument", json_of_rwarg1 arg);
  ]

let json_of_preduction red =
  `Assoc [
    ("beta"   , `Bool red.pbeta);
    ("delta"  , json_of_option json_of_pqsymbol_list red.pdelta);
    ("zeta"   , `Bool red.pzeta);
    ("iota"   , `Bool red.piota);
    ("eta"    , `Bool red.peta);
    ("logic"  , `Bool red.plogic);
    ("modpath", `Bool red.pmodpath);
    ("user"   , `Bool red.puser);
  ]

let json_of_ptybinding (names, ty) =
  `Assoc [
    ("names", json_of_osymbol_list names);
    ("type" , json_of_located ty);
  ]

let json_of_ptybindings =
  json_of_list json_of_ptybinding

let json_of_pgenhave (name, pattern, clear, formula) =
  `Assoc [
    ("name"   , json_of_psymbol name);
    ("pattern", json_of_option json_of_intropattern pattern);
    ("clear"  , json_of_psymbol_list clear);
    ("formula", json_of_pformula formula);
  ]

let json_of_coq_mode = function
  | EcProvers.Check -> `String "check"
  | EcProvers.Edit  -> `String "edit"
  | EcProvers.Fix   -> `String "fix"

let json_of_include_exclude = function
  | `Include -> `String "include"
  | `Exclude -> `String "exclude"

let json_of_pdbmap1 entry =
  `Assoc [
    ("flag", json_of_include_exclude entry.pht_flag);
    ("kind",
     `String (match entry.pht_kind with `Theory -> "theory" | `Lemma -> "lemma"));
    ("name", json_of_pqsymbol entry.pht_name);
  ]

let json_of_pdbhint hint =
  json_of_list json_of_pdbmap1 hint

let json_of_pprover_list plist =
  `Assoc [
    ("use_only", json_of_list json_of_located_string plist.pp_use_only);
    ("add_rm",
     json_of_list
       (fun (flag, name) ->
          `Assoc [
            ("flag", json_of_include_exclude flag);
            ("name", json_of_located_string name);
          ])
       plist.pp_add_rm);
  ]

let json_of_pprover_infos info =
  `Assoc [
    ("max"       , json_of_int_option info.pprov_max);
    ("timeout"   , json_of_int_option info.pprov_timeout);
    ("cpufactor" , json_of_int_option info.pprov_cpufactor);
    ("names"     , json_of_option json_of_pprover_list info.pprov_names);
    ("quorum"    , json_of_int_option info.pprov_quorum);
    ("verbose"   , json_of_option json_of_int_option info.pprov_verbose);
    ("version"   ,
     match info.pprov_version with
     | None       -> `Null
     | Some `Lazy -> `String "lazy"
     | Some `Full -> `String "full");
    ("lem_all"   , json_of_option (fun b -> `Bool b) info.plem_all);
    ("lem_max"   ,
     match info.plem_max with
     | None       -> `Null
     | Some inner -> json_of_int_option inner);
    ("lem_iterate", json_of_option (fun b -> `Bool b) info.plem_iterate);
    ("wanted"    , json_of_option json_of_pdbhint info.plem_wanted);
    ("unwanted"  , json_of_option json_of_pdbhint info.plem_unwanted);
    ("dumpin"    , json_of_option json_of_located_string info.plem_dumpin);
    ("selected"  , json_of_option (fun b -> `Bool b) info.plem_selected);
    ("smt_debug" , json_of_option (fun b -> `Bool b) info.psmt_debug);
  ]

let json_of_pcut (kind, pattern, formula, proof) =
  let kind =
    match kind with
    | `Have -> "have"
    | `Suff -> "suff"
  in
  `Assoc [
    ("kind"   , `String kind);
    ("pattern", json_of_intropattern pattern);
    ("formula", json_of_pformula formula);
    ("script" , json_of_ptactics_located proof);
  ]

let json_of_doption f = function
  | Single v ->
      `Assoc [
        ("kind" , `String "single");
        ("value", f v);
      ]
  | Double (v1, v2) ->
      `Assoc [
        ("kind" , `String "double");
        ("first", f v1);
        ("second", f v2);
      ]

let json_of_pcp_match = function
  | `If          -> `String "if"
  | `While       -> `String "while"
  | `Match       -> `String "match"
  | `Assign _    -> `String "assign"
  | `AssignTuple _ -> `String "assign-tuple"
  | `Sample _    -> `String "sample"
  | `Call _      -> `String "call"

let json_of_pcp_base = function
  | `ByPos idx ->
      `Assoc [
        ("kind", `String "by-pos");
        ("index", `Int idx);
      ]
  | `ByMatch (idx, selector) ->
      `Assoc [
        ("kind"    , `String "by-match");
        ("index"   , json_of_int_option idx);
        ("pattern" , json_of_pcp_match selector);
      ]

let json_of_pbranch_select = function
  | `Cond flag ->
      `Assoc [("kind", `String "cond"); ("branch", `Bool flag)]
  | `Match sym ->
      `Assoc [("kind", `String "match"); ("symbol", json_of_psymbol sym)]

let json_of_pcodepos1 (_, base) =
  `Assoc [
    ("base", json_of_pcp_base base);
  ]

let json_of_pcodepos1_option = json_of_option json_of_pcodepos1

let json_of_pcodepos (path, anchor) =
  `Assoc [
    ("path",
     json_of_list
       (fun (pos, select) ->
          `Assoc [
            ("position", json_of_pcodepos1 pos);
            ("select"  , json_of_pbranch_select select);
          ])
       path);
    ("anchor", json_of_pcodepos1 anchor);
  ]

let json_of_pcodeoffset1 = function
  | `ByOffset ofs ->
      `Assoc [
        ("kind" , `String "offset");
        ("value", `Int ofs);
      ]
  | `ByPosition pos ->
      `Assoc [
        ("kind" , `String "position");
        ("value", json_of_pcodepos1 pos);
      ]

let json_of_pcodepos_range (base, bound) =
  let bound =
    match bound with
    | `Base pos   -> `Assoc [("kind", `String "base"); ("value", json_of_pcodepos pos)]
    | `Offset pos -> `Assoc [("kind", `String "offset"); ("value", json_of_pcodepos1 pos)]
  in
  `Assoc [
    ("range", json_of_pcodepos base);
    ("bound", bound);
  ]

let json_of_pdocodepos1 = function
  | None        -> `Null
  | Some dopts  -> json_of_doption json_of_pcodepos1 dopts

let json_of_inlineopt = function
  | None -> `Null
  | Some (`UseTuple flag) ->
      `Assoc [
        ("kind" , `String "use-tuple");
        ("value", `Bool flag);
      ]

let rec json_of_inline_pat1 = function
  | `InlineXpath path ->
      `Assoc [
        ("kind", `String "xpath");
        ("path", json_of_pgamepath path);
      ]
  | `InlinePat (ms, (names, alias)) ->
      `Assoc [
        ("kind" , `String "pattern");
        ("path" , json_of_pmsymbol_located ms);
        ("names", json_of_psymbol_list names);
        ("alias", json_of_psymbol_option alias);
      ]
  | `InlineAll ->
      `Assoc [("kind", `String "all")]

and json_of_inline_pat pats =
  json_of_list
    (fun (mode, pat) ->
       `Assoc [
         ("mode",
          `String (match mode with `DIFF -> "diff" | `UNION -> "union"));
         ("pattern", json_of_inline_pat1 pat);
       ])
    pats

let json_of_inline_info = function
  | `ByName (side, opts, (pat, indexes)) ->
      `Assoc [
        ("kind"   , `String "by-name");
        ("side"   , json_of_oside side);
        ("options", json_of_inlineopt opts);
        ("pattern", json_of_inline_pat pat);
        ("indexes", json_of_option (json_of_list (fun i -> `Int i)) indexes);
      ]
  | `CodePos (side, opts, pos) ->
      `Assoc [
        ("kind"   , `String "codepos");
        ("side"   , json_of_oside side);
        ("options", json_of_inlineopt opts);
        ("pos"    , json_of_pcodepos pos);
      ]

let json_of_outline_kind = function
  | OKstmt body ->
      `Assoc [
        ("kind" , `String "stmt");
        ("body" , json_of_pstmt body);
      ]
  | OKproc (path, flag) ->
      `Assoc [
        ("kind"  , `String "proc");
        ("name"  , json_of_pgamepath path);
        ("exact" , `Bool flag);
      ]

let json_of_outline_info info =
  `Assoc [
    ("side" , json_of_side info.outline_side);
    ("range", json_of_pcodepos_range info.outline_range);
    ("kind" , json_of_outline_kind info.outline_kind);
  ]

let json_of_interleave_info located =
  let (side, (start, stop), ranges, depth) = unloc located in
  json_of_located
    ~extra:[
      ("side" , json_of_oside side);
      ("info" ,
       `Assoc [
         ("start" , `Int start);
         ("stop"  , `Int stop);
         ("ranges",
          json_of_list (fun (s, e) -> `Assoc [("start", `Int s); ("stop", `Int e)]) ranges);
         ("depth" , `Int depth);
       ]);
    ]
    located

let json_of_while_info info =
  `Assoc [
    ("invariant", json_of_pformula info.wh_inv);
    ("variant"  , json_of_pformula_option info.wh_vrnt);
    ("bounds"   ,
     match info.wh_bds with
     | None -> `Null
     | Some (`Bd (p1, p2)) ->
         `Assoc [
           ("kind", `String "bd");
           ("lower", json_of_pformula p1);
           ("upper", json_of_pformula p2);
         ]);
  ]

let json_of_async_while_info info =
  let json_of_test (expr, formula) =
    `Assoc [
      ("expr"   , json_of_pexpr expr);
      ("formula", json_of_pformula formula);
    ]
  in
  `Assoc [
    ("test" , json_of_pair json_of_test info.asw_test);
    ("predicate",
     let (pre, post) = info.asw_pred in
     `Assoc [
       ("pre" , json_of_pformula pre);
       ("post", json_of_pformula post);
     ]);
    ("invariant", json_of_pformula info.asw_inv);
  ]

let json_of_pcodepos_pair =
  json_of_pair json_of_pcodepos1

let json_of_pswap_kind kind =
  `Assoc [
    ("interval",
     match kind.interval with
     | None -> `Null
     | Some (base, bound) ->
         `Assoc [
           ("start", json_of_pcodepos1 base);
           ("end"  , json_of_pcodepos1_option bound);
         ]);
    ("offset", json_of_pcodeoffset1 kind.offset);
  ]

let json_of_psemrndpos pos =
  json_of_doption
    (fun (flag, codepos) ->
       `Assoc [
         ("flag", `Bool flag);
         ("pos" , json_of_pcodepos1 codepos);
       ])
    pos

let json_of_rnd_tac_info f1 f2 f3 = function
  | PNoRndParams ->
      `Assoc [("kind", `String "none")]
  | PSingleRndParam x ->
      `Assoc [
        ("kind" , `String "single");
        ("value", f3 x);
      ]
  | PTwoRndParams (x, y) ->
      `Assoc [
        ("kind" , `String "pair");
        ("first", f1 x);
        ("second", f1 y);
      ]
  | PMultRndParams (params, extra) ->
      let (a, b, c, d, e) = params in
      `Assoc [
        ("kind" , `String "multi");
        ("params",
         `List [f1 a; f1 b; f1 c; f1 d; f1 e]);
        ("extra", f2 extra);
      ]

let json_of_rnd_tac_info_f =
  json_of_rnd_tac_info json_of_pformula json_of_pformula_option json_of_pformula

let json_of_prrewrite = function
  | `Rw term  -> `Assoc [("kind", `String "rw"); ("term", json_of_ppterm term)]
  | `Simpl    -> `Assoc [("kind", `String "simpl")]

let json_of_fun_params params =
  json_of_list
    (fun (symbol, ty) ->
       `Assoc [
         ("symbol", json_of_osymbol symbol);
         ("type"  , json_of_located ty);
       ])
    params

let json_of_trans_kind = function
  | TKfun path ->
      `Assoc [
        ("kind", `String "fun");
        ("path", json_of_pgamepath path);
      ]
  | TKstmt (side, stmt) ->
      `Assoc [
        ("kind", `String "stmt");
        ("side", json_of_side side);
        ("body", json_of_pstmt stmt);
      ]
  | TKparsedStmt (side, (anchors, _regexp), stmt) ->
      let json_of_anchor (a1, a2) =
        let to_json = function
          | Without_anchor -> `String "without"
          | With_anchor    -> `String "with"
        in
        `List [to_json a1; to_json a2]
      in
      `Assoc [
        ("kind"   , `String "parsed-stmt");
        ("side"   , json_of_side side);
        ("anchors", json_of_anchor anchors);
        ("regexp" , `String "<regexp>");
        ("body"   , json_of_pstmt stmt);
      ]

let json_of_trans_formula = function
  | TFform (a, b, c, d) ->
      `Assoc [
        ("kind", `String "form");
        ("pre" , json_of_pformula a);
        ("post", json_of_pformula b);
        ("inv" , json_of_pformula c);
        ("cond", json_of_pformula d);
      ]
  | TFeq ->
      `Assoc [("kind", `String "eq")]

let json_of_trans_info (kind, formula) =
  `Assoc [
    ("kind"   , json_of_trans_kind kind);
    ("formula", json_of_trans_formula formula);
  ]

let json_of_fun_info = function
  | `Def ->
      `Assoc [("kind", `String "def")]
  | `Code ->
      `Assoc [("kind", `String "code")]
  | `Abs pf ->
      `Assoc [
        ("kind" , `String "abs");
        ("body" , json_of_pformula pf);
      ]
  | `Upto (pre, post, bound) ->
    `Assoc [
      ("kind" , `String "upto");
      ("pre"  , json_of_pformula pre);
      ("post" , json_of_pformula post);
      ("bound", json_of_pformula_option bound);
    ]

let json_of_tac_dir = function
  | Backs -> `String "backward"
  | Fwds  -> `String "forward"

let json_of_p_app_xt_info = function
  | PAppNone -> `String "none"
  | PAppSingle pf ->
      `Assoc [("kind", `String "single"); ("value", json_of_pformula pf)]
  | PAppMult (a, b, c, d, e) ->
      `Assoc [
        ("kind" , `String "multi");
        ("values",
         `List [
           json_of_pformula_option a;
           json_of_pformula_option b;
           json_of_pformula_option c;
           json_of_pformula_option d;
           json_of_pformula_option e;
         ]);
      ]

let json_of_app_info (side, dir, pos, formula, extra) =
  `Assoc [
    ("side"   , json_of_oside side);
    ("dir"    , json_of_tac_dir dir);
    ("pos"    , json_of_doption json_of_pcodepos1 pos);
    ("formula", json_of_doption json_of_pformula formula);
    ("extra"  , json_of_p_app_xt_info extra);
  ]

let json_of_pcond_info = function
  | `Head side ->
      `Assoc [
        ("kind", `String "head");
        ("side", json_of_oside side);
      ]
  | `Seq (side, bounds, formula) ->
      `Assoc [
        ("kind"   , `String "seq");
        ("side"   , json_of_oside side);
        ("bounds" , json_of_pair json_of_pcodepos1_option bounds);
        ("formula", json_of_pformula formula);
      ]
  | `SeqOne (side, pos, pre, post) ->
      `Assoc [
        ("kind" , `String "seq-one");
        ("side" , json_of_side side);
        ("pos"  , json_of_pcodepos1_option pos);
        ("pre"  , json_of_pformula pre);
        ("post" , json_of_pformula post);
      ]

let json_of_crushmode mode =
  `Assoc [
    ("simplify", `Bool mode.cm_simplify);
    ("solve"   , `Bool mode.cm_solve);
  ]

let json_of_matchmode = function
  | `DSided kind ->
      `Assoc [
        ("kind", `String "double-sided");
        ("mode",
         `String (match kind with `Eq -> "eq" | `ConstrSynced -> "constr-synced"));
      ]
  | `SSided side ->
      `Assoc [
        ("kind", `String "single-sided");
        ("side", json_of_side side);
      ]

let json_of_conseq_info = function
  | None -> `Null
  | Some (CQI_bd (cmp, formula)) ->
      let cmp =
        match cmp with
        | None            -> `Null
        | Some EcAst.FHle -> `String "le"
        | Some EcAst.FHeq -> `String "eq"
        | Some EcAst.FHge -> `String "ge"
      in
      `Assoc [
        ("kind"   , `String "bd");
        ("cmp"    , cmp);
        ("formula", json_of_pformula formula);
      ]

let json_of_deno_ppterm term =
  json_of_gppterm (json_of_pair json_of_pformula_option) term

let json_of_conseq_ppterm term =
  json_of_gppterm
    (fun (pair, info) ->
       `Assoc [
         ("pair", json_of_pair json_of_pformula_option pair);
         ("info", json_of_conseq_info info);
       ])
    term

let json_of_bdh_split = function
  | BDH_split_bop (a, b, c) ->
      `Assoc [
        ("kind" , `String "bop");
        ("lhs"  , json_of_pformula a);
        ("rhs"  , json_of_pformula b);
        ("bound", json_of_pformula_option c);
      ]
  | BDH_split_or_case (a, b, c) ->
      `Assoc [
        ("kind"  , `String "or-case");
        ("left"  , json_of_pformula a);
        ("right" , json_of_pformula b);
        ("final" , json_of_pformula c);
      ]
  | BDH_split_not (a, b) ->
      `Assoc [
        ("kind" , `String "not");
        ("guard", json_of_pformula_option a);
        ("body" , json_of_pformula b);
      ]

let json_of_fel_info info =
  `Assoc [
    ("counter", json_of_pformula info.pfel_cntr);
    ("assign" , json_of_pformula info.pfel_asg);
    ("q"      , json_of_pformula info.pfel_q);
    ("event"  , json_of_pformula info.pfel_event);
    ("predicates",
     json_of_list
       (fun (path, formula) ->
          `Assoc [
            ("path"   , json_of_pgamepath path);
            ("formula", json_of_pformula formula);
          ])
       info.pfel_specs);
    ("invariant", json_of_pformula_option info.pfel_inv);
  ]

let json_of_sim_info info =
  `Assoc [
    ("pos" ,
     match info.sim_pos with
     | None -> `Null
     | Some pair -> json_of_pair json_of_pcodepos1 pair);
    ("hint",
     let (entries, trailing) = info.sim_hint in
     `Assoc [
       ("entries",
        json_of_list
          (fun ((l, r), formula) ->
             `Assoc [
               ("left" , json_of_option json_of_pgamepath l);
               ("right", json_of_option json_of_pgamepath r);
               ("formula", json_of_pformula formula);
             ])
          entries);
       ("trailing", json_of_pformula_option trailing);
     ]);
    ("eqs", json_of_pformula_option info.sim_eqs);
  ]

let json_of_rw_eqv_info info =
  `Assoc [
    ("side" , json_of_side info.rw_eqv_side);
    ("dir"  ,
     `String (match info.rw_eqv_dir with `LtoR -> "l-to-r" | `RtoL -> "r-to-l"));
    ("pos"  , json_of_pcodepos1 info.rw_eqv_pos);
    ("lemma", json_of_ppterm info.rw_eqv_lemma);
    ("proc" ,
     match info.rw_eqv_proc with
     | None -> `Null
     | Some (args, ret) ->
         `Assoc [
           ("args", json_of_located args);
           ("return", json_of_option json_of_pexpr ret);
         ]);
  ]

let json_of_rwtac_kind = function
  | `Ring  -> `String "ring"
  | `Field -> `String "field"

let json_of_eager_info = function
  | LE_done sym ->
      `Assoc [
        ("kind", `String "done");
        ("name", json_of_psymbol sym);
      ]
  | LE_todo (sym, pre, post, inv, concl) ->
      `Assoc [
        ("kind" , `String "todo");
        ("name" , json_of_psymbol sym);
        ("pre"  , json_of_pstmt pre);
        ("post" , json_of_pstmt post);
        ("inv"  , json_of_pformula inv);
        ("concl", json_of_pformula concl);
      ]

let json_of_pcqoption = function
  | `Frame -> `String "frame"

let json_of_pcqoptions opts =
  json_of_list
    (fun (flag, opt) ->
       `Assoc [
         ("enabled", `Bool flag);
         ("option" , json_of_pcqoption opt);
       ])
    opts

let json_of_logtactic = function
  | Preflexivity ->
      mk_json "Preflexivity" []
  | Passumption ->
      mk_json "Passumption" []
  | Psmt info ->
      mk_json "Psmt" [("info", json_of_pprover_infos info)]
  | Psplit depth ->
      mk_json "Psplit" [("parts", json_of_int_option depth)]
  | Pfield symbols ->
      mk_json "Pfield" [("fields", json_of_psymbol_list symbols)]
  | Pring symbols ->
      mk_json "Pring" [("rings", json_of_psymbol_list symbols)]
  | Palg_norm ->
      mk_json "Palg_norm" []
  | Pexists args ->
      mk_json "Pexists" [("args", json_of_list json_of_ppt_arg args)]
  | Pleft ->
      mk_json "Pleft" []
  | Pright ->
      mk_json "Pright" []
  | Ptrivial ->
      mk_json "Ptrivial" []
  | Pcongr ->
      mk_json "Pcongr" []
  | Pelim (rev, sym) ->
      mk_json "Pelim" [
        ("revert", json_of_prevert rev);
        ("symbol", json_of_option json_of_pqsymbol sym);
      ]
  | Papply (info, revert) ->
      mk_json "Papply" [
        ("info"  , json_of_apply_info info);
        ("revert", json_of_option json_of_prevert revert);
      ]
  | Pcut data ->
      mk_json "Pcut" [("cut", json_of_pcut data)]
  | Pcutdef (pattern, def) ->
      mk_json "Pcutdef" [
        ("pattern", json_of_intropattern pattern);
        ("def"    , json_of_pcutdef def);
      ]
  | Pmove info ->
      mk_json "Pmove" [("info", json_of_prevertv info)]
  | Pclear info ->
      mk_json "Pclear" [("info", json_of_clear_info info)]
  | Prewrite (args, sym) ->
      mk_json "Prewrite" [
        ("args"  , json_of_list json_of_rwarg args);
        ("symbol", json_of_osymbol_r sym);
      ]
  | Prwnormal (formula, symbols) ->
      mk_json "Prwnormal" [
        ("formula", json_of_pformula formula);
        ("symbols", json_of_pqsymbol_list symbols);
      ]
  | Psubst formulas ->
      mk_json "Psubst" [("formulas", json_of_pformula_list formulas)]
  | Psimplify reduction ->
      mk_json "Psimplify" [("reduction", json_of_preduction reduction)]
  | Pcbv reduction ->
      mk_json "Pcbv" [("reduction", json_of_preduction reduction)]
  | Pchange formula ->
      mk_json "Pchange" [("formula", json_of_pformula formula)]
  | Ppose (name, bindings, occ, formula) ->
      mk_json "Ppose" [
        ("name"    , json_of_psymbol name);
        ("bindings", json_of_ptybindings bindings);
        ("occurs"  , json_of_rwocc occ);
        ("formula" , json_of_pformula formula);
      ]
  | Pmemory symbol ->
      mk_json "Pmemory" [("symbol", json_of_psymbol symbol)]
  | Pgenhave have ->
      mk_json "Pgenhave" [("info", json_of_pgenhave have)]
  | Pwlog (symbols, flag, formula) ->
      mk_json "Pwlog" [
        ("symbols", json_of_psymbol_list symbols);
        ("strict" , `Bool flag);
        ("formula", json_of_pformula formula);
      ]
  | Pcoq (mode, script, info) ->
      mk_json "Pcoq" [
        ("mode"  , json_of_option json_of_coq_mode mode);
        ("script", json_of_psymbol script);
        ("info"  , json_of_pprover_infos info);
      ]

let json_of_phltactic = function
  | Pskip ->
      mk_json "Pskip" []
  | Prepl_stmt info ->
      mk_json "Prepl_stmt" [("info", json_of_trans_info info)]
  | Pfun info ->
      mk_json "Pfun" [("info", json_of_fun_info info)]
  | Papp info ->
      mk_json "Papp" [("info", json_of_app_info info)]
  | Pwp pos ->
      mk_json "Pwp" [("position", json_of_pdocodepos1 pos)]
  | Psp pos ->
      mk_json "Psp" [("position", json_of_pdocodepos1 pos)]
  | Pwhile (side, info) ->
      mk_json "Pwhile" [
        ("side", json_of_oside side);
        ("info", json_of_while_info info);
      ]
  | Pasyncwhile info ->
      mk_json "Pasyncwhile" [("info", json_of_async_while_info info)]
  | Pfission (side, pos, (width, (start, stop))) ->
      mk_json "Pfission" [
        ("side" , json_of_oside side);
        ("pos"  , json_of_pcodepos pos);
        ("width", `Int width);
        ("range",
         `Assoc [
           ("start", `Int start);
           ("stop" , `Int stop);
         ]);
      ]
  | Pfusion (side, pos, (width, (start, stop))) ->
      mk_json "Pfusion" [
        ("side" , json_of_oside side);
        ("pos"  , json_of_pcodepos pos);
        ("width", `Int width);
        ("range",
         `Assoc [
           ("start", `Int start);
           ("stop" , `Int stop);
         ]);
      ]
  | Punroll (side, pos, flag) ->
      mk_json "Punroll" [
        ("side" , json_of_oside side);
        ("pos"  , json_of_pcodepos pos);
        ("exact", `Bool flag);
      ]
  | Psplitwhile (expr, side, pos) ->
      mk_json "Psplitwhile" [
        ("expr", json_of_pexpr expr);
        ("side", json_of_oside side);
        ("pos" , json_of_pcodepos pos);
      ]
  | Pcall (side, term) ->
      mk_json "Pcall" [
        ("side", json_of_oside side);
        ("term", json_of_call_term term);
      ]
  | Pcallconcave (formula, term) ->
      mk_json "Pcallconcave" [
        ("formula", json_of_pformula formula);
        ("term"   , json_of_call_term term);
      ]
  | Prcond (side, flag, pos) ->
      mk_json "Prcond" [
        ("side" , json_of_oside side);
        ("flag" , `Bool flag);
        ("pos"  , json_of_pcodepos1 pos);
      ]
  | Prmatch (side, symbol, pos) ->
      mk_json "Prmatch" [
        ("side"  , json_of_oside side);
        ("symbol", json_of_symbol symbol);
        ("pos"   , json_of_pcodepos1 pos);
      ]
  | Pcond info ->
      mk_json "Pcond" [("info", json_of_pcond_info info)]
  | Pmatch mode ->
      mk_json "Pmatch" [("mode", json_of_matchmode mode)]
  | Pswap entries ->
      let convert entry =
        let (side, kind) = unloc entry in
        json_of_located
          ~extra:[
            ("side", json_of_oside side);
            ("kind", json_of_pswap_kind kind);
          ]
          entry
      in
      mk_json "Pswap" [("entries", json_of_list convert entries)]
  | Pcfold (side, pos, count) ->
      mk_json "Pcfold" [
        ("side" , json_of_oside side);
        ("pos"  , json_of_pcodepos pos);
        ("count", json_of_int_option count);
      ]
  | Pinline info ->
      mk_json "Pinline" [("info", json_of_inline_info info)]
  | Poutline info ->
      mk_json "Poutline" [("info", json_of_outline_info info)]
  | Pinterleave info ->
      mk_json "Pinterleave" [("info", json_of_interleave_info info)]
  | Pkill (side, pos, count) ->
      mk_json "Pkill" [
        ("side" , json_of_oside side);
        ("pos"  , json_of_pcodepos pos);
        ("count", json_of_int_option count);
      ]
  | Pasgncase (side, pos) ->
      mk_json "Pasgncase" [
        ("side", json_of_oside side);
        ("pos" , json_of_pcodepos pos);
      ]
  | Prnd (side, pos, info) ->
      mk_json "Prnd" [
        ("side"    , json_of_oside side);
        ("pos"     , json_of_option json_of_psemrndpos pos);
        ("payload" , json_of_rnd_tac_info_f info);
      ]
  | Prndsem (flag, side, pos) ->
      mk_json "Prndsem" [
        ("strict", `Bool flag);
        ("side"  , json_of_oside side);
        ("pos"   , json_of_pcodepos1 pos);
      ]
  | Palias (side, pos, symbol) ->
      mk_json "Palias" [
        ("side"  , json_of_oside side);
        ("pos"   , json_of_pcodepos pos);
        ("symbol", json_of_osymbol_r symbol);
      ]
  | Pweakmem (side, sym, params) ->
      mk_json "Pweakmem" [
        ("side"  , json_of_oside side);
        ("symbol", json_of_psymbol sym);
        ("params", json_of_fun_params params);
      ]
  | Pset (side, pos, flag, sym, expr) ->
      mk_json "Pset" [
        ("side"  , json_of_oside side);
        ("pos"   , json_of_pcodepos pos);
        ("fresh" , `Bool flag);
        ("symbol", json_of_psymbol sym);
        ("expr"  , json_of_pexpr expr);
      ]
  | Psetmatch (side, pos, sym, formula) ->
      mk_json "Psetmatch" [
        ("side"  , json_of_oside side);
        ("pos"   , json_of_pcodepos pos);
        ("symbol", json_of_psymbol sym);
        ("formula", json_of_pformula formula);
      ]
  | Pconseq (options, triple) ->
      let triple_json =
        let (a, b, c) = triple in
        `List [
          json_of_option json_of_conseq_ppterm a;
          json_of_option json_of_conseq_ppterm b;
          json_of_option json_of_conseq_ppterm c;
        ]
      in
      mk_json "Pconseq" [
        ("options", json_of_pcqoptions options);
        ("proofs" , triple_json);
      ]
  | Pconseqauto mode ->
      mk_json "Pconseqauto" [("mode", json_of_crushmode mode)]
  | Pconcave (term, formula) ->
      mk_json "Pconcave" [
        ("term",
         json_of_gppterm
           (json_of_tuple2 json_of_pformula_option json_of_pformula_option)
           term);
        ("formula", json_of_pformula formula);
      ]
  | Phrex_elim ->
      mk_json "Phrex_elim" []
  | Phrex_intro (formulas, flag) ->
      mk_json "Phrex_intro" [
        ("formulas", json_of_pformula_list formulas);
        ("flag"    , `Bool flag);
      ]
  | Phecall (side, (qs, annot, formulas)) ->
      mk_json "Phecall" [
        ("side"    , json_of_oside side);
        ("name"    , json_of_pqsymbol qs);
        ("annot"   , json_of_option json_of_located annot);
        ("formulas", json_of_pformula_list formulas);
      ]
  | Pexfalso ->
      mk_json "Pexfalso" []
  | Pbydeno (kind, (term, flag, formula)) ->
      let mode =
        match kind with
        | `PHoare -> "phoare"
        | `Equiv  -> "equiv"
        | `EHoare -> "ehoare"
      in
      mk_json "Pbydeno" [
        ("mode"   , `String mode);
        ("term"   , json_of_deno_ppterm term);
        ("flag"   , `Bool flag);
        ("formula", json_of_pformula_option formula);
      ]
  | PPr pair ->
      mk_json "PPr" [
        ("pair",
         match pair with
         | None -> `Null
         | Some (a, b) ->
             `Assoc [
               ("left" , json_of_pformula a);
               ("right", json_of_pformula b);
             ]);
      ]
  | Pbyupto ->
      mk_json "Pbyupto" []
  | Pfel (pos, info) ->
      mk_json "Pfel" [
        ("pos" , json_of_pcodepos1 pos);
        ("info", json_of_fel_info info);
      ]
  | Phoare ->
      mk_json "Phoare" []
  | Pprbounded ->
      mk_json "Pprbounded" []
  | Psim (mode, info) ->
      mk_json "Psim" [
        ("mode" , json_of_option json_of_crushmode mode);
        ("info" , json_of_sim_info info);
      ]
  | Ptrans_stmt info ->
      mk_json "Ptrans_stmt" [("info", json_of_trans_info info)]
  | Prw_equiv info ->
      mk_json "Prw_equiv" [("info", json_of_rw_eqv_info info)]
  | Psymmetry ->
      mk_json "Psymmetry" []
  | Pbdhoare_split info ->
      mk_json "Pbdhoare_split" [("info", json_of_bdh_split info)]
  | Pprocchange (side, pos, expr) ->
      mk_json "Pprocchange" [
        ("side" , json_of_oside side);
        ("pos"  , json_of_pcodepos pos);
        ("expr" , json_of_pexpr expr);
      ]
  | Pprocrewrite (side, pos, action) ->
      mk_json "Pprocrewrite" [
        ("side"  , json_of_oside side);
        ("pos"   , json_of_pcodepos pos);
        ("action", json_of_prrewrite action);
      ]
  | Peager_seq (info, pos, formula) ->
      mk_json "Peager_seq" [
        ("info"   , json_of_eager_info info);
        ("pos"    , json_of_pair json_of_pcodepos1 pos);
        ("formula", json_of_pformula formula);
      ]
  | Peager_if ->
      mk_json "Peager_if" []
  | Peager_while info ->
      mk_json "Peager_while" [("info", json_of_eager_info info)]
  | Peager_fun_def ->
      mk_json "Peager_fun_def" []
  | Peager_fun_abs (info, formula) ->
      mk_json "Peager_fun_abs" [
        ("info"   , json_of_eager_info info);
        ("formula", json_of_pformula formula);
      ]
  | Peager_call term ->
      mk_json "Peager_call" [("term", json_of_call_term term)]
  | Peager (info, formula) ->
      mk_json "Peager" [
        ("info"   , json_of_eager_info info);
        ("formula", json_of_pformula formula);
      ]
  | Pbd_equiv (side, left, right) ->
      mk_json "Pbd_equiv" [
        ("side" , json_of_side side);
        ("left" , json_of_pformula left);
        ("right", json_of_pformula right);
      ]
  | Pauto ->
      mk_json "Pauto" []
  | Plossless ->
      mk_json "Plossless" []


(* -------------------------------------------------------------------- *)
let goal_trace_fields apps =
  match apps with
  | [] -> []
  | _ ->
      let maybe field enabled =
        if not enabled then None else json_of_goal_trace field apps
      in
      let acc = [] in
      let acc =
        match maybe `Emacs !include_emacs_goals with
        | Some v -> v :: acc
        | None -> acc
      in
      let acc =
        match maybe `Serialized !include_serialized_goals with
        | Some v -> v :: acc
        | None -> acc
      in
      List.rev acc

let enrich_prewrite_core tac core_json =
  match unloc tac.pt_core with
  | Plogic (Prewrite _) ->
      begin match core_json with
      | `Assoc fields ->
          let update_args_field value =
            match value with
            | `Assoc args_fields ->
                let args_fields =
                  List.map
                    (fun (k, v) ->
                       if k <> "tactic" then (k, v) else
                         let v =
                           match v with
                           | `Assoc tactic_fields ->
                               let tactic_fields =
                                 List.map
                                   (fun (tk, tv) ->
                                      if tk <> "args" then (tk, tv) else
                                        let tv =
                                          match tv with
                                          | `List arg_list ->
                                              let enriched =
                                                List.mapi
                                                  (fun idx arg_json ->
                                                     let events = consume_rewrite_applications tac idx in
                                                     let apps =
                                                       List.map (fun ev -> ev.re_app) events in
                                                     let paths =
                                                       events
                                                       |> List.map (fun ev -> ev.re_paths)
                                                       |> List.concat
                                                       |> List.filter (fun p -> p <> "")
                                                       |> List.sort_uniq String.compare
                                                     in
                                                    let chosen_path =
                                                      events
                                                      |> List.filter_map (fun ev -> ev.re_chosen)
                                                      |> List.rev
                                                      |> (function
                                                          | hd :: _ -> Some hd
                                                          | [] -> None)
                                                    in
                                                     let extras =
                                                       let goals = goal_trace_fields apps in
                                                       let resolved =
                                                         match paths with
                                                         | [] -> []
                                                         | _ ->
                                                             [("resolved_paths",
                                                               `List (List.map (fun p -> `String p) paths))]
                                                       in
                                                      let chosen =
                                                        match chosen_path with
                                                        | None -> []
                                                        | Some p -> [("chosen_path", `String p)]
                                                      in
                                                      goals @ resolved @ chosen
                                                     in
                                                     match extras with
                                                     | [] -> arg_json
                                                     | extras ->
                                                         begin match arg_json with
                                                         | `Assoc fields -> `Assoc (fields @ extras)
                                                         | json -> `Assoc (("value", json) :: extras)
                                                         end)
                                                  arg_list
                                              in
                                              `List enriched
                                          | _ -> tv
                                        in
                                        (tk, tv))
                                   tactic_fields
                               in
                               `Assoc tactic_fields
                           | _ -> v
                         in
                         (k, v))
                    args_fields
                in
                `Assoc args_fields
            | _ -> value
          in
          let fields =
            List.map
              (fun (k, v) ->
                 if k = "args" then (k, update_args_field v) else (k, v))
              fields
          in
          `Assoc fields
      | _ -> core_json
      end
  | _ -> core_json

let rec json_of_ptactics ts =
  json_of_list json_of_ptactic ts

and json_of_ptactic t =
  let core_json = json_of_ptactic_core t.pt_core in
  let core_json = enrich_prewrite_core t core_json in
  let base = [
    ("core"  , core_json);
  ] in
  let base =
    if !include_intros && not (List.is_empty t.pt_intros) then
      ("intros", json_of_intros t t.pt_intros) :: base
    else base
  in
  let apps = consume_tactic_applications t in
  let base =
    match apps with
    | [] -> base
    | _  ->
        let extras = goal_trace_fields apps in
        base @ extras
  in
  `Assoc base

and json_of_intros tac intros =
  let enrich idx intro =
    let base_assoc =
      match json_of_introgenpattern intro with
      | `Assoc fields -> fields
      | json -> [("value", json)]
    in
    let apps = consume_intro_applications tac idx in
    let events = consume_intro_elements tac idx in
    let events =
      let bridges = synthesize_intro_tail_bridges events apps in
      events @ bridges
    in
    let extras =
      match apps with
      | [] -> []
      | _ ->
          let maybe field enabled =
            if not enabled then None else json_of_goal_trace field apps
          in
          let acc = [] in
          let acc =
            match maybe `Emacs !include_emacs_goals with
            | Some v -> v :: acc
            | None -> acc
          in
          let acc =
            match maybe `Serialized !include_serialized_goals with
            | Some v -> v :: acc
            | None -> acc
          in
          List.rev acc
    in
    let base_assoc =
      match events with
      | [] -> base_assoc
      | _ ->
          let pattern_entries =
            List.concat (List.map json_entries_of_intro_element events)
          in
          let rec replace = function
            | [] -> [("pattern", `List pattern_entries)]
            | ("pattern", _) :: rest ->
                ("pattern", `List pattern_entries) :: rest
            | hd :: tl -> hd :: replace tl
          in
          replace base_assoc
    in
    `Assoc (base_assoc @ extras)
  in
  `List (List.mapi enrich intros)

and json_of_ptactic_core core =
  let loc = core.pl_loc in
  let desc = core.pl_desc in
  let node, args, children =
    match desc with
    | Pidtac msg ->
        ("Pidtac", [("message", json_of_string_option msg)], [])
    | Pdo (repeat, t) ->
        ("Pdo", [("repeat", json_of_trepeat repeat)], [json_of_ptactic_core t])
    | Ptry t ->
        ("Ptry", [], [json_of_ptactic_core t])
    | Pby None ->
        ("Pby", [("script", `Null)], [])
    | Pby (Some ts) ->
        ("Pby", [("script", json_of_ptactics ts)], [])
    | Psolve (depth, bases) ->
        ("Psolve",
         [ ("depth", json_of_int_option depth);
           ("bases", json_of_option json_of_psymbol_list bases) ],
         [])
    | Por (t1, t2) ->
        ("Por", [], [json_of_ptactic t1; json_of_ptactic t2])
    | Pseq ts ->
        ("Pseq", [], List.map json_of_ptactic ts)
    | Pcase (b, opts, info) ->
        ("Pcase",
         [ ("by_eq", `Bool b);
           ("options", json_of_pcaseoptions opts);
           ("focus", json_of_prevertv info) ],
         [])
    | Plogic tac ->
        ("Plogic", [("tactic", json_of_logtactic tac)], [])
    | PPhl tac ->
        ("PPhl", [("tactic", json_of_phltactic tac)], [])
    | Pprogress (opts, next) ->
        ("Pprogress",
         [("options", json_of_ppgoptions opts)],
         match next with
         | None   -> []
         | Some t -> [json_of_ptactic_core t])
    | Psubgoal chain ->
        ("Psubgoal", [("chain", json_of_ptactic_chain chain)], [])
    | Pnstrict t ->
        ("Pnstrict", [], [json_of_ptactic_core t])
    | Padmit ->
        ("Padmit", [], [])
  in
  let base = [
    ("node"   , `String node);
    ("source" , json_of_source loc);
    ("args"   , `Assoc args);
  ] in
  let base =
    if children = [] then base
    else base @ [("children", `List children)]
  in
  `Assoc base

and json_of_ptactic_chain = function
  | Psubtacs ts ->
      `Assoc [
        ("kind"   , `String "Psubtacs");
        ("tactics", json_of_ptactics ts);
      ]
  | Pfsubtacs (ts, fallback) ->
      let entries =
        List.map
          (fun (focus, tac) ->
             `Assoc [
               ("focus" , json_of_tfocus focus);
               ("tactic", json_of_ptactic tac);
             ])
          ts
      in
      `Assoc [
        ("kind"    , `String "Pfsubtacs");
        ("targets" , `List entries);
        ("fallback", json_of_option json_of_ptactic fallback);
      ]
  | Pfirst (tac, count) ->
      `Assoc [
        ("kind"  , `String "Pfirst");
        ("count" , `Int count);
        ("tactic", json_of_ptactic tac);
      ]
  | Plast (tac, count) ->
      `Assoc [
        ("kind"  , `String "Plast");
        ("count" , `Int count);
        ("tactic", json_of_ptactic tac);
      ]
  | Pexpect (expect, n) ->
      `Assoc [
        ("kind"   , `String "Pexpect");
        ("goals"  , `Int n);
        ("expect" , json_of_pexpect expect);
      ]
  | Pfocus (tac, focus) ->
      `Assoc [
        ("kind"  , `String "Pfocus");
        ("focus" , json_of_tfocus focus);
        ("tactic", json_of_ptactic tac);
      ]
  | Protate (dir, n) ->
      let dir =
        match dir with
        | `Left  -> "left"
        | `Right -> "right"
      in
      `Assoc [
        ("kind" , `String "Protate");
        ("dir"  , `String dir);
        ("count", `Int n);
      ]

and json_of_pexpect = function
  | `None ->
      `Assoc [("kind", `String "None")]
  | `Tactic t ->
      `Assoc [
        ("kind"  , `String "Tactic");
        ("tactic", json_of_ptactic t);
      ]
  | `Chain chains ->
      `Assoc [
        ("kind"  , `String "Chain");
        ("chains", json_of_list json_of_ptactic_chain (unloc chains));
      ]

let () = json_of_ptactics_ref := json_of_ptactics

(* -------------------------------------------------------------------- *)
let record_clone ~theory ~base ~target =
  if not !enabled then
    ()
  else
    let loc = theory.pthc_base.pl_loc in
    if EcLocation.isdummy loc then
      ()
    else if not (matches_target_file loc.loc_fname) then
      ()
    else
      let entry = {
        clone_data        = theory;
        clone_base_path   = base;
        clone_target_path = target;
      } in
      clones := entry :: !clones

(* -------------------------------------------------------------------- *)
let block_loc tactics =
  let merge acc t =
    let loc = t.pt_core.pl_loc in
    if EcLocation.isdummy loc then acc
    else
      match acc with
      | None   -> Some loc
      | Some l -> Some (EcLocation.merge l loc)
  in
  List.fold_left merge None tactics

let ensure_entry lemma lemma_name lemma_path =
  match Hashtbl.find_opt lemmas lemma with
  | Some entry ->
      (match lemma_name, entry.name with
       | Some name, None -> entry.name <- Some name
       | Some name, Some _ -> entry.name <- Some name
       | _ -> ());
      if lemma_path <> "" then entry.path <- lemma_path;
      entry
  | None ->
      let entry = {
        lemma;
        name   = lemma_name;
        path   = lemma_path;
        blocks = [];
        status = `Pending;
      } in
      Hashtbl.add lemmas lemma entry;
      lemma_order := lemma :: !lemma_order;
      entry

let record_block ~lemma ~lemma_name ~lemma_path ~tactics =
  if not !enabled then
    ()
  else
    match block_loc tactics with
    | None -> ()
    | Some loc when not (matches_target_file loc.loc_fname) -> ()
    | Some loc ->
        let entry = ensure_entry lemma lemma_name lemma_path in
        (match !current_lemma with
         | Some cur when cur == lemma -> ()
         | _ ->
             current_lemma := Some lemma;
             reset_goal_indices ());
        let index = List.length entry.blocks in
        let block = { index; loc = Some loc; tactics } in
        entry.blocks <- entry.blocks @ [block]

let mark_status ~lemma ~lemma_name ~lemma_path ~status =
  match Hashtbl.find_opt lemmas lemma with
  | None -> ()
  | Some entry ->
      (match lemma_name, entry.name with
       | Some name, None -> entry.name <- Some name
       | _ -> ());
      if lemma_path <> "" then entry.path <- lemma_path;
      entry.status <- (status :> lemma_status);
      (match !current_lemma with
       | Some cur when cur == lemma -> current_lemma := None
       | _ -> ())

let string_of_status = function
  | `Pending  -> "pending"
  | `Qed      -> "qed"
  | `Admitted -> "admitted"
  | `Aborted  -> "aborted"

let json_of_block block =
  `Assoc [
    ("index"  , `Int block.index);
    ("source" , json_of_option json_of_source block.loc);
    ("tactics", json_of_ptactics block.tactics);
  ]

(* -------------------------------------------------------------------- *)
let json_of_pqsymbol_located qs =
  json_of_located
    ~extra:[("value", `String (EcSymbols.string_of_qsymbol (unloc qs)))]
    qs

let json_of_clone_locality = function
  | None -> `Null
  | Some `Local -> `String "local"
  | Some `Global -> `String "global"

let json_of_clone_import = function
  | None -> `Null
  | Some `Import -> `String "import"
  | Some `Export -> `String "export"
  | Some `Include -> `String "include"

let json_of_clone_option (enabled, opt) =
  let name =
    match opt with
    | `Abstract -> "abstract"
  in
  `Assoc [
    ("enabled", `Bool enabled);
    ("option" , `String name);
  ]

let json_of_clone_options opts =
  `List (List.map json_of_clone_option opts)

let json_of_clmode = function
  | `Alias -> `String "alias"
  | `Inline `Keep -> `String "inline-keep"
  | `Inline `Clear -> `String "inline-clear"

let json_of_genoverride json_of_syntax = function
  | `ByPath path ->
      `Assoc [
        ("kind", `String "by-path");
        ("path", `String (EcPath.tostring path));
      ]
  | `BySyntax v ->
      `Assoc [
        ("kind" , `String "by-syntax");
        ("value", json_of_syntax v);
      ]

let json_of_ty_override_def (params, body) =
  `Assoc [
    ("params", json_of_psymbol_list params);
    ("body"  , json_of_located body);
  ]

let json_of_ty_override (override, mode) =
  `Assoc [
    ("mode" , json_of_clmode mode);
    ("value", json_of_genoverride json_of_ty_override_def override);
  ]

let json_of_op_override_def ov =
  `Assoc [
    ("tyvars", json_of_option json_of_psymbol_list ov.opov_tyvars);
    ("args"  , json_of_ptybindings ov.opov_args);
    ("return", json_of_located ov.opov_retty);
    ("body"  , json_of_pformula ov.opov_body);
  ]

let json_of_pr_override_def ov =
  `Assoc [
    ("tyvars", json_of_option json_of_psymbol_list ov.prov_tyvars);
    ("args"  , json_of_ptybindings ov.prov_args);
    ("body"  , json_of_pformula ov.prov_body);
  ]

let json_of_simple_override (qs, mode) =
  `Assoc [
    ("symbol", json_of_pqsymbol_located qs);
    ("mode"  , json_of_clmode mode);
  ]

let json_of_theory_override = function
  | PTHO_Type ov ->
      `Assoc [
        ("kind" , `String "type");
        ("value", json_of_ty_override ov);
      ]
  | PTHO_Op (override, mode) ->
      `Assoc [
        ("kind" , `String "op");
        ("mode" , json_of_clmode mode);
        ("value", json_of_genoverride json_of_op_override_def override);
      ]
  | PTHO_Pred (override, mode) ->
      `Assoc [
        ("kind" , `String "pred");
        ("mode" , json_of_clmode mode);
        ("value", json_of_genoverride json_of_pr_override_def override);
      ]
  | PTHO_Axiom ov ->
      `Assoc [
        ("kind" , `String "axiom");
        ("value", json_of_simple_override ov);
      ]
  | PTHO_ModTyp ov ->
      `Assoc [
        ("kind" , `String "module-type");
        ("value", json_of_simple_override ov);
      ]
  | PTHO_Theory ov ->
      `Assoc [
        ("kind" , `String "theory");
        ("value", json_of_simple_override ov);
      ]

let json_of_clone_proof_tag (action, sym) =
  let action =
    match action with
    | `Include -> "include"
    | `Exclude -> "exclude"
  in
  `Assoc [
    ("action", `String action);
    ("name"  , json_of_psymbol sym);
  ]

let json_of_clone_proof proof =
  let base_fields =
    match proof.pthp_mode with
    | `All (name, tags) ->
        let fields = [
          ("kind" , `String "all");
          ("tags" , json_of_list json_of_clone_proof_tag tags);
        ] in
        begin
          match name with
          | None -> fields
          | Some qs -> ("name", json_of_pqsymbol_located qs) :: fields
        end
    | `Named (name, mode) ->
        [
          ("kind" , `String "named");
          ("name" , json_of_pqsymbol_located name);
          ("mode" , json_of_clmode mode);
        ]
  in
  let tactic_field =
    match proof.pthp_tactic with
    | None -> []
    | Some core -> [("tactic", json_of_ptactic_core core)]
  in
  `Assoc (base_fields @ tactic_field)

let json_of_clone_renaming_kind = function
  | `Lemma   -> "lemma"
  | `Op      -> "op"
  | `Pred    -> "pred"
  | `Type    -> "type"
  | `Module  -> "module"
  | `ModType -> "module-type"
  | `Theory  -> "theory"

let json_of_clone_renaming (kinds, (src, dst)) =
  `Assoc [
    ("kinds", `List (List.map (fun k -> `String (json_of_clone_renaming_kind k)) kinds));
    ("from" , json_of_located_string src);
    ("to"   , json_of_located_string dst);
  ]

let json_of_clone_clear (`Abbrev, qs) =
  `Assoc [
    ("kind", `String "abbrev");
    ("name", json_of_pqsymbol_located qs);
  ]

let json_of_clone_override (qs, ov) =
  `Assoc [
    ("symbol"  , json_of_pqsymbol_located qs);
    ("override", json_of_theory_override ov);
  ]

let json_of_clone_entry entry =
  let data = entry.clone_data in
  `Assoc [
    ("base"       , json_of_pqsymbol_located data.pthc_base);
    ("alias"      , json_of_osymbol_r data.pthc_name);
    ("base_path"  , `String entry.clone_base_path);
    ("target_path", `String entry.clone_target_path);
    ("import"     , json_of_clone_import data.pthc_import);
    ("locality"   , json_of_clone_locality data.pthc_local);
    ("options"    , json_of_clone_options data.pthc_opts);
    ("overrides"  , json_of_list json_of_clone_override data.pthc_ext);
    ("proofs"     , json_of_list json_of_clone_proof data.pthc_prf);
    ("renames"    , json_of_list json_of_clone_renaming data.pthc_rnm);
    ("clears"     , json_of_list json_of_clone_clear data.pthc_clears);
    ("source"     , json_of_source data.pthc_base.pl_loc);
  ]

(* -------------------------------------------------------------------- *)
let starts_with prefix s =
  let lp = String.length prefix in
  String.length s >= lp && String.sub s 0 lp = prefix

let rec drop_local_prefix s =
  let trimmed = String.trim s in
  if starts_with "local " trimmed then
    let rest = String.sub trimmed 6 (String.length trimmed - 6) in
    drop_local_prefix rest
  else
    trimmed

let is_ident_char = function
  | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' -> true
  | _ -> false

let extract_decl_name block =
  match block.loc with
  | None -> None
  | Some loc ->
      match snippet_of_loc loc with
      | None -> None
      | Some text ->
          let text = drop_local_prefix text in
          if starts_with "lemma" text then
            let rest =
              String.sub text 5 (String.length text - 5) |> String.trim in
            let len = String.length rest in
            let rec find i =
              if i < len && is_ident_char rest.[i] then find (i + 1) else i in
            let stop = find 0 in
            if stop = 0 then None else Some (String.sub rest 0 stop)
          else
            None

let reindex_blocks blocks =
  List.mapi (fun i block -> { block with index = i }) blocks

let rec consume_foreign name acc = function
  | block :: rest when extract_decl_name block = Some name ->
      consume_foreign name (block :: acc) rest
  | rest ->
      (List.rev acc, rest)

let partition_foreign_blocks entry blocks =
  let rec aux acc extras = function
    | [] ->
        (List.rev acc |> reindex_blocks, List.rev extras)
    | block :: rest ->
        (match entry.name, extract_decl_name block with
         | Some entry_name, Some foreign when foreign <> entry_name ->
             let taken, rest' = consume_foreign foreign [block] rest in
             let extras =
               (foreign, reindex_blocks taken) :: extras
             in
             aux acc extras rest'
         | _ ->
             aux (block :: acc) extras rest)
  in
  aux [] [] blocks

let build_path base current_name target_name =
  match current_name with
  | Some _ ->
      (match String.rindex_opt base '.' with
       | None -> target_name
       | Some idx ->
           let prefix = String.sub base 0 (idx + 1) in
           prefix ^ target_name)
  | None -> base

let json_entry ~name ~path ~status ~blocks =
  `Assoc [
    ("name"  , json_of_string_option name);
    ("path"  , `String path);
    ("status", `String (string_of_status status));
    ("blocks", `List (List.map json_of_block blocks));
  ]

let json_of_entry entry =
  let blocks =
    entry.blocks
    |> List.sort (fun b1 b2 -> Int.compare b1.index b2.index)
  in
  let kept, extras = partition_foreign_blocks entry blocks in
  let extra_jsons =
    List.map
      (fun (name, blocks) ->
         json_entry
           ~name:(Some name)
           ~path:(build_path entry.path entry.name name)
           ~status:entry.status
           ~blocks)
      extras
  in
  let current =
    json_entry
      ~name:entry.name
      ~path:entry.path
      ~status:entry.status
      ~blocks:kept
  in
  extra_jsons @ [current]

let finalize () =
  if not !enabled then
    ()
  else
    match !current_source with
    | None -> ()
    | Some source ->
        let clones_json =
          !clones
          |> List.rev
          |> List.map json_of_clone_entry
        in
        let lemmas_json =
          !lemma_order
          |> List.rev
          |> List.filter_map (fun ax -> Hashtbl.find_opt lemmas ax)
          |> List.map json_of_entry
          |> List.concat
        in
        let payload =
          `Assoc [
            ("file"  , `String source);
            ("clones", `List clones_json);
            ("lemmas", `List lemmas_json);
          ]
        in
        let outfile = proofast_filename source in
        let oc = open_out_bin outfile in
        EcUtils.try_finally
          (fun () ->
             Yojson.Basic.pretty_to_channel oc payload;
             output_char oc '\n')
          (fun () -> close_out oc)
