(* -------------------------------------------------------------------- *)
open EcUtils
open EcLocation
open EcSymbols
open EcParsetree

module P = EcParser
module L = Lexing
module I = EcParser.MenhirInterpreter

(* -------------------------------------------------------------------- *)
type reader = {
  lexbuf  : L.lexbuf;
  mutable tokens : P.token list;
}

let reader_of_string (data : string) : reader =
  { lexbuf = L.from_string data; tokens = []; }

let lexer ?(checkpoint : _ I.checkpoint option) (r : reader) =
  if List.is_empty r.tokens then
    r.tokens <- EcLexer.main r.lexbuf;

  let token, queue = List.destruct r.tokens in
  let token, prequeue =
    match checkpoint, token with
    | Some checkpoint, P.DECIMAL (pre, (_, post)) ->
        if I.acceptable checkpoint token r.lexbuf.lex_curr_p then
          token, []
        else
          List.destruct P.[UINT pre; DOT; UINT post]
    | _ ->
        token, []
  in

  r.tokens <- prequeue @ queue;
  (token, L.lexeme_start_p r.lexbuf, L.lexeme_end_p r.lexbuf)

let ensure_trailing_dot (data : string) =
  let data = String.trim data in
  let len = String.length data in
  if len > 0 && data.[len - 1] = '.' then data else data ^ "."

let parse_tactics_from_string (data : string) : ptactics =
  let data = ensure_trailing_dot data in
  let reader = EcIo.from_string data in
  let globals =
    try EcIo.parseall reader
    with e ->
      EcIo.finalize reader;
      raise e
  in
  EcIo.finalize reader;
  List.fold_left
    (fun acc g ->
      match unloc g.gl_action with
      | Gtactics (`Actual ts) -> acc @ ts
      | Gtactics `Proof -> acc
      | _ -> acc)
    [] globals

(* -------------------------------------------------------------------- *)
module SSet = Ssym

let add_sym (s : string) (acc : SSet.t) =
  SSet.add s acc

let add_psymbol (s : psymbol) (acc : SSet.t) =
  add_sym (unloc s) acc

let add_qsymbol (s : pqsymbol) (acc : SSet.t) =
  add_sym (string_of_qsymbol (unloc s)) acc

let rec add_pmsymbol_r (s : pmsymbol) (acc : SSet.t) =
  match s with
  | [] -> acc
  | (x, None) :: tl ->
      add_pmsymbol_r tl (add_psymbol x acc)
  | (x, Some args) :: tl ->
      let acc = add_psymbol x acc in
      let acc = List.fold_left (fun acc ms -> add_pmsymbol ms acc) acc args in
      add_pmsymbol_r tl acc

and add_pmsymbol (s : pmsymbol located) (acc : SSet.t) =
  add_pmsymbol_r (unloc s) acc

let add_pmsymbol_path (s : pmsymbol) (acc : SSet.t) =
  let rec collect acc = function
    | [] -> acc
    | (x, _) :: tl -> collect (unloc x :: acc) tl
  in
  match collect [] s with
  | [] -> acc
  | x :: xs ->
      let q = (xs, x) in
      add_sym (string_of_qsymbol q) acc

let add_option f (acc : SSet.t) = function
  | None -> acc
  | Some v -> f v acc

let add_doption f (acc : SSet.t) = function
  | Single v -> f v acc
  | Double (v1, v2) -> acc |> f v1 |> f v2

let add_list f (acc : SSet.t) xs =
  List.fold_left (fun acc x -> f x acc) acc xs

(* -------------------------------------------------------------------- *)
let add_bound_psymbol (bound : SSet.t) (s : psymbol) =
  SSet.add (unloc s) bound

let add_bound_osymbol (bound : SSet.t) (s : osymbol) =
  match unloc s with
  | None -> bound
  | Some s -> add_bound_psymbol bound s

let add_bound_osymbols (bound : SSet.t) (xs : osymbol list) =
  List.fold_left add_bound_osymbol bound xs

let add_bound_ptybindings (bound : SSet.t) (bs : ptybindings) =
  List.fold_left (fun b (xs, _) -> add_bound_osymbols b xs) bound bs

let add_bound_pgtybindings (bound : SSet.t) (bs : pgtybindings) =
  List.fold_left (fun b (xs, _) -> add_bound_osymbols b xs) bound bs

let add_bound_plpattern (bound : SSet.t) (p : plpattern) =
  match unloc p with
  | LPSymbol s -> add_bound_psymbol bound s
  | LPTuple xs -> add_bound_osymbols bound xs
  | LPRecord xs ->
      List.fold_left (fun b (_, s) -> add_bound_psymbol b s) bound xs

let add_bound_ppattern (bound : SSet.t) (p : ppattern) =
  match p with
  | PPApp (_, xs) -> add_bound_osymbols bound xs

let is_bound_qsymbol (bound : SSet.t) (q : pqsymbol) =
  match unloc q with
  | ([], x) -> SSet.mem x bound
  | _ -> false

let rec names_of_pformula_bound (bound : SSet.t) (f : pformula) (acc : SSet.t) : SSet.t =
  match unloc f with
  | PFhole
  | PFint _
  | PFdecimal _ ->
      acc

  | PFident (x, _) ->
      if is_bound_qsymbol bound x then acc else add_qsymbol x acc

  | PFref (x, _) | PFmem x ->
      if SSet.mem (unloc x) bound then acc else add_psymbol x acc

  | PFglob ms ->
      add_pmsymbol ms acc

  | PFcast (f, _) ->
      names_of_pformula_bound bound f acc

  | PFtuple fs ->
      add_list (names_of_pformula_bound bound) acc fs

  | PFapp (f, args) ->
      let acc = names_of_pformula_bound bound f acc in
      add_list (names_of_pformula_bound bound) acc args

  | PFif (f1, f2, f3) ->
      acc
      |> names_of_pformula_bound bound f1
      |> names_of_pformula_bound bound f2
      |> names_of_pformula_bound bound f3

  | PFmatch (f, branches) ->
      let acc = names_of_pformula_bound bound f acc in
      add_list
        (fun (p, f) acc ->
          let bound = add_bound_ppattern bound p in
          names_of_pformula_bound bound f acc)
        acc branches

  | PFlet (p, (f, _), body) ->
      let acc = names_of_pformula_bound bound f acc in
      let bound = add_bound_plpattern bound p in
      names_of_pformula_bound bound body acc

  | PFforall (bs, f)
  | PFexists (bs, f) ->
      let bound = add_bound_pgtybindings bound bs in
      names_of_pformula_bound bound f acc

  | PFlambda (bs, f) ->
      let bound = add_bound_ptybindings bound bs in
      names_of_pformula_bound bound f acc

  | PFrecord (base, fields) ->
      let acc = add_option (names_of_pformula_bound bound) acc base in
      add_list (fun rf acc -> names_of_pformula_bound bound rf.rf_value acc) acc fields

  | PFproj (f, p) ->
      acc |> names_of_pformula_bound bound f |> add_qsymbol p

  | PFproji (f, _) ->
      names_of_pformula_bound bound f acc

  | PFside (f, (_, s)) ->
      acc |> names_of_pformula_bound bound f |> add_psymbol s

  | PFeqveq (gvs, mods) ->
      let acc =
        add_list (fun gv acc ->
          match gv with
          | GVglob (m, qs) ->
              let acc = add_pmsymbol m acc in
              add_list add_qsymbol acc qs
          | GVvar q ->
              if is_bound_qsymbol bound q then acc else add_qsymbol q acc) acc gvs
      in
      add_option (fun (l, r) acc -> acc |> add_pmsymbol_r l |> add_pmsymbol_r r) acc mods

  | PFeqf fs ->
      add_list (names_of_pformula_bound bound) acc fs

  | PFlsless gp ->
      names_of_pgamepath gp acc

  | PFscope (p, f) ->
      acc |> add_qsymbol p |> names_of_pformula_bound bound f

  | PFhoareF (p, gp, q) ->
      acc |> names_of_pformula_bound bound p |> names_of_pgamepath gp |> names_of_pformula_bound bound q

  | PFehoareF (p, gp, q) ->
      acc |> names_of_pformula_bound bound p |> names_of_pgamepath gp |> names_of_pformula_bound bound q

  | PFequivF (p, (g1, g2), q) ->
      acc
      |> names_of_pformula_bound bound p
      |> names_of_pgamepath g1
      |> names_of_pgamepath g2
      |> names_of_pformula_bound bound q

  | PFeagerF (p, (s1, g1, g2, s2), q) ->
      acc
      |> names_of_pformula_bound bound p
      |> names_of_pstmt s1
      |> names_of_pgamepath g1
      |> names_of_pgamepath g2
      |> names_of_pstmt s2
      |> names_of_pformula_bound bound q

  | PFprob (gp, fs, mem, f) ->
      let acc = names_of_pgamepath gp acc in
      let acc = add_list (names_of_pformula_bound bound) acc fs in
      acc |> add_psymbol mem |> names_of_pformula_bound bound f

  | PFBDhoareF (p, gp, q, _, r) ->
      acc
      |> names_of_pformula_bound bound p
      |> names_of_pgamepath gp
      |> names_of_pformula_bound bound q
      |> names_of_pformula_bound bound r

and names_of_pformula (f : pformula) (acc : SSet.t) : SSet.t =
  names_of_pformula_bound SSet.empty f acc

and names_of_pexpr (e : pexpr) (acc : SSet.t) : SSet.t =
  match unloc e with
  | Expr f -> names_of_pformula f acc

and names_of_pgamepath (p : pgamepath) (acc : SSet.t) =
  let (mods, _) = unloc p in
  add_pmsymbol_path mods acc

and names_of_pstmt (s : pstmt) (acc : SSet.t) =
  let names_of_pinstr (i : pinstr) (acc : SSet.t) =
    match unloc i with
    | PSident x ->
        add_psymbol x acc
    | PSasgn (lv, e)
    | PSrnd (lv, e) ->
        let acc = names_of_plvalue lv acc in
        names_of_pexpr e acc
    | PScall (lv, p, args) ->
        let acc = add_option names_of_plvalue acc lv in
        let acc = names_of_pgamepath p acc in
        add_list names_of_pexpr acc (unloc args)
    | PSif ((c, t), elseifs, el) ->
        let acc = names_of_pexpr c acc in
        let acc = names_of_pstmt t acc in
        let acc = add_list (fun (c, b) acc -> names_of_pexpr c acc |> names_of_pstmt b) acc elseifs in
        names_of_pstmt el acc
    | PSwhile (c, body) ->
        names_of_pexpr c acc |> names_of_pstmt body
    | PSmatch (e, cases) ->
        let acc = names_of_pexpr e acc in
        (match cases with
         | `Full xs -> add_list (fun (_, b) acc -> names_of_pstmt b acc) acc xs
         | `If ((_, b1), b2) ->
             let acc = names_of_pstmt b1 acc in
             add_option names_of_pstmt acc b2)
    | PSassert e ->
        names_of_pexpr e acc
  in
  add_list names_of_pinstr acc s

and names_of_plvalue (lv : plvalue) (acc : SSet.t) =
  match unloc lv with
  | PLvSymbol p -> add_qsymbol p acc
  | PLvTuple ps -> add_list add_qsymbol acc ps
  | PLvMap (p, _, _, es) ->
      let acc = add_qsymbol p acc in
      add_list names_of_pexpr acc es

let rec names_of_ppterm (t : ppterm) (acc : SSet.t) : SSet.t =
  let acc =
    match t.fp_head with
    | FPNamed (x, _) -> add_qsymbol x acc
    | FPCut None -> acc
    | FPCut (Some f) -> names_of_pformula f acc
  in
  add_list names_of_ppt_arg acc t.fp_args

and names_of_ppt_arg (a : ppt_arg located) (acc : SSet.t) : SSet.t =
  match unloc a with
  | EA_none
  | EA_tactic _ ->
      acc
  | EA_form f ->
      names_of_pformula f acc
  | EA_mem m ->
      add_psymbol m acc
  | EA_mod m ->
      add_pmsymbol m acc
  | EA_proof p ->
      names_of_ppterm p acc

let names_of_gppterm_with_head
  (names_of_head : 'a ppt_head -> SSet.t -> SSet.t)
  (t : 'a gppterm)
  (acc : SSet.t)
 =
  let acc = names_of_head t.fp_head acc in
  add_list names_of_ppt_arg acc t.fp_args

let names_of_tuple2_ppterm (t : pformula option tuple2 gppterm) (acc : SSet.t) =
  let names_of_head = function
    | FPNamed (x, _) -> add_qsymbol x
    | FPCut (f1, f2) ->
        fun acc ->
          let acc = add_option names_of_pformula acc f1 in
          add_option names_of_pformula acc f2
  in
  names_of_gppterm_with_head names_of_head t acc

let names_of_call_info (ci : call_info) (acc : SSet.t) =
  match ci with
  | CI_spec (f1, f2) ->
      acc |> names_of_pformula f1 |> names_of_pformula f2
  | CI_inv f ->
      names_of_pformula f acc
  | CI_upto (f1, f2, f3) ->
      let acc = acc |> names_of_pformula f1 |> names_of_pformula f2 in
      add_option names_of_pformula acc f3

let names_of_call_gppterm (t : call_info gppterm) (acc : SSet.t) =
  let names_of_head = function
    | FPNamed (x, _) -> add_qsymbol x
    | FPCut ci -> names_of_call_info ci
  in
  names_of_gppterm_with_head names_of_head t acc

(* -------------------------------------------------------------------- *)
let names_of_genpattern (gp : genpattern) (acc : SSet.t) =
  match gp with
  | `ProofTerm pt ->
      names_of_ppterm pt acc
  | `Form (_, f) ->
      names_of_pformula f acc
  | `LetIn _ ->
      acc

let names_of_prevert (p : prevert) (acc : SSet.t) =
  add_list names_of_genpattern acc p.pr_genp

let names_of_prevertv (p : prevertv) (acc : SSet.t) =
  let acc = add_list names_of_ppterm acc p.pr_view in
  names_of_prevert p.pr_rev acc

let names_of_apply_info (ai : apply_info) (acc : SSet.t) =
  match ai with
  | `ApplyIn (pt, m) ->
      acc |> names_of_ppterm pt |> add_psymbol m
  | `Apply (pts, _) ->
      add_list names_of_ppterm acc pts
  | `Top _ ->
      acc
  | `Alpha pt ->
      names_of_ppterm pt acc
  | `ExactType qt ->
      add_qsymbol qt acc

let names_of_rwoptions (rw : rwoptions) (acc : SSet.t) =
  let (_, _, _, f) = rw in
  add_option names_of_pformula acc f

let names_of_rwarg (rw : rwarg) (acc : SSet.t) =
  let (_, rw1) = rw in
  match unloc rw1 with
  | RWSimpl _
  | RWDone _
  | RWSmt _
  | RWTactic _ ->
      acc
  | RWDelta (opts, f) ->
      acc |> names_of_rwoptions opts |> names_of_pformula f
  | RWRw (opts, rs) ->
      let acc = names_of_rwoptions opts acc in
      add_list (fun (_, pt) acc -> names_of_ppterm pt acc) acc rs
  | RWPr (x, f) ->
      let acc = add_psymbol x acc in
      add_option names_of_pformula acc f
  | RWApp pt ->
      names_of_ppterm pt acc

(* -------------------------------------------------------------------- *)
let names_of_fun_info (fi : fun_info) (acc : SSet.t) =
  match fi with
  | `Def
  | `Code ->
      acc
  | `Abs f ->
      names_of_pformula f acc
  | `Upto (f1, f2, f3) ->
      let acc = acc |> names_of_pformula f1 |> names_of_pformula f2 in
      add_option names_of_pformula acc f3

let names_of_app_info (ai : app_info) (acc : SSet.t) =
  let (_, _, _, f, xt) = ai in
  let acc = add_doption names_of_pformula acc f in
  match xt with
  | PAppNone -> acc
  | PAppSingle f -> names_of_pformula f acc
  | PAppMult (f1, f2, f3, f4, f5) ->
      let acc = add_option names_of_pformula acc f1 in
      let acc = add_option names_of_pformula acc f2 in
      let acc = add_option names_of_pformula acc f3 in
      let acc = add_option names_of_pformula acc f4 in
      add_option names_of_pformula acc f5

let names_of_trans_formula (tf : trans_formula) (acc : SSet.t) =
  match tf with
  | TFform (f1, f2, f3, f4) ->
      acc |> names_of_pformula f1 |> names_of_pformula f2 |> names_of_pformula f3 |> names_of_pformula f4
  | TFeq ->
      acc

let names_of_trans_info (ti : trans_info) (acc : SSet.t) =
  let (k, tf) = ti in
  let acc =
    match k with
    | TKfun p ->
        names_of_pgamepath p acc
    | TKstmt (_, s)
    | TKparsedStmt (_, _, s) ->
        names_of_pstmt s acc
  in
  names_of_trans_formula tf acc

let names_of_pcond_info (ci : pcond_info) (acc : SSet.t) =
  match ci with
  | `Head _ -> acc
  | `Seq (_, _, f) -> names_of_pformula f acc
  | `SeqOne (_, _, f1, f2) -> acc |> names_of_pformula f1 |> names_of_pformula f2

let names_of_while_info (wi : while_info) (acc : SSet.t) =
  let acc = names_of_pformula wi.wh_inv acc in
  let acc = add_option names_of_pformula acc wi.wh_vrnt in
  match wi.wh_bds with
  | None -> acc
  | Some (`Bd (b1, b2)) ->
      acc |> names_of_pformula b1 |> names_of_pformula b2

let names_of_async_while_info (ai : async_while_info) (acc : SSet.t) =
  let (tleft, tright) = ai.asw_test in
  let (t1, t2) = tleft in
  let (t3, t4) = tright in
  let (p1, p2) = ai.asw_pred in
  acc
  |> names_of_pexpr t1
  |> names_of_pformula t2
  |> names_of_pexpr t3
  |> names_of_pformula t4
  |> names_of_pformula p1
  |> names_of_pformula p2
  |> names_of_pformula ai.asw_inv

let names_of_inline_pat1 (ip : inline_pat1) (acc : SSet.t) =
  match ip with
  | `InlineXpath p ->
      names_of_pgamepath p acc
  | `InlinePat (m, (xs, y)) ->
      let acc = add_pmsymbol m acc in
      let acc = add_list add_psymbol acc xs in
      add_option add_psymbol acc y
  | `InlineAll ->
      acc

let names_of_inline_info (ii : inline_info) (acc : SSet.t) =
  match ii with
  | `ByName (_, _, (pats, _)) ->
      add_list (fun (_, p) acc -> names_of_inline_pat1 p acc) acc pats
  | `CodePos _ ->
      acc

let names_of_outline_info (oi : outline_info) (acc : SSet.t) =
  match oi.outline_kind with
  | OKstmt s -> names_of_pstmt s acc
  | OKproc (p, _) -> names_of_pgamepath p acc

let names_of_fel_info (fi : fel_info) (acc : SSet.t) =
  let acc =
    acc
    |> names_of_pformula fi.pfel_cntr
    |> names_of_pformula fi.pfel_asg
    |> names_of_pformula fi.pfel_q
    |> names_of_pformula fi.pfel_event
  in
  let acc = add_option names_of_pformula acc fi.pfel_inv in
  add_list (fun (p, f) acc -> names_of_pgamepath p acc |> names_of_pformula f) acc fi.pfel_specs

let names_of_conseq_ppterm (t : conseq_ppterm) (acc : SSet.t) =
  let names_of_head = function
    | FPNamed (x, _) -> add_qsymbol x
    | FPCut ((f1, f2), cinfo) ->
        fun acc ->
          let acc = add_option names_of_pformula acc f1 in
          let acc = add_option names_of_pformula acc f2 in
          match cinfo with
          | None -> acc
          | Some (CQI_bd (_, f)) -> names_of_pformula f acc
  in
  names_of_gppterm_with_head names_of_head t acc

let names_of_deno_ppterm (t : deno_ppterm) (acc : SSet.t) =
  let names_of_head = function
    | FPNamed (x, _) -> add_qsymbol x
    | FPCut (f1, f2) ->
        fun acc ->
          let acc = add_option names_of_pformula acc f1 in
          add_option names_of_pformula acc f2
  in
  names_of_gppterm_with_head names_of_head t acc

let names_of_sim_info (si : sim_info) (acc : SSet.t) =
  let acc =
    add_list
      (fun ((p1, p2), f) acc ->
        let acc = add_option names_of_pgamepath acc p1 in
        let acc = add_option names_of_pgamepath acc p2 in
        names_of_pformula f acc)
      acc (fst si.sim_hint)
  in
  let acc = add_option names_of_pformula acc (snd si.sim_hint) in
  add_option names_of_pformula acc si.sim_eqs

let names_of_rw_eqv_info (ri : rw_eqv_info) (acc : SSet.t) =
  let acc = names_of_ppterm ri.rw_eqv_lemma acc in
  match ri.rw_eqv_proc with
  | None -> acc
  | Some (es, eo) ->
      let acc = add_list names_of_pexpr acc (unloc es) in
      add_option names_of_pexpr acc eo

let names_of_bdh_split (bs : bdh_split) (acc : SSet.t) =
  match bs with
  | BDH_split_bop (f1, f2, f3) ->
      let acc = acc |> names_of_pformula f1 |> names_of_pformula f2 in
      add_option names_of_pformula acc f3
  | BDH_split_or_case (f1, f2, f3) ->
      acc |> names_of_pformula f1 |> names_of_pformula f2 |> names_of_pformula f3
  | BDH_split_not (f1, f2) ->
      let acc = add_option names_of_pformula acc f1 in
      names_of_pformula f2 acc

(* -------------------------------------------------------------------- *)
let rec names_of_logtactic (t : logtactic) (acc : SSet.t) =
  match t with
  | Preflexivity
  | Passumption
  | Ptrivial
  | Pcongr
  | Pleft
  | Pright ->
      acc
  | Psmt info ->
      let add_hints acc = add_list (fun h acc -> add_qsymbol h.pht_name acc) acc in
      let acc =
        match info.plem_wanted with
        | None -> acc
        | Some xs -> add_hints acc xs
      in
      (match info.plem_unwanted with
       | None -> acc
       | Some xs -> add_hints acc xs)
  | Psplit _
  | Palg_norm ->
      acc
  | Pfield xs
  | Pring xs ->
      add_list add_psymbol acc xs
  | Pexists xs ->
      add_list names_of_ppt_arg acc xs
  | Pelim (_, p) ->
      add_option add_qsymbol acc p
  | Papply (ai, _) ->
      names_of_apply_info ai acc
  | Pcut (_, _, f, tacs) ->
      let acc = names_of_pformula f acc in
      add_option (fun t acc -> names_of_ptactics (unloc t) acc) acc tacs
  | Pcutdef (_, cd) ->
      let acc = add_qsymbol cd.ptcd_name acc in
      add_list names_of_ppt_arg acc cd.ptcd_args
  | Pmove pv ->
      names_of_prevertv pv acc
  | Pclear ci ->
      (match ci with
       | `Exclude xs
       | `Include xs -> add_list add_psymbol acc xs)
  | Prewrite (rws, os) ->
      let acc = add_list names_of_rwarg acc rws in
      add_option add_psymbol acc os
  | Prwnormal (f, xs) ->
      let acc = names_of_pformula f acc in
      add_list add_qsymbol acc xs
  | Psubst fs ->
      add_list names_of_pformula acc fs
  | Psimplify _
  | Pcbv _ ->
      acc
  | Pchange f ->
      names_of_pformula f acc
  | Ppose (x, _, _, f) ->
      acc |> add_psymbol x |> names_of_pformula f
  | Pmemory x ->
      add_psymbol x acc
  | Pgenhave (x, _, ys, f) ->
      let acc = add_psymbol x acc in
      let acc = add_list add_psymbol acc ys in
      names_of_pformula f acc
  | Pwlog (xs, _, f) ->
      let acc = add_list add_psymbol acc xs in
      names_of_pformula f acc
  | Pcoq (_, x, _) ->
      add_psymbol x acc

and names_of_phltactic (t : phltactic) (acc : SSet.t) =
  match t with
  | Pskip
  | Pmatch _
  | Pswap _
  | Pcfold _
  | Pkill _
  | Pasgncase _
  | Prndsem _
  | Pfission _
  | Pfusion _
  | Punroll _
  | Phrex_elim
  | Pexfalso
  | Pbyupto
  | Phoare
  | Pprbounded
  | Psymmetry
  | Peager_if
  | Peager_while _
  | Peager_fun_def
  | Pauto
  | Plossless ->
      acc
  | Prepl_stmt ti
  | Ptrans_stmt ti ->
      names_of_trans_info ti acc
  | Pfun fi ->
      names_of_fun_info fi acc
  | Papp ai ->
      names_of_app_info ai acc
  | Pwp _
  | Psp _ ->
      acc
  | Pwhile (_, wi) ->
      names_of_while_info wi acc
  | Pasyncwhile ai ->
      names_of_async_while_info ai acc
  | Psplitwhile (e, _, _) ->
      names_of_pexpr e acc
  | Pcall (_, pt)
  | Peager_call pt ->
      names_of_call_gppterm pt acc
  | Pcallconcave (f, pt) ->
      acc |> names_of_pformula f |> names_of_call_gppterm pt
  | Prcond _
  | Prmatch _ ->
      acc
  | Pcond ci ->
      names_of_pcond_info ci acc
  | Pinline ii ->
      names_of_inline_info ii acc
  | Poutline oi ->
      names_of_outline_info oi acc
  | Pinterleave _ ->
      acc
  | Pweakmem (_, x, _) ->
      add_psymbol x acc
  | Pset (_, _, _, x, e) ->
      acc |> add_psymbol x |> names_of_pexpr e
  | Psetmatch (_, _, x, f) ->
      acc |> add_psymbol x |> names_of_pformula f
  | Prnd (_, _, info) ->
      (match info with
       | PNoRndParams -> acc
       | PSingleRndParam f -> names_of_pformula f acc
       | PTwoRndParams (f1, f2) -> acc |> names_of_pformula f1 |> names_of_pformula f2
       | PMultRndParams ((f1, f2, f3, f4, f5), f6) ->
           let acc =
             acc
             |> names_of_pformula f1
             |> names_of_pformula f2
             |> names_of_pformula f3
             |> names_of_pformula f4
             |> names_of_pformula f5
           in
           add_option names_of_pformula acc f6)
  | Palias (_, _, os) ->
      add_option add_psymbol acc os
  | Pconseq (_, cs) ->
      let (c1, c2, c3) = cs in
      let acc = add_option names_of_conseq_ppterm acc c1 in
      let acc = add_option names_of_conseq_ppterm acc c2 in
      add_option names_of_conseq_ppterm acc c3
  | Pconseqauto _ ->
      acc
  | Pconcave (pt, f) ->
      acc |> names_of_tuple2_ppterm pt |> names_of_pformula f
  | Phrex_intro (fs, _) ->
      add_list names_of_pformula acc fs
  | Phecall (_, (q, _, fs)) ->
      let acc = add_qsymbol q acc in
      add_list names_of_pformula acc fs
  | Pbydeno (_, (pt, _, f)) ->
      let acc = names_of_deno_ppterm pt acc in
      add_option names_of_pformula acc f
  | PPr fo ->
      add_option (fun (f1, f2) acc -> acc |> names_of_pformula f1 |> names_of_pformula f2) acc fo
  | Pfel (_, fi) ->
      names_of_fel_info fi acc
  | Psim (_, si) ->
      names_of_sim_info si acc
  | Prw_equiv ri ->
      names_of_rw_eqv_info ri acc
  | Pbdhoare_split bs ->
      names_of_bdh_split bs acc
  | Pprocchange (_, _, e) ->
      names_of_pexpr e acc
  | Pprocrewrite (_, _, rw) ->
      (match rw with
       | `Rw pt -> names_of_ppterm pt acc
       | `Simpl -> acc)
  | Peager_seq (_, _, f)
  | Peager_fun_abs (_, f)
  | Peager (_, f) ->
      names_of_pformula f acc
  | Pbd_equiv (_, f1, f2) ->
      acc |> names_of_pformula f1 |> names_of_pformula f2

and names_of_ptactic_core (t : ptactic_core) (acc : SSet.t) : SSet.t =
  match unloc t with
  | Pidtac _ | Padmit -> acc
  | Pdo (_, t)
  | Ptry t
  | Pnstrict t ->
      names_of_ptactic_core t acc
  | Pby None ->
      acc
  | Pby (Some ts)
  | Pseq ts ->
      names_of_ptactics ts acc
  | Psolve (_, xs) ->
      (match xs with
       | None -> acc
       | Some ys -> add_list add_psymbol acc ys)
  | Por (t1, t2) ->
      acc |> names_of_ptactic t1 |> names_of_ptactic t2
  | Pcase (_, _, pv) ->
      names_of_prevertv pv acc
  | Plogic lt ->
      names_of_logtactic lt acc
  | PPhl ht ->
      names_of_phltactic ht acc
  | Pprogress (_, t) ->
      add_option names_of_ptactic_core acc t
  | Psubgoal tc ->
      names_of_ptactic_chain tc acc

and names_of_ptactic_chain (t : ptactic_chain) (acc : SSet.t) =
  match t with
  | Psubtacs ts ->
      names_of_ptactics ts acc
  | Pfsubtacs (ts, te) ->
      let acc = add_list (fun (_, t) acc -> names_of_ptactic t acc) acc ts in
      add_option names_of_ptactic acc te
  | Pfirst (t, _)
  | Plast (t, _)
  | Pfocus (t, _) ->
      names_of_ptactic t acc
  | Pexpect (e, _) ->
      (match e with
       | `None -> acc
       | `Tactic t -> names_of_ptactic t acc
       | `Chain ls ->
           add_list names_of_ptactic_chain acc (unloc ls))
  | Protate _ ->
      acc

and names_of_ptactic (t : ptactic) (acc : SSet.t) =
  (* Skip intro patterns by ignoring pt_intros. *)
  names_of_ptactic_core t.pt_core acc

and names_of_ptactics (ts : ptactics) (acc : SSet.t) =
  add_list names_of_ptactic acc ts

(* -------------------------------------------------------------------- *)
let tactic_names (data : string) : string list =
  let tactics = parse_tactics_from_string data in
  let names = names_of_ptactics tactics SSet.empty in
  let is_ident_segment s =
    match EcIo.lex_single_token s with
    | Some (EcParser.LIDENT _)
    | Some (EcParser.UIDENT _) -> true
    | _ -> false
  in
  let is_qualified_ident s =
    s
    |> String.split_on_char '.'
    |> List.for_all is_ident_segment
  in
  let is_blacklisted = function
    | "true" | "false" -> true
    | _ -> false
  in
  SSet.elements names
  |> List.filter is_qualified_ident
  |> List.filter (fun s -> not (is_blacklisted s))
