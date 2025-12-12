(* -------------------------------------------------------------------- *)
open EcUtils
open EcLocation
open EcSymbols
open EcParsetree
open EcAst
open EcDecl
open EcTypes
open EcFol
open EcEnv
open EcMatching

open EcBaseLogic

open EcProofTerm
open EcCoreGoal
open EcCoreGoal.FApi
open EcLowGoal

module Sid  = EcIdent.Sid
module Mid  = EcIdent.Mid
module Sp   = EcPath.Sp

module ER  = EcReduction
module PT  = EcProofTerm
module TT  = EcTyping
module TTC = EcProofTyping
module LG  = EcCoreLib.CI_Logic

(* -------------------------------------------------------------------- *)
type ttenv = {
  tt_provers   : EcParsetree.pprover_infos option -> EcProvers.prover_infos;
  tt_smtmode   : [`Admit | `Strict | `Sloppy | `Report];
  tt_implicits : bool;
  tt_oldip     : bool;
  tt_redlogic  : bool;
  tt_und_delta : bool;
  (* Optional ProofAst hook: per-rewrite logging callback installed by ecHiTacticals. *)
  tt_logrewrite :
    (int -> string option -> string list -> EcCoreGoal.handle list -> EcCoreGoal.handle list -> unit) option;
  (* Optional ProofAst hook: per-apply logging callback installed by ecHiTacticals. *)
  tt_logapply :
    (int -> string option -> string list -> EcCoreGoal.handle list -> EcCoreGoal.handle list -> unit) option;
}

type engine = ptactic_core -> FApi.backward

(* -------------------------------------------------------------------- *)
let t_simplify_lg ?target ?delta (ttenv, logic) (tc : tcenv1) =
  let logic =
    match logic with
    | `Default -> if ttenv.tt_redlogic then `Full else `ProductCompat
    | `Variant -> if ttenv.tt_redlogic then `ProductCompat else `Full
  in t_simplify ?target ?delta ~logic:(Some logic) tc

(* -------------------------------------------------------------------- *)
type focus_t = EcParsetree.tfocus

let process_tfocus tc (focus : focus_t) : tfocus =
  let count = FApi.tc_count tc in

  let check1 i =
    let error () = tc_error !$tc "invalid focus index: %d" i in
    if   i >= 0
    then if not (0 < i && i <= count) then error () else i-1
    else if -i > count then error () else count+i
  in

  let checkfs fs =
    List.fold_left
      (fun rg (i1, i2) ->
        let i1 = odfl min_int (omap check1 i1) in
        let i2 = odfl max_int (omap check1 i2) in
        if i1 <= i2 then ISet.add_range i1 i2 rg else rg)
      ISet.empty fs
  in

  let posfs = omap checkfs (fst focus) in
  let negfs = omap checkfs (snd focus) in

  fun i ->
       odfl true (posfs |> omap (ISet.mem i))
    && odfl true (negfs |> omap (fun fc -> not (ISet.mem i fc)))

(* -------------------------------------------------------------------- *)
let process_assumption (tc : tcenv1) =
  EcLowGoal.t_assumption `Conv tc

(* -------------------------------------------------------------------- *)
let process_reflexivity (tc : tcenv1) =
  try  EcLowGoal.t_reflex tc
  with InvalidGoalShape ->
    tc_error !!tc "cannot prove goal by reflexivity"

(* -------------------------------------------------------------------- *)
let process_change fp (tc : tcenv1) =
  let fp = TTC.tc1_process_formula tc fp in
  t_change fp tc

(* -------------------------------------------------------------------- *)
let process_simplify_info ri (tc : tcenv1) =
  let env, hyps, _ = FApi.tc1_eflat tc in

  let do1 (sop, sid) ps =
    match ps.pl_desc with
    | ([], s) when LDecl.has_name s hyps ->
        let id = fst (LDecl.by_name s hyps) in
        (sop, Sid.add id sid)

    | qs ->
        match EcEnv.Op.lookup_opt qs env with
        | None   -> tc_lookup_error !!tc ~loc:ps.pl_loc `Operator qs
        | Some p -> (Sp.add (fst p) sop, sid)
  in

  let delta_p, delta_h =
    ri.pdelta
      |> omap (List.fold_left do1 (Sp.empty, Sid.empty))
      |> omap (fun (x, y) -> (fun p -> if Sp.mem p x then `Force else `IfApplied), (Sid.mem^~ y))
      |> odfl ((fun _ -> `IfTransparent), predT)
  in

  {
    EcReduction.beta    = ri.pbeta;
    EcReduction.delta_p = delta_p;
    EcReduction.delta_h = delta_h;
    EcReduction.zeta    = ri.pzeta;
    EcReduction.iota    = ri.piota;
    EcReduction.eta     = ri.peta;
    EcReduction.logic   = if ri.plogic then Some `Full else None;
    EcReduction.modpath = ri.pmodpath;
    EcReduction.user    = ri.puser;
  }

(*-------------------------------------------------------------------- *)
let process_simplify ri (tc : tcenv1) =
  t_simplify_with_info (process_simplify_info ri tc) tc

(* -------------------------------------------------------------------- *)
let process_cbv ri (tc : tcenv1) =
  t_cbv_with_info (process_simplify_info ri tc) tc

(* -------------------------------------------------------------------- *)
let process_smt ?loc (ttenv : ttenv) pi (tc : tcenv1) =
  let pi = ttenv.tt_provers pi in

  match ttenv.tt_smtmode with
  | `Admit ->
      t_admit tc

  | (`Sloppy | `Strict) as mode ->
      t_seq (t_simplify ~delta:`No) (t_smt ~mode pi) tc

  | `Report ->
      t_seq (t_simplify ~delta:`No) (t_smt ~mode:(`Report loc) pi) tc

(* -------------------------------------------------------------------- *)

let process_coq ~loc ~name (ttenv : ttenv) coqmode  pi (tc : tcenv1) =
  let pi = ttenv.tt_provers (Some pi) in

  match ttenv.tt_smtmode with
  | `Admit ->
    t_admit tc

  | (`Sloppy | `Strict) as mode ->
    t_seq (t_simplify ~delta:`No) (t_coq ~loc ~name ~mode coqmode pi) tc

  | `Report ->
    t_seq (t_simplify ~delta:`No) (t_coq ~loc ~name ~mode:(`Report (Some loc)) coqmode pi) tc

(* -------------------------------------------------------------------- *)
let process_clear (info : clear_info) tc =
  let hyps = FApi.tc1_hyps tc in
  let toid s =
    if not (LDecl.has_name (unloc s) hyps) then
      tc_lookup_error !!tc ~loc:s.pl_loc `Local ([], unloc s);
    fst (LDecl.by_name (unloc s) hyps)
  in
  match info with
  | `Include symbols -> begin
    try  t_clears (List.map toid symbols) tc
    with (ClearError _) as err -> tc_error_exn !!tc err
  end
  | `Exclude symbols -> 
    let excluded = List.map toid symbols in
    let hyp_ids = List.map fst (LDecl.tohyps hyps).h_local in
    let clear_list = List.filter (fun x -> not (List.mem x excluded)) hyp_ids in
    t_clears ~leniant:true clear_list tc

(* -------------------------------------------------------------------- *)
let process_algebra mode kind eqs (tc : tcenv1) =
  let (env, hyps, concl) = FApi.tc1_eflat tc in

  if not (EcAlgTactic.is_module_loaded env) then
    tacuerror "ring/field cannot be used when AlgTactic is not loaded";

  let (ty, f1, f2) =
    match sform_of_form concl with
    | SFeq (f1, f2) -> (f1.f_ty, f1, f2)
    | _ -> tacuerror "conclusion must be an equation"
  in

  let eqs =
    let eq1 { pl_desc = x } =
      match LDecl.hyp_exists x hyps with
      | false -> tacuerror "cannot find equation referenced by `%s'" x
      | true  -> begin
        match sform_of_form (snd (LDecl.hyp_by_name x hyps)) with
        | SFeq (f1, f2) ->
            if not (EcReduction.EqTest.for_type env ty f1.f_ty) then
              tacuerror "assumption `%s' is not an equation over the right type" x;
            (f1, f2)
        | _ -> tacuerror "assumption `%s' is not an equation" x
      end
    in List.map eq1 eqs
  in

  let tparams = (LDecl.tohyps hyps).h_tvar in

  let tactic =
    match
      match mode, kind with
      | `Simpl, `Ring  -> `Ring  EcAlgTactic.t_ring_simplify
      | `Simpl, `Field -> `Field EcAlgTactic.t_field_simplify
      | `Solve, `Ring  -> `Ring  EcAlgTactic.t_ring
      | `Solve, `Field -> `Field EcAlgTactic.t_field
    with
    | `Ring t ->
        let r =
          match TT.get_ring (tparams, ty) env with
          | None   -> tacuerror "cannot find a ring structure"
          | Some r -> r
        in t r eqs (f1, f2)
    | `Field t ->
        let r =
          match TT.get_field (tparams, ty) env with
          | None   -> tacuerror "cannot find a field structure"
          | Some r -> r
        in t r eqs (f1, f2)
  in

  tactic tc

(* -------------------------------------------------------------------- *)
let t_apply_prept pt tc =
  EcLowGoal.Apply.t_apply_bwd_r (pt_of_prept tc pt) tc

(* -------------------------------------------------------------------- *)
module LowRewrite = struct
  type error =
  | LRW_NotAnEquation
  | LRW_NothingToRewrite
  | LRW_InvalidOccurence
  | LRW_CannotInfer
  | LRW_IdRewriting
  | LRW_RPatternNoMatch
  | LRW_RPatternNoRuleMatch

  exception RewriteError of error

  let rec find_rewrite_patterns ~inpred (dir : rwside) pt =
    let hyps = pt.PT.ptev_env.PT.pte_hy in
    let env  = LDecl.toenv hyps in
    let pt   = { pt with ptev_ax = snd (PT.concretize pt) } in
    let ptc  = { pt with ptev_env = EcProofTerm.copy pt.ptev_env } in
    let ax   = pt.ptev_ax in

    let base ax =
      match EcFol.sform_of_form ax with
      | EcFol.SFeq  (f1, f2) -> [(pt, `Eq, (f1, f2))]
      | EcFol.SFiff (f1, f2) -> [(pt, `Eq, (f1, f2))]

      | EcFol.SFnot f ->
          let pt' = pt_of_global_r pt.ptev_env LG.p_negeqF [] in
          let pt' = apply_pterm_to_arg_r pt' (PVAFormula f) in
          let pt' = apply_pterm_to_arg_r pt' (PVASub pt) in
          [(pt', `Eq, (f, f_false))]

      | _ -> []

    and split ax =
      match EcFol.sform_of_form ax with
      | EcFol.SFand (`Sym, (f1, f2)) ->
         let pt1 =
           let pt'= pt_of_global_r pt.ptev_env LG.p_and_proj_l [] in
           let pt'= apply_pterm_to_arg_r pt' (PVAFormula f1) in
           let pt'= apply_pterm_to_arg_r pt' (PVAFormula f2) in
           apply_pterm_to_arg_r pt' (PVASub pt) in

         let pt2 =
           let pt'= pt_of_global_r pt.ptev_env LG.p_and_proj_r [] in
           let pt'= apply_pterm_to_arg_r pt' (PVAFormula f1) in
           let pt'= apply_pterm_to_arg_r pt' (PVAFormula f2) in
           apply_pterm_to_arg_r pt' (PVASub pt) in

           (find_rewrite_patterns ~inpred dir pt2)
         @ (find_rewrite_patterns ~inpred dir pt1)

      | _ -> []
    in

    match base ax with
    | _::_ as rws -> rws

    | [] -> begin
      let ptb = Lazy.from_fun (fun () ->
        let pt1 = split ax
        and pt2 =
          if dir = `LtoR then
            if   ER.EqTest.for_type env ax.f_ty tbool
            then Some (ptc, `Bool, (ax, f_true))
            else None
          else None
        and pt3 = omap base
          (EcReduction.h_red_opt EcReduction.full_red hyps ax)
        in pt1 @ (otolist pt2) @ (odfl [] pt3)) in

        let rec doit reduce =
          match TTC.destruct_product ~reduce hyps ax with
          | None -> begin
             if reduce then Lazy.force ptb else
               let pts = doit true in
               if inpred then pts else (Lazy.force ptb) @ pts
            end

          | Some _ ->
             let pt = EcProofTerm.apply_pterm_to_hole pt in
             find_rewrite_patterns ~inpred:(inpred || reduce) dir pt

        in doit false
      end

  let find_rewrite_patterns = find_rewrite_patterns ~inpred:false

  type rwinfos = rwside * EcFol.form option * EcMatching.occ option

  let t_rewrite_r ?(mode = `Full) ?target ((s, prw, o) : rwinfos) pt tc =
    let hyps, tgfp = FApi.tc1_flat ?target tc in

    let modes =
      match mode with
      | `Full  -> [{ k_keyed = true; k_conv = false };
                   { k_keyed = true; k_conv =  true };]
      | `Light -> [{ k_keyed = true; k_conv = false }] in

    let for1 (pt, mode, (f1, f2)) =
      let fp, tp = match s with `LtoR -> f1, f2 | `RtoL -> f2, f1 in
      let subf, occmode =
        match prw with
        | None -> begin
           try
             PT.pf_find_occurence_lazy pt.PT.ptev_env ~modes ~ptn:fp tgfp
           with
           | PT.FindOccFailure `MatchFailure ->
               raise (RewriteError LRW_NothingToRewrite)
           | PT.FindOccFailure `IncompleteMatch ->
               raise (RewriteError LRW_CannotInfer)
          end

        | Some prw -> begin
           let prw, _ =
             try
               PT.pf_find_occurence_lazy
                 pt.PT.ptev_env ~full:false ~modes ~ptn:prw tgfp
             with PT.FindOccFailure `MatchFailure ->
                 raise (RewriteError LRW_RPatternNoMatch) in

           try
             PT.pf_find_occurence_lazy
               pt.PT.ptev_env ~rooted:true ~modes ~ptn:fp prw
           with
           | PT.FindOccFailure `MatchFailure ->
              raise (RewriteError LRW_RPatternNoRuleMatch)
           | PT.FindOccFailure `IncompleteMatch ->
               raise (RewriteError LRW_CannotInfer)
          end in

      if not occmode.k_keyed then begin
        let tp = PT.concretize_form pt.PT.ptev_env tp in
        if EcReduction.is_conv hyps fp tp then
          raise (RewriteError LRW_IdRewriting);
      end;

      let pt = fst (PT.concretize pt) in
      let cpos =
        try  FPosition.select_form
               ~xconv:`AlphaEq ~keyed:occmode.k_keyed
               hyps o subf tgfp
        with InvalidOccurence -> raise (RewriteError (LRW_InvalidOccurence))
      in

      EcLowGoal.t_rewrite
        ~keyed:occmode.k_keyed ?target ~mode pt (s, Some cpos) tc in

    let rec do_first = function
      | [] -> raise (RewriteError LRW_NothingToRewrite)

      | (pt, mode, (f1, f2)) :: pts ->
           try  for1 (pt, mode, (f1, f2))
           with RewriteError _ ->
             do_first pts
    in

    let pts = find_rewrite_patterns s pt in

    if List.is_empty pts then
      raise (RewriteError LRW_NotAnEquation);
    do_first (List.rev pts)

  let t_rewrite ?target (s, p, o) pt (tc : tcenv1) =
    let hyps   = FApi.tc1_hyps ?target tc in
    let pt, ax = EcLowGoal.LowApply.check `Elim pt (`Hyps (hyps, !!tc)) in
    let ptenv  = ptenv_of_penv hyps !!tc in

    t_rewrite_r ?target (s, p, o)
      { ptev_env = ptenv; ptev_pt = pt; ptev_ax = ax; }
      tc

  let t_autorewrite lemmas (tc : tcenv1) =
    let pts =
      let do1 lemma =
        PT.pt_of_uglobal !!tc (FApi.tc1_hyps tc) lemma in
      List.map do1 lemmas
    in

    let try1 pt tc =
      let pt = { pt with PT.ptev_env = PT.copy pt.ptev_env } in
        try  t_rewrite_r (`LtoR, None, None) pt tc
        with RewriteError _ -> raise InvalidGoalShape
    in t_do_r ~focus:0 `Maybe None (t_ors (List.map try1 pts)) !@tc
end

let t_rewrite_prept info pt tc =
  LowRewrite.t_rewrite_r info (pt_of_prept tc pt) tc

(* -------------------------------------------------------------------- *)
(* Logging of the fully-qualified rewrite rule used during execution (for ProofAst).
   Lifecycle: enabled when ecHiTacticals installs a log_rewrite; buffers are
   cleared per rewrite argument, populated during rule discovery/application,
   then drained into ProofAst at the end of that argument. *)
let rewrite_paths : string list ref = ref []
let rewrite_last_path : string option ref = ref None
let rewrite_logging_active = ref false

let clear_rewrite_paths () =
  (* Reset per-argument rewrite buffers. No-op when logging is disabled. *)
  if !rewrite_logging_active then begin
    rewrite_paths := [];
    rewrite_last_path := None
  end

(* Build a path from string segments. Used by alias resolution helpers below. *)
let path_of_segments = function
  | [] -> invalid_arg "empty path"
  | hd :: tl ->
      List.fold_left (fun acc x -> EcPath.pqname acc x) (EcPath.psymbol hd) tl

(* Replace an alias prefix using the theory alias map.
   Example: if A is an alias for Top.Lib, and we see A.f, rewrite it to Top.Lib.f. *)
let dealias_path env p =
  let aliases = EcEnv.Theory.aliases env in
  let target = EcPath.tolist p in
  let rec prefix a b =
    match a, b with
    | [], _ -> true
    | x :: xs, y :: ys when String.equal x y -> prefix xs ys
    | _ -> false
  in
  let module MP = EcPath.Mp in
  MP.fold
    (fun real alias acc ->
       match acc with
       | Some _ -> acc
       | None ->
           let alias_l = EcPath.tolist alias in
           if prefix alias_l target then
             let real_l = EcPath.tolist real in
             let rest = List.drop (List.length alias_l) target in
             Some (path_of_segments (real_l @ rest))
           else None)
    aliases None
  |> odfl p

(* Canonicalize module path representations into a uniform EcPath.path. *)
let path_of_mpath mp =
  match mp.EcPath.m_top with
  | `Concrete (p, None) -> p
  | `Concrete (p, Some sub) -> EcPath.pappend p sub
  | `Local id -> EcPath.psymbol (EcIdent.tostring id)

(* Strip known aliases from a path, yielding the real module-qualified path. *)
let strip_alias env p =
  let module MP = EcPath.Mp in
  let aliases = EcEnv.Theory.aliases env in
  let target = EcPath.tolist p in
  let rec prefix a b =
    match a, b with
    | [], _ -> true
    | x :: xs, y :: ys when String.equal x y -> prefix xs ys
    | _ -> false
  in
  MP.fold
    (fun real alias acc ->
       match acc with
       | Some _ -> acc
       | None ->
           let alias_l = EcPath.tolist alias in
           if prefix alias_l target then
             let real_l = EcPath.tolist real in
             let rest = List.drop (List.length alias_l) target in
             Some (path_of_segments (real_l @ rest))
           else None)
    aliases None

(* Given a possibly-aliased/instantiated axiom path, enumerate all original
   definitions that are alpha-eq and parameter-compatible. Used to populate
   resolved_paths for ProofAst. *)
let find_original_axiom_paths env p =
  match Ax.by_path_opt p env with
  | None -> [p]
  | Some ref_ax ->
      let params_match params =
        List.length params = List.length ref_ax.ax_tparams
        && List.for_all2
             (fun (_, tc1) (_, tc2) -> Sp.equal tc1 tc2)
             ref_ax.ax_tparams params in

      let specs_match cand_ax =
        try
          let tv =
            List.fold_left2
              (fun tv (ref_id, _) (cand_id, _) ->
                 Mid.add cand_id (tvar ref_id) tv)
              Mid.empty ref_ax.ax_tparams cand_ax.ax_tparams in
          let subst = EcCoreSubst.Fsubst.f_subst_init ~tv () in
          let cand_spec = EcCoreSubst.Fsubst.f_subst subst cand_ax.ax_spec in
          let hyps = EcEnv.LDecl.init env ref_ax.ax_tparams in
          ER.is_alpha_eq hyps ref_ax.ax_spec cand_spec
        with _ -> false in

      let paths =
        Ax.all env
        |> List.filter (fun (_, cand_ax) ->
               cand_ax.ax_kind = ref_ax.ax_kind
            && params_match cand_ax.ax_tparams
            && specs_match cand_ax)
        |> List.map fst
        |> List.sort_uniq EcPath.p_compare
      in
      if paths = [] then [p] else paths

let normalize_paths env p =
  (* Normalize a candidate rule path: expand aliases, reattach module path,
     stringify, and deduplicate. This is what ProofAst emits as resolved_paths. *)
  find_original_axiom_paths env p
  |> List.map (fun p ->
         let base = EcPath.basename p in
         let module_path =
           match EcPath.prefix p with
           | None -> None
           | Some prefix ->
               let mp = EcPath.mpath_crt prefix [] None in
               let mp = EcEnv.NormMp.norm_mpath env mp in
               Some (path_of_mpath mp)
         in
         let p_norm =
           match module_path with
           | None -> p
           | Some mp -> EcPath.pqname mp base
         in
         let p_norm = dealias_path env p_norm in
         EcPath.tostring p_norm)
  |> List.sort_uniq String.compare

let record_rewrite_path env path =
  (* Record every rule path encountered while rewrite logging is active so
     ProofAst can emit resolved_paths/chosen_path in the JSON. *)
  if !rewrite_logging_active then
    let ps = normalize_paths env path in
    ps
    |> List.filter (fun p -> p <> "")
    |> List.iter (fun p ->
         rewrite_paths := p :: !rewrite_paths;
         rewrite_last_path := Some p)

let take_rewrite_paths_and_chosen () =
  (* Flush buffered rewrite paths and the last chosen rule for the current
     rewrite argument; used right after each rewrite application. *)
  if not !rewrite_logging_active then ([], None)
  else begin
    let paths =
      !rewrite_paths
      |> List.rev
      |> List.sort_uniq String.compare
    in
    let chosen = !rewrite_last_path in
    rewrite_paths := [];
    rewrite_last_path := None;
    (paths, chosen)
  end

let record_rewrite_proofterm env (pt : PT.pt_ev) =
  (* If the rewrite came from a proof term, extract its head/global and record
     it as a rule used, so ProofAst can still attribute the rewrite. *)
  let rec from_head = function
    | PTGlobal (p, _) -> Some p
    | PTTerm pt       -> from_term pt
    | _               -> None
  and from_term = function
    | PTApply { pt_head; _ } -> from_head pt_head
    | PTQuant (_, pt)        -> from_term pt
  in
  match from_term pt.ptev_pt with
  | Some p -> record_rewrite_path env p
  | None   -> ()

let apply_paths : string list ref = ref []
let apply_last_path : string option ref = ref None
let apply_logging_active = ref false

let clear_apply_paths () =
  if !apply_logging_active then begin
    apply_paths := [];
    apply_last_path := None
  end

let record_apply_path env path =
  if !apply_logging_active then
    let ps = normalize_paths env path in
    ps
    |> List.filter (fun p -> p <> "")
    |> List.iter (fun p ->
           apply_paths := p :: !apply_paths;
           apply_last_path := Some p)

let take_apply_paths_and_chosen () =
  if not !apply_logging_active then ([], None)
  else begin
    let paths =
      !apply_paths
      |> List.rev
      |> List.sort_uniq String.compare
    in
    let chosen = !apply_last_path in
    apply_paths := [];
    apply_last_path := None;
    (paths, chosen)
  end

let record_apply_proofterm env (pt : PT.pt_ev) =
  let rec from_head = function
    | PTGlobal (p, _) -> Some p
    | PTTerm pt       -> from_term pt
    | _               -> None
  and from_term = function
    | PTApply { pt_head; _ } -> from_head pt_head
    | PTQuant (_, pt)        -> from_term pt
  in
  match from_term pt.ptev_pt with
  | Some p -> record_apply_path env p
  | None   -> ()

(* -------------------------------------------------------------------- *)
let process_solve ?bases ?depth (tc : tcenv1) =
  match FApi.t_try_base (EcLowGoal.t_solve ~canfail:false ?bases ?depth) tc with
  | `Failure _ ->
      tc_error (FApi.tc1_penv tc) "[solve]: cannot close goal"
  | `Success tc ->
      tc

(* -------------------------------------------------------------------- *)
let process_trivial (tc : tcenv1) =
  EcPhlAuto.t_pl_trivial ~conv:`Conv tc

(* -------------------------------------------------------------------- *)
let process_crushmode d =
  d.cm_simplify, if d.cm_solve then Some process_trivial else None

(* -------------------------------------------------------------------- *)
let process_done tc =
  let tc = process_trivial tc in

  if not (FApi.tc_done tc) then
    tc_error (FApi.tc_penv tc) "[by]: cannot close goals";
  tc

(* -------------------------------------------------------------------- *)
let process_apply_bwd ~implicits mode (ff : ppterm) (tc : tcenv1) =
  let pt = PT.tc1_process_full_pterm ~implicits tc ff in

  try
    match mode with
    | `Alpha ->
        begin try
          PT.pf_form_match
            pt.ptev_env
            ~mode:fmrigid
            ~ptn:pt.ptev_ax
            (FApi.tc1_goal tc)
        with EcMatching.MatchFailure ->
          tc_error !!tc "@[<v>proof-term is not alpha-convertible to conclusion@ @[%a@]@]"
              (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv (EcEnv.LDecl.toenv pt.ptev_env.pte_hy))) pt.ptev_ax
        end;
        let aout = EcLowGoal.t_apply (fst (PT.concretize pt)) tc in
        record_apply_proofterm (FApi.tc1_env tc) pt;
        aout
    | `Apply ->
        let aout = EcLowGoal.Apply.t_apply_bwd_r pt tc in
        record_apply_proofterm (FApi.tc1_env tc) pt;
        aout
    | `Exact ->
        let aout = EcLowGoal.Apply.t_apply_bwd_r pt tc in
        record_apply_proofterm (FApi.tc1_env tc) pt;
        let aout = FApi.t_onall process_trivial aout in
        if not (FApi.tc_done aout) then
          tc_error !!tc "cannot close goal";
        aout

  with (EcLowGoal.Apply.NoInstance _) as err ->
    tc_error_exn !!tc err

(* -------------------------------------------------------------------- *)
let process_exacttype qs (tc : tcenv1) =
  let env, hyps, _ = FApi.tc1_eflat tc in
  let p =
    try EcEnv.Ax.lookup_path (EcLocation.unloc qs) env
    with LookupFailure cause ->
      tc_error !!tc "%a" EcEnv.pp_lookup_failure cause
  in
  let tys =
    List.map (fun (a,_) -> EcTypes.tvar a)
      (EcEnv.LDecl.tohyps hyps).h_tvar in
  let pt = ptglobal ~tys p in

  try
    let tc' = EcLowGoal.t_apply pt tc in
    record_apply_path (FApi.tc_env tc') p;
    tc'
  with InvalidGoalShape ->
    let ppe = EcPrinting.PPEnv.ofenv env in
    tc_error !!tc "cannot apply %a@." (EcPrinting.pp_axname ppe) p

(* -------------------------------------------------------------------- *)
let process_apply_fwd ~implicits (pe, hyp) tc =
  let module E = struct exception NoInstance end in

  let hyps = FApi.tc1_hyps tc in

  if not (LDecl.hyp_exists (unloc hyp) hyps) then
    tc_error !!tc "unknown hypothesis: %s" (unloc hyp);

  let hyp, fp = LDecl.hyp_by_name (unloc hyp) hyps in
  let pte = PT.tc1_process_full_pterm ~implicits tc pe in

  try
    let rec instantiate pte =
      match TTC.destruct_product hyps pte.PT.ptev_ax with
      | None -> raise E.NoInstance

      | Some (`Forall _) ->
          instantiate (PT.apply_pterm_to_hole pte)

      | Some (`Imp (f1, f2)) ->
          try
            PT.pf_form_match ~mode:fmdelta pte.PT.ptev_env ~ptn:f1 fp;
            (pte, f2)
          with MatchFailure -> raise E.NoInstance
    in

    let (pte, cutf) = instantiate pte in

    if not (PT.can_concretize pte.ptev_env) then
      tc_error !!tc "cannot infer all variables";

    let pt = fst (PT.concretize pte) in
    let pt = EcCoreGoal.ptapply pt [palocal hyp] in
    let cutf = PT.concretize_form pte.PT.ptev_env cutf in

    let tc' =
      FApi.t_last
        (FApi.t_seq (t_clear hyp) (t_intros_i [hyp]))
        (t_cutdef pt cutf tc)
    in
    record_apply_proofterm (FApi.tc_env tc') pte;
    tc'

  with E.NoInstance ->
    tc_error_lazy !!tc
      (fun fmt ->
        let ppe = EcPrinting.PPEnv.ofenv (FApi.tc1_env tc) in
        Format.fprintf fmt
          "cannot apply (in %a) the given proof-term for:\n\n%!"
          (EcPrinting.pp_local ppe) hyp;
        Format.fprintf fmt
          "  @[%a@]" (EcPrinting.pp_form ppe) pte.PT.ptev_ax)

(* -------------------------------------------------------------------- *)
let process_apply_top tc =
  let hyps, concl = FApi.tc1_flat tc in

  match TTC.destruct_product hyps concl with
  | Some (`Imp _) -> begin
     let h = LDecl.fresh_id hyps "h" in

     try
       EcLowGoal.t_intros_i_seq ~clear:true [h]
         (EcLowGoal.Apply.t_apply_bwd (ptlocal h) )
         tc
     with (EcLowGoal.Apply.NoInstance _) as err ->
       tc_error_exn !!tc err
    end

  | _ -> tc_error !!tc "no top assumption"

(* -------------------------------------------------------------------- *)
let process_rewrite1_core ?mode ?(close = true) ?target (s, p, o) pt tc =
  let o = norm_rwocc o in

  try
    let tc = LowRewrite.t_rewrite_r ?mode ?target (s, p, o) pt tc in
    let cl = fun tc ->
      if EcFol.f_equal f_true (FApi.tc1_goal tc) then
        t_true tc
      else t_id tc
    in if close then FApi.t_last cl tc else tc
  with
  | LowRewrite.RewriteError e ->
      match e with
      | LowRewrite.LRW_NotAnEquation ->
          tc_error !!tc "not an equation to rewrite"
      | LowRewrite.LRW_NothingToRewrite ->
          tc_error !!tc "nothing to rewrite"
      | LowRewrite.LRW_InvalidOccurence ->
          tc_error !!tc "invalid occurence selector"
      | LowRewrite.LRW_CannotInfer ->
          tc_error !!tc "cannot infer all placeholders"
      | LowRewrite.LRW_IdRewriting ->
          tc_error !!tc "refuse to perform an identity rewriting"
      | LowRewrite.LRW_RPatternNoMatch ->
          tc_error !!tc "r-pattern does not match the goal"
      | LowRewrite.LRW_RPatternNoRuleMatch ->
          tc_error !!tc "r-pattern does not match the rewriting rule"

(* -------------------------------------------------------------------- *)
let process_delta ~und_delta ?target (s, o, p) tc =
  let env, hyps, concl = FApi.tc1_eflat tc in
  let o = norm_rwocc o in

  let idtg, target =
    match target with
    | None   -> (None, concl)
    | Some h -> fst_map some (LDecl.hyp_by_name (unloc h) hyps)
  in

  match unloc p with
  | PFident ({ pl_desc = ([], x) }, None)
      when s = `LtoR && EcUtils.is_none o ->

    let check_op = fun p -> if sym_equal (EcPath.basename p) x then `Force else `No in
    let check_id = fun y -> sym_equal (EcIdent.name y) x in
    let ri =
      { EcReduction.no_red with
          EcReduction.delta_p = check_op;
          EcReduction.delta_h = check_id; } in
    let redform = EcReduction.simplify ri hyps target in

    if und_delta then begin
      if EcFol.f_equal target redform then
        EcEnv.notify env `Warning "unused unfold: /%s" x
    end;

    t_change ~ri:{ ri with eta = true; beta = true; } ?target:idtg redform tc

  | _ ->

  (* Continue with matching based unfolding *)
  let (ptenv, p) =
    let (ps, ue), p = TTC.tc1_process_pattern tc p in
    let ev = MEV.of_idents (Mid.keys ps) `Form in
      (ptenv !!tc hyps (ue, ev), p)
  in

  let (tvi, tparams, body, args, dp) =
    match sform_of_form p with
    | SFop (p, args) -> begin
        let op = EcEnv.Op.by_path (fst p) env in

        match op.EcDecl.op_kind with
        | EcDecl.OB_oper (Some (EcDecl.OP_Plain f)) ->
            (snd p, op.EcDecl.op_tparams, f, args, Some (fst p))
        | EcDecl.OB_pred (Some (EcDecl.PR_Plain f)) ->
            (snd p, op.EcDecl.op_tparams, f, args, Some (fst p))
        | _ ->
            tc_error !!tc "the operator cannot be unfolded"
    end

    | SFlocal x when LDecl.can_unfold x hyps ->
        ([], [], LDecl.unfold x hyps, [], None)

    | SFother { f_node = Fapp ({ f_node = Flocal x }, args) }
        when LDecl.can_unfold x hyps ->
        ([], [], LDecl.unfold x hyps, args, None)

    | _ -> tc_error !!tc "not headed by an operator/predicate"

  in

  let ri = { EcReduction.full_red with
               delta_p = (fun p -> if Some p = dp then `Force else `IfTransparent)} in
  let na = List.length args in

  match s with
  | `LtoR -> begin
    let matches =
      try  ignore (PT.pf_find_occurence ptenv ~ptn:p target); true
      with PT.FindOccFailure _ -> false
    in

    if matches then begin
      let p    = concretize_form ptenv p in
      let cpos =
        let test = fun _ fp ->
          let fp =
            match fp.f_node with
            | Fapp (h, hargs) when List.length hargs > na ->
                let (a1, a2) = List.takedrop na hargs in
                  f_app h a1 (toarrow (List.map f_ty a2) fp.f_ty)
            | _ -> fp
          in
            if   EcReduction.is_alpha_eq hyps p fp
            then `Accept (-1)
            else `Continue
        in
          try  FPosition.select ?o test target
          with InvalidOccurence ->
            tc_error !!tc "invalid occurences selector"
      in

      let target =
        FPosition.map cpos
          (fun topfp ->
            let (fp, args) = EcFol.destr_app topfp in

            match sform_of_form fp with
            | SFop ((_, tvi), []) -> begin
              (* FIXME: TC HOOK *)
              let body  = Tvar.f_subst ~freshen:true (List.map fst tparams) tvi body in
              let body  = f_app body args topfp.f_ty in
                try  EcReduction.h_red EcReduction.beta_red hyps body
                with EcEnv.NotReducible -> body
            end

            | SFlocal _ -> begin
                assert (tparams = []);
                let body = f_app body args topfp.f_ty in
                  try  EcReduction.h_red EcReduction.beta_red hyps body
                  with EcEnv.NotReducible -> body
            end

            | _ -> assert false)
          target
      in
        t_change ~ri ?target:idtg target tc
    end else t_id tc
  end

  | `RtoL ->
    let fp =
      (* FIXME: TC HOOK *)
      let body  = Tvar.f_subst ~freshen:true (List.map fst tparams) tvi body in
      let fp    = f_app body args p.f_ty in
        try  EcReduction.h_red EcReduction.beta_red hyps fp
        with EcEnv.NotReducible -> fp
    in

    let matches =
      try  ignore (PT.pf_find_occurence ptenv ~ptn:fp target); true
      with PT.FindOccFailure _ -> false
    in

    if matches then begin
      let p    = concretize_form ptenv p  in
      let fp   = concretize_form ptenv fp in
      let cpos =
        try  FPosition.select_form hyps o fp target
        with InvalidOccurence ->
          tc_error !!tc "invalid occurences selector"
      in

      let target = FPosition.map cpos (fun _ -> p) target in
      t_change ~ri ?target:idtg target tc
    end else t_id tc

(* -------------------------------------------------------------------- *)
let process_rewrite1_r ttenv ?target ri tc =
  let implicits = ttenv.tt_implicits in
  let und_delta = ttenv.tt_und_delta in

  match unloc ri with
  | RWDone simpl ->
      (* `/=` or `/~=` final simplification; optional logic controls reduction. *)
      let tt =
        match simpl with
        | Some logic ->
           let hyps   = FApi.tc1_hyps tc in
           let target = target |> omap (fst |- LDecl.hyp_by_name^~ hyps |- unloc) in
           t_simplify_lg ?target ~delta:`IfApplied (ttenv, logic)
        | None -> t_id
      in FApi.t_seq tt process_trivial tc

  | RWSimpl logic ->
      (* Plain simplify (no “done”): run logical reduction, then continue. *)
      let hyps   = FApi.tc1_hyps tc in
      let target = target |> omap (fst |- LDecl.hyp_by_name^~ hyps |- unloc) in
      t_simplify_lg ?target ~delta:`IfApplied (ttenv, logic) tc

  | RWDelta ((s, r, o, px), p) -> begin
      if Option.is_some px then
        tc_error !!tc "cannot use pattern selection in delta-rewrite rules";

      (* Delta-rewrite (unfold) with optional repeat spec r. *)
      let do1 tc = process_delta ~und_delta ?target (s, o, p) tc in

      match r with
      | None -> do1 tc
      | Some (b, n) -> t_do b n do1 tc
  end

  | RWRw (((s : rwside), r, o, p), pts) -> begin
      (* Main rewrite: over a list of proof terms [pts], maybe with pattern p,
         occurrence o, side s, repeat r, and sub-direction subs per proof term. *)
      let do1 (mode : [`Full | `Light]) ((subs : rwside), pt) tc =
        let hyps   = FApi.tc1_hyps tc in
        let target = target |> omap (fst |- LDecl.hyp_by_name^~ hyps |- unloc) in
        let hyps   = FApi.tc1_hyps ?target tc in

        let ptenv, prw =
          match p with
          | None ->
              PT.ptenv_of_penv hyps !!tc, None

          | Some p ->
              let (ps, ue), p = TTC.tc1_process_pattern tc p in
              let ev = MEV.of_idents (Mid.keys ps) `Form in
              (PT.ptenv !!tc hyps (ue, ev), Some p) in

        let theside =
          match s, subs with
          | `LtoR, _     -> (subs  :> rwside)
          | _    , `LtoR -> (s     :> rwside)
          | `RtoL, `RtoL -> (`LtoR :> rwside) in

        let is_baserw p =
          EcEnv.BaseRw.is_base p.pl_desc (FApi.tc1_env tc) in

        match pt with
        | { fp_head = FPNamed (p, None); fp_args = []; }
              when pt.fp_mode = `Implicit && is_baserw p
        ->
          (* Implicit base-rewrite: expand to all lemmas registered in base. *)
          let env = FApi.tc1_env tc in
          let ls  = snd (EcEnv.BaseRw.lookup p.pl_desc env) in
          let ls  = EcPath.Sp.elements ls in

          let do1 lemma tc =
            let pt = PT.pt_of_uglobal_r (PT.copy ptenv) lemma in
            let tc = process_rewrite1_core ~mode ?target (theside, prw, o) pt tc in
            let env = FApi.tc_env tc in
            (* Track which base rewrite lemma was applied (for ProofAst). *)
            record_rewrite_path env lemma;
            tc
          in t_ors (List.map do1 ls) tc

        | { fp_head = FPNamed (p, None); fp_args = []; }
              when pt.fp_mode = `Implicit
        ->
          (* Implicit named lemma: either expand all lemmas with that name or
             use the provided proof term head if not a bare global. *)
          let env    = FApi.tc1_env tc in
          let ptenv0 = PT.copy ptenv in
          let pt     = PT.process_full_pterm ~implicits ptenv pt
          in

          begin
            match pt.ptev_pt with
            | PTApply { pt_head = PTGlobal _; pt_args = [] } ->
              (* Expand to all axioms matching the given name. *)
              let ls = EcEnv.Ax.all ~name:(unloc p) env in

              let do1 (lemma, _) tc =
                let pt = PT.pt_of_uglobal_r (PT.copy ptenv0) lemma in
                let tc =
                  process_rewrite1_core ~mode ?target (theside, prw, o) pt tc
                in
                (* Track which candidate lemma actually rewrote the goal.
                   record_rewrite_path is used when we know the concrete lemma path. *)
                record_rewrite_path env lemma;
                tc in
              t_ors (List.map do1 ls) tc

            | _ ->
              (* Generic proof term rewrite (not a bare global). *)
              let tc =
                process_rewrite1_core ~mode ?target (theside, prw, o) pt tc in
              (* Rewrite driven by a proof term: log its head for ProofAst.
                 record_rewrite_proofterm is used when we only have a proof term
                 and need to extract a global head, not a named lemma path. *)
              record_rewrite_proofterm env pt;
              tc
          end

        | { fp_head = FPCut (Some f); fp_args = []; }
        ->
          (* Rewrite via a cut pattern: build a PTCut proof term and apply. *)
          let ps = ref Mid.empty in

          let f =
            EcTyping.trans_pattern
              (LDecl.toenv ptenv.pte_hy) ps ptenv.pte_ue
              f
          in

          !ps |> Mid.iter (fun x _ ->
            ptenv.pte_ev := MEV.add x `Form !(ptenv.pte_ev)
          );

          let pt = PTApply { pt_head = PTCut (f, None); pt_args = []; } in
          let pt = { ptev_env = ptenv; ptev_pt = pt; ptev_ax = f; } in

          let tc = process_rewrite1_core ~mode ?target (theside, prw, o) pt tc in
          let env = FApi.tc_env tc in
          (* Cut-based rewrite proof term: record its head for ProofAst. *)
          record_rewrite_proofterm env pt;
          tc

        | _ ->
          (* Fully processed proof term: just apply and log head for ProofAst. *)
          let pt = PT.process_full_pterm ~implicits ptenv pt in
          let tc = process_rewrite1_core ~mode ?target (theside, prw, o) pt tc in
          let env = FApi.tc_env tc in
          (* Here too, we only have a proof term, so extract/log via record_rewrite_proofterm. *)
          record_rewrite_proofterm env pt;
          tc
        in

      let doall mode tc = t_ors (List.map (do1 mode) pts) tc in

      match r with
      | None ->
          doall `Full tc
      | Some (`Maybe, None) ->
          t_seq
            (t_do `Maybe (Some 1) (doall `Full))
            (t_do `Maybe None (doall `Light))
            tc
      | Some (b, n) ->
          t_do b n (doall `Full) tc
  end

  | RWPr (x, f) -> begin
      (* Probabilistic rewrite Pr[...] — only on main goal, not hypotheses. *)
      if EcUtils.is_some target then
        tc_error !!tc "cannot rewrite Pr[] in local assumptions";
      EcPhlPrRw.t_pr_rewrite (unloc x, f) tc
  end

  | RWSmt (false, info) ->
     (* SMT-based rewrite; info carries solver config. *)
     process_smt ~loc:ri.pl_loc ttenv (Some info) tc

  | RWSmt (true, info) ->
     (* SMT with /done variant: try done first, else SMT. *)
     t_or process_done (process_smt ~loc:ri.pl_loc ttenv (Some info)) tc

  | RWApp fp -> begin
      (* Apply a proof term as a rewrite (backward/forward depending on target). *)
      let implicits = ttenv.tt_implicits in
      match target with
      | None -> process_apply_bwd ~implicits `Apply fp tc
      | Some target -> process_apply_fwd ~implicits (fp, target) tc
    end

  | RWTactic `Ring ->
      (* Algebraic ring rewrite/solve. *)
      process_algebra `Solve `Ring [] tc

  | RWTactic `Field ->
      (* Algebraic field rewrite/solve. *)
      process_algebra `Solve `Field [] tc

(* -------------------------------------------------------------------- *)
let process_rewrite1 ttenv ?target ri tc =
  EcCoreGoal.reloc (loc ri) (process_rewrite1_r ttenv ?target ri) tc

(* -------------------------------------------------------------------- *)
let process_rewrite ttenv ?target ?log_rewrite ri tc =
  (* ri: list of rewrite items (ri is a list; we fold over it below).
     ttenv: tactic env carrying implicits and the rewrite logger (if any).
     target: optional focus hypothesis to rewrite instead of the goal.
     log_rewrite: optional ProofAst callback installed by ecHiTacticals.
     tc: current proof state (tcenv), which holds open goals and environment. *)
  let do1 tc gi (fc, ri) =
    (* gi: global index of the current rewrite item in the list.
       fc: optional focus selector (where to apply this rewrite across goals).
       ngoals: number of current open goals in this tcenv. *)
    let ngoals = FApi.tc_count tc in
    let with_logging before process =
      (* logging: enable only if a callback was provided by ecHiTacticals. *)
      let logging = Option.is_some log_rewrite in
      (* Preserve previous flag so nested/other rewrites restore state. *)
      let old_flag = !rewrite_logging_active in
      rewrite_logging_active := logging;
      EcUtils.try_finally
        (fun () ->
           (* Enable per-argument buffers, run the rewrite under test. *)
           if logging then clear_rewrite_paths ();
           let tc' = process () in
           (* Drain buffers: all rule paths seen + last chosen rule. *)
           let paths, chosen =
             if logging then take_rewrite_paths_and_chosen () else ([], None)
           in
           (* If a callback exists, report this argument’s data + goal trace. *)
           (match log_rewrite with
            | Some f ->
                let after_goal = FApi.tc_opened tc' in
                f gi chosen paths before after_goal
            | None -> ());
           tc')
        (fun () -> rewrite_logging_active := old_flag)
    in
    (* i: index of the selected subgoal inside this tcenv (0-based). *)
    let dorw   = fun i tc ->
      (* i: index of this subgoal (0-based) among currently open goals. *)
      (* Snapshot the single goal handle we’re about to rewrite.
         tc1_handle : tcenv1 -> handle (wraps the current main goal). *)
      let before_goal = [FApi.tc1_handle tc] in
      (* If logging and this is an RWRw with multiple entries, log per entry. *)
      (* When ProofAst logging is on, RWRw with multiple entries needs
         per-entry paths/chosen. We cannot recurse on the real proof state
         (it may change the goal tree or introduce mismatched handles), so:
         1) do a side pass that *only* collects paths/chosen for each entry,
            swallowing benign “nothing to rewrite” failures and never mutating
            the real proof; 2) run the real rewrite once; 3) replay the collected
            events using the real before/after goal handles so JSON goal traces
            stay aligned with the actual rewrite result. *)
      match log_rewrite, unloc ri with
      | Some f, RWRw ((s, r, o, p), entries) ->
          let old_flag = !rewrite_logging_active in
          (* Side collection: gather per-entry paths/chosen without mutating the real proof. *)
          let events = ref [] in
          let () =
            rewrite_logging_active := true;
            clear_rewrite_paths ();
            let is_skippable = function
              | LowRewrite.RewriteError LowRewrite.LRW_NothingToRewrite
              | LowRewrite.RewriteError LowRewrite.LRW_RPatternNoMatch
              | LowRewrite.RewriteError LowRewrite.LRW_RPatternNoRuleMatch
              | LowRewrite.RewriteError LowRewrite.LRW_NotAnEquation -> true
              | EcCoreGoal.TcError tcerr -> begin
                  match tcerr.tc_message with
                  | EcCoreGoal.TCEUser (x, pp) -> String.equal (pp x) "nothing to rewrite"
                  | _ -> false
                end
              | _ -> false
            in
            let rec collect tc entries =
              match entries with
              | [] -> ()
              | (subs, pt) :: rest ->
                  clear_rewrite_paths ();
                  let ri_entry = { ri with pl_desc = RWRw ((s, r, o, p), [ (subs, pt) ]) } in
                  let attempt =
                    if gi = 0 || (i+1) = ngoals
                    then process_rewrite1 ttenv ?target ri_entry
                    else process_rewrite1 ttenv ri_entry in
                  begin match FApi.t_try_base attempt tc with
                  | `Failure exn when is_skippable exn ->
                      events := ([], None) :: !events;
                      collect tc rest
                  | `Failure _ ->
                      events := ([], None) :: !events;
                      collect tc rest
                  | `Success tc' ->
                      let paths, chosen = take_rewrite_paths_and_chosen () in
                      events := (paths, chosen) :: !events;
                      (* Advance if single goal, else stop collecting. *)
                      if FApi.tc_count tc' = 1 then
                        collect (FApi.as_tcenv1 tc') rest
                  end
            in
            collect tc entries;
            rewrite_logging_active := old_flag
          in
          (* Real rewrite run once. *)
          let res = process_rewrite1 ttenv ?target ri tc in
          let after_goal = FApi.tc_opened res in
          (* Replay events with real goal handles to keep numbering consistent. *)
          List.iter
            (fun (paths, chosen) -> f gi chosen paths before_goal after_goal)
            (List.rev !events);
          res
      | _ ->
          if   gi = 0 || (i+1) = ngoals
          then
            (* If this rewrite item is the first, or we’re on the last remaining
               goal, honor the optional [target] (rewrite a specific hypothesis
               instead of the goal) and log around that call. *)
            with_logging before_goal (fun () -> process_rewrite1 ttenv ?target ri tc)
          else
            (* For intermediate goals we ignore [target] to avoid reapplying a
               hypothesis-targeted rewrite across all goals; still log the rewrite. *)
            with_logging before_goal (fun () -> process_rewrite1 ttenv ri tc)
    in

    (* Apply this rewrite item to goals, honoring optional focus [fc]:
       - If no focus, apply to all goals (t_onalli).
       - If focus provided, apply only to selected goals (t_onselecti). *)
    match fc |> omap ((process_tfocus tc) |- unloc) with
    | None    -> FApi.t_onalli dorw tc
    | Some fc -> FApi.t_onselecti fc dorw tc

  in
  (* fold_lefti threads tcenv across rewrite items, passing index+element to do1.
     tcenv_of_tcenv1 lifts the single-goal tcenv1 to multi-goal tcenv. *)
  List.fold_lefti do1 (tcenv_of_tcenv1 tc) ri

(* -------------------------------------------------------------------- *)
let process_elimT qs tc =
  let noelim () = tc_error !!tc "cannot recognize elimination principle" in

  let (hyps, concl) = FApi.tc1_flat tc in

  let (pf, pfty, _concl) =
    match TTC.destruct_product hyps concl with
    | Some (`Forall (x, GTty xty, concl)) -> (x, xty, concl)
    | _ -> noelim ()
  in

  let pf = LDecl.fresh_id hyps (EcIdent.name pf) in
  let tc = t_intros_i_1 [pf] tc in

  let (hyps, concl) = FApi.tc1_flat tc in

  let pt = PT.tc1_process_full_pterm tc qs in

  let (_xp, xpty, ax) =
    match TTC.destruct_product hyps pt.ptev_ax with
    | Some (`Forall (xp, GTty xpty, f)) -> (xp, xpty, f)
    | _ -> noelim ()
  in

  begin
    let ue = pt.ptev_env.pte_ue in
    try  EcUnify.unify (LDecl.toenv hyps) ue (tfun pfty tbool) xpty
    with EcUnify.UnificationFailure _ -> noelim ()
  end;

  if not (PT.can_concretize pt.ptev_env) then noelim ();

  let ax = PT.concretize_form pt.ptev_env ax in

  let rec skip ax =
    match TTC.destruct_product hyps ax with
    | Some (`Imp (_f1, f2)) -> skip f2
    | Some (`Forall (x, GTty xty, f)) -> ((x, xty), f)
    | _ -> noelim ()
  in

  let ((x, _xty), ax) = skip ax in

  let fpf  = f_local pf pfty in

  let ptnpos = FPosition.select_form hyps None fpf concl in
  let (_xabs, body) = FPosition.topattern ~x:x ptnpos concl in

  let rec skipmatch ax body sk =
    match TTC.destruct_product hyps ax, TTC.destruct_product hyps body with
    | Some (`Imp (i1, f1)), Some (`Imp (i2, f2)) ->
        if   EcReduction.is_alpha_eq hyps i1 i2
        then skipmatch f1 f2 (sk+1)
        else sk
    | _ -> sk
  in

  let sk = skipmatch ax body 0 in

  t_seqs
    [t_elimT_form (fst (PT.concretize pt)) ~sk fpf;
     t_or
       (t_clear pf)
       (t_seq (t_generalize_hyp pf) (t_clear pf));
     t_simplify_with_info EcReduction.beta_red]
    tc

(* -------------------------------------------------------------------- *)
let process_view1 pe tc =
  let module E = struct
    exception NoInstance
    exception NoTopAssumption
  end in

  let destruct hyps fp =
    let doit fp =
      match EcFol.sform_of_form fp with
      | SFquant (Lforall, (x, t), lazy f) -> `Forall (x, t, f)
      | SFimp (f1, f2) -> `Imp (f1, f2)
      | SFiff (f1, f2) -> `Iff (f1, f2)
      | _ -> raise EcProofTyping.NoMatch
    in
      EcProofTyping.lazy_destruct hyps doit fp
  in

  let rec instantiate fp ids pte =
    let hyps = pte.PT.ptev_env.PT.pte_hy in

    match destruct hyps pte.PT.ptev_ax with
    | None -> raise E.NoInstance

    | Some (`Forall (x, xty, _)) ->
        instantiate fp ((x, xty) :: ids) (PT.apply_pterm_to_hole pte)

    | Some (`Imp (f1, f2)) -> begin
        try
          PT.pf_form_match ~mode:fmdelta pte.PT.ptev_env ~ptn:f1 fp;
          (pte, ids, f2, `None)
        with MatchFailure -> raise E.NoInstance
    end

    | Some (`Iff (f1, f2)) -> begin
        try
          PT.pf_form_match ~mode:fmdelta pte.PT.ptev_env ~ptn:f1 fp;
          (pte, ids, f2, `IffLR (f1, f2))
        with MatchFailure -> try
          PT.pf_form_match ~mode:fmdelta pte.PT.ptev_env ~ptn:f2 fp;
          (pte, ids, f1, `IffRL (f1, f2))
        with MatchFailure ->
          raise E.NoInstance
    end
  in

  try
    match TTC.destruct_product (tc1_hyps tc) (FApi.tc1_goal tc) with
    | None -> raise E.NoTopAssumption

    | Some (`Forall _) ->
      process_elimT pe tc

    | Some (`Imp (f1, _)) when pe.fp_head = FPCut None ->
        let hyps = FApi.tc1_hyps tc in
        let hid  = LDecl.fresh_id hyps "h" in
        let hqs  = mk_loc _dummy ([], EcIdent.name hid) in
        let pe   = { pe with fp_head = FPNamed (hqs, None) } in

        t_intros_i_seq ~clear:true [hid]
          (fun tc ->
            let pe = PT.tc1_process_full_pterm tc pe in
            let regen =
              if PT.can_concretize pe.PT.ptev_env then [] else

              snd (List.fold_left_map (fun f1 arg ->
                let pre, f1 =
                  match oget (TTC.destruct_product (tc1_hyps tc) f1) with
                  | `Imp    (_, f1)      -> (None, f1)
                  | `Forall (x, xty, f1) ->
                    let aout =
                      match xty with GTty ty -> Some (x, ty) | _ -> None
                    in (aout, f1)
                in

                let module E = struct exception Bailout end in

                try
                  let v =
                    match arg with
                    | PAFormula { f_node = Flocal x } ->
                        let meta =
                          let env = !(pe.PT.ptev_env.pte_ev) in
                          MEV.mem x `Form env && not (MEV.isset x `Form env) in

                        if not meta then raise E.Bailout;

                        let y, yty =
                          let CPTEnv subst = PT.concretize_env pe.PT.ptev_env in
                          snd_map (ty_subst subst) (oget pre) in
                        let fy = EcIdent.fresh y in

                        pe.PT.ptev_env.pte_ev := MEV.set
                          x (`Form (f_local fy yty)) !(pe.PT.ptev_env.pte_ev);
                        (fy, yty)

                    | _ ->
                        raise E.Bailout
                  in (f1, Some v)

                with E.Bailout -> (f1, None)
              ) f1 (get_pt_top_args pe.PT.ptev_pt))
            in

            let regen = List.pmap (fun x -> x) regen in
            let bds   = List.map (fun (x, ty) -> (x, GTty ty)) regen in

            if not (PT.can_concretize pe.PT.ptev_env) then
              tc_error !!tc "cannot infer all placeholders";

            let pt, ax = PT.concretize_gen pe bds in
            t_first (fun subtc ->
              let regen = List.fst regen in
              let ttcut tc =
                t_onall
                  (EcLowGoal.t_generalize_hyps ~clear:`Yes regen)
                  (EcLowGoal.t_apply pt tc) in
              t_intros_i_seq regen ttcut subtc
            ) (t_cut ax tc)
          ) tc

    | Some (`Imp (f1, _)) ->
        let top    = LDecl.fresh_id (tc1_hyps tc) "h" in
        let tc     = t_intros_i_1 [top] tc in
        let hyps   = tc1_hyps tc in
        let pte    = PT.tc1_process_full_pterm tc pe in
        let inargs = List.length (get_pt_top_args pte.PT.ptev_pt) in

        let (pte, ids, cutf, view) = instantiate f1 [] pte in

        let evm  = !(pte.PT.ptev_env.PT.pte_ev) in
        let args = List.drop inargs (get_pt_top_args pte.PT.ptev_pt) in
        let args = List.combine (List.rev ids) args in

        let ids =
          let for1 ((_, ty) as idty, arg) =
            match ty, arg with
            | GTty _, PAFormula { f_node = Flocal x } when MEV.mem x `Form evm ->
                if MEV.isset x `Form evm then None else Some (x, idty)

            | GTmem _, PAMemory x when MEV.mem x `Mem evm ->
                if MEV.isset x `Mem evm then None else Some (x, idty)

            | _, _ -> assert false

          in List.pmap for1 args
        in

        let cutf =
          let ptenv = PT.copy pte.PT.ptev_env in

          let for1 evm (x, idty) =
            match idty with
            | id, GTty    ty -> evm := MEV.set x (`Form (f_local id ty)) !evm
            | id, GTmem   _  -> evm := MEV.set x (`Mem id) !evm
            | _ , GTmodty _  -> assert false
          in

          List.iter (for1 ptenv.PT.pte_ev) ids;

          if not (PT.can_concretize ptenv) then
            tc_error !!tc "cannot infer all type variables";

          PT.concretize_e_form_gen
            (PT.concretize_env ptenv)
            (List.snd ids) cutf
        in

        let discharge tc =
          let intros = List.map (EcIdent.name |- fst |- snd) ids in
          let intros = LDecl.fresh_ids hyps intros in

          let for1 evm (x, idty) id =
            match idty with
            | _, GTty   ty -> evm := MEV.set x (`Form (f_local id ty)) !evm
            | _, GTmem   _ -> evm := MEV.set x (`Mem id) !evm
            | _, GTmodty _ -> assert false

          in

          let tc = EcLowGoal.t_intros_i_1 intros tc in

          List.iter2 (for1 pte.PT.ptev_env.PT.pte_ev) ids intros;

          let pte =
            match view with
            | `None -> pte

            | `IffLR (f1, f2) ->
                let vpte = PT.pt_of_global_r pte.PT.ptev_env LG.p_iff_lr [] in
                let vpte = PT.apply_pterm_to_arg_r vpte (PVAFormula f1) in
                let vpte = PT.apply_pterm_to_arg_r vpte (PVAFormula f2) in
                let vpte = PT.apply_pterm_to_arg_r vpte (PVASub pte) in
                vpte

            | `IffRL (f1, f2) ->
                let vpte = PT.pt_of_global_r pte.PT.ptev_env LG.p_iff_rl [] in
                let vpte = PT.apply_pterm_to_arg_r vpte (PVAFormula f1) in
                let vpte = PT.apply_pterm_to_arg_r vpte (PVAFormula f2) in
                let vpte = PT.apply_pterm_to_arg_r vpte (PVASub pte) in
                vpte

          in

          let pt = fst (PT.concretize (PT.apply_pterm_to_hole pte)) in

          FApi.t_seq
            (EcLowGoal.t_apply pt)
            (EcLowGoal.t_apply_hyp top)
            tc
        in

        FApi.t_internal
          (FApi.t_seqsub (EcLowGoal.t_cut cutf)
             [EcLowGoal.t_close ~who:"view" discharge;
              EcLowGoal.t_clear top])
          tc

  with
  | E.NoInstance ->
      tc_error !!tc "cannot apply view"
  | E.NoTopAssumption ->
      tc_error !!tc "no top assumption"

(* -------------------------------------------------------------------- *)
let process_view pes tc =
  let views = List.map (t_last |- process_view1) pes in
  List.fold_left (fun tc tt -> tt tc) (FApi.tcenv_of_tcenv1 tc) views

(* -------------------------------------------------------------------- *)
module IntroState : sig
  type state
  type action = [ `Revert | `Dup | `Clear ]

  val create  : unit -> state
  val push    : ?name:symbol -> action -> EcIdent.t -> state -> unit
  val listing : state -> ([`Gen of genclear | `Clear] * EcIdent.t) list
  val naming  : state -> (EcIdent.t -> symbol option)
end = struct
  type state = {
    mutable torev  : ([`Gen of genclear | `Clear] * EcIdent.t) list;
    mutable naming : symbol option Mid.t;
  }

  and action = [ `Revert | `Dup | `Clear ]

  let create () =
    { torev = []; naming = Mid.empty; }

  let push ?name action id st =
    let map =
      Mid.change (function
      | None   -> Some name
      | Some _ -> assert false)
      id st.naming
    and action =
      match action with
      | `Revert -> `Gen `TryClear
      | `Dup    -> `Gen `NoClear
      | `Clear  -> `Clear
    in
      st.torev  <- (action, id) :: st.torev;
      st.naming <- map

  let listing (st : state) =
    List.rev st.torev

  let naming (st : state) (x : EcIdent.t) =
    Mid.find_opt x st.naming |> odfl None
end

(* -------------------------------------------------------------------- *)
exception IntroCollect of [
  `InternalBreak
]

exception CollectBreak
exception CollectCore of ipcore located

let rec process_mintros_1 ?(cf = true) ?log_elem ttenv pis gs =
  let module ST = IntroState in

  let mk_intro ids (hyps, form) =
    let (_, torev), ids =
      let rec compile (((hyps, form), torev) as acc) newids ids =
        match ids with [] -> (acc, newids) | s :: ids ->

        let rec destruct fp =
          match EcFol.sform_of_form fp with
          | SFquant (Lforall, (x, _)  , lazy fp) ->
              let name = EcIdent.name x in (name, Some name, `Named, fp)
          | SFlet (LSymbol (x, _), _, fp) ->
              let name = EcIdent.name x in (name, Some name, `Named, fp)
          | SFimp (_, fp) ->
              ("H", None, `Hyp, fp)
          | _ -> begin
            match EcReduction.h_red_opt EcReduction.full_red hyps fp with
            | None   -> ("_", None, `None, f_true)
            | Some f -> destruct f
          end
        in
        let name, revname, kind, form = destruct form in
        let revertid =
          if ttenv.tt_oldip then
            match unloc s with
            | `Revert      -> Some (Some false, EcIdent.create "_")
            | `Clear       -> Some (None      , EcIdent.create "_")
            | `Named s     -> Some (None      , EcIdent.create s)
            | `Anonymous a ->
               if   (a = Some None && kind = `None) || a = Some (Some 0)
               then None
               else Some (None, LDecl.fresh_id hyps name)
          else
            match unloc s with
            | `Revert      -> Some (Some false, EcIdent.create "_")
            | `Clear       -> Some (Some true , EcIdent.create "_")
            | `Named s     -> Some (None      , EcIdent.create s)
            | `Anonymous a ->
               match a, kind with
               | Some None, `None ->
                  None
               | (Some (Some 0), _) ->
                  None
               | _, `Named ->
                  Some (None, LDecl.fresh_id hyps ("`" ^ name))
               | _, _ ->
                  Some (None, LDecl.fresh_id hyps "_")
        in

        match revertid with
        | Some (revert, id) ->
            let id     = mk_loc s.pl_loc id in
            let hyps   = LDecl.add_local id.pl_desc (LD_var (tbool, None)) hyps in
            let revert = revert |> omap (fun b -> if b then `Clear else `Revert) in
            let torev  = revert
              |> omap (fun b -> (b, unloc id, revname) :: torev)
              |> odfl torev
            in

            let newids = Tagged (unloc id, Some id.pl_loc) :: newids in

            let ((hyps, form), torev), newids =
              match unloc s with
              | `Anonymous (Some None) when kind <> `None ->
                 compile ((hyps, form), torev) newids [s]
              | `Anonymous (Some (Some i)) when 1 < i ->
                 let s = mk_loc (loc s) (`Anonymous (Some (Some (i-1)))) in
                 compile ((hyps, form), torev) newids [s]
              | _ -> ((hyps, form), torev), newids

            in compile ((hyps, form), torev) newids ids

        | None -> compile ((hyps, form), torev) newids ids

      in snd_map List.rev (compile ((hyps, form), []) [] ids)

    in (List.rev torev, ids)
  in

  let intropattern_of_token (token : EcProofAst.intro_token located) =
    match token.pl_desc with
    | `Core cores ->
        List.map
          (fun ip -> mk_loc ip.pl_loc (IPCore (unloc ip)))
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
  in

  let tokens_to_pattern tokens =
    List.flatten (List.map intropattern_of_token tokens)
  in

  let rec collect intl acc core pis =
    let maybe_core () =
      let loc = EcLocation.mergeall (List.map loc core) in
      match core with
      | [] -> acc
      | _  -> mk_loc loc (`Core (List.rev core)) :: acc
    in

    match pis with
    | [] -> (maybe_core (), [])
    | { pl_loc = ploc } as pi :: pis ->
      try
        let ip =
          match unloc pi with
          | IPBreak ->
             if intl then raise (IntroCollect `InternalBreak);
             raise CollectBreak

          | IPCore     x -> raise (CollectCore (mk_loc (loc pi) x))
          | IPDup        -> `Dup
          | IPDone     x -> `Done x
          | IPSmt      x -> `Smt x
          | IPClear    x -> `Clear x
          | IPRw       x -> `Rw x
          | IPDelta    x -> `Delta x
          | IPView     x -> `View x
          | IPSubst    x -> `Subst x
          | IPSimplify x -> `Simpl x
          | IPCrush    x -> `Crush x

          | IPCase (mode, x) ->
              let subcollect tokens =
                let tokens, _ = collect true [] [] tokens in
                tokens_to_pattern (List.rev tokens)
              in
              `Case (mode, List.map subcollect x)

          | IPSubstTop x -> `SubstTop x

        in collect intl (mk_loc ploc ip :: maybe_core ()) [] pis

      with
      | CollectBreak  -> (maybe_core (), pis)
      | CollectCore x -> collect intl acc (x :: core) pis

  in

  let collect pis = collect false [] [] pis in

  let rec intro1_core (st : ST.state) ids (tc : tcenv1) =
    let torev, ids = mk_intro ids (FApi.tc1_flat tc) in
    List.iter (fun (act, id, name) -> ST.push ?name act id st) torev;
    t_intros ids tc

  and intro1_dup (_ : ST.state) (tc : tcenv1) =
    try
      let pt = PT.pt_of_uglobal !!tc (FApi.tc1_hyps tc) LG.p_ip_dup in
      EcLowGoal.Apply.t_apply_bwd_r ~mode:fmrigid ~canview:false pt tc
    with EcLowGoal.Apply.NoInstance _ ->
      tc_error !!tc "no top-assumption to duplicate"

  and intro1_done (_ : ST.state) simplify (tc : tcenv1) =
    let t =
      match simplify with
      | Some x ->
         t_seq (t_simplify_lg ~delta:`No (ttenv, x)) process_trivial
      | None -> process_trivial
    in t tc

  and intro1_smt (_ : ST.state) (dn : bool) (pi : pprover_infos) (tc : tcenv1) =
    if dn then
      t_or process_done (process_smt ttenv (Some pi)) tc
    else process_smt ttenv (Some pi) tc

  and intro1_simplify (_ : ST.state) logic tc =
    t_simplify_lg ~delta:`IfApplied (ttenv, logic) tc

  and intro1_clear (_ : ST.state) xs tc =
    process_clear (`Include xs) tc

  and intro1_case (st : ST.state) nointro pis gs =
    let branch_logger =
      match pis with
      | [_] -> None
      | _ -> log_elem
    in

    let onsub gs =
      if List.is_empty pis then gs else begin
        if FApi.tc_count gs <> List.length pis then
          tc_error !$gs
            "not the right number of intro-patterns (got %d, expecting %d)"
            (List.length pis) (FApi.tc_count gs);
        t_sub (List.map (dointro1 branch_logger st false) pis) gs
        end
    in

    let tc = t_ors [t_elimT_ind `Case; t_elim; t_elim_prind `Case] in
    let tc =
      fun g ->
        try  tc g
        with InvalidGoalShape ->
          tc_error !!g "invalid intro-pattern: nothing to eliminate"
    in

    let apply_case_all state =
      match log_elem with
      | None -> t_onall tc state
      | Some log ->
          let before = FApi.tc_opened state in
          let state' = t_onall tc state in
          let after = FApi.tc_opened state' in
          if before <> after then log EcProofAst.IEBridge before after;
          state'
    in

    if nointro && not cf then onsub gs else begin
      match pis with
      | [] -> apply_case_all gs
      | _  ->
          let eliminated = apply_case_all gs in
          t_onall (fun goal -> onsub (FApi.tcenv_of_tcenv1 goal)) eliminated
    end

  and intro1_full_case (st : ST.state)
    ((prind, delta), withor, (cnt : icasemode_full option)) pis tc
  =
    let cnt = cnt |> odfl (`AtMost 1) in
    let red = if delta then `Full else `NoDelta in

    let t_case =
      let t_and, t_or =
        if prind then
          ((fun tc -> fst_map List.singleton (t_elim_iso_and ~reduce:red tc)),
           (fun tc -> t_elim_iso_or ~reduce:red tc))
        else
          ((fun tc -> ([2]   , t_elim_and ~reduce:red tc)),
           (fun tc -> ([1; 1], t_elim_or  ~reduce:red tc))) in
      let ts = if withor then [t_and; t_or] else [t_and] in
      fun tc -> FApi.t_or_map ts tc
    in

    let onsub gs =
      if List.is_empty pis then gs else begin
        if FApi.tc_count gs <> List.length pis then
          tc_error !$gs
            "not the right number of intro-patterns (got %d, expecting %d)"
            (List.length pis) (FApi.tc_count gs);
        t_sub (List.map (dointro1 log_elem st false) pis) gs
        end
    in

    let doit tc =
      let rec aux imax tc =
        if imax = Some 0 then t_id tc else

        try
          let ntop, tc = t_case tc in

          FApi.t_sublasts
            (List.map (fun i tc -> aux (omap ((+) (i-1)) imax) tc) ntop)
            tc
        with InvalidGoalShape ->
          try
            tc |> EcLowGoal.t_intro_sx_seq
              `Fresh
              (fun id ->
                t_seq
                  (aux (omap ((+) (-1)) imax))
                  (t_generalize_hyps ~clear:`Yes [id]))
          with
          | EcCoreGoal.TcError _ when EcUtils.is_some imax ->
              tc_error !!tc "not enough top-assumptions"
          | EcCoreGoal.TcError _ ->
              t_id tc
      in

      match cnt with
      | `AtMost cnt -> aux (Some (max 1 cnt)) tc
      | `AsMuch     -> aux None tc
    in

    let run_with_bridge_tcenv1 :
        (tcenv1 -> tcenv) -> tcenv1 -> tcenv =
      fun action tc ->
        match log_elem with
        | None -> action tc
        | Some log ->
            let before = FApi.tc_opened (FApi.tcenv_of_tcenv1 tc) in
            let tc' = action tc in
            let after = FApi.tc_opened tc' in
            if before <> after then log EcProofAst.IEBridge before after;
            tc'
    in

    if List.is_empty pis then run_with_bridge_tcenv1 doit tc
    else onsub (run_with_bridge_tcenv1 doit tc)

  and intro1_rw (_ : ST.state) (o, s) tc =
    let h = EcIdent.create "_" in
    let rwt tc =
      let pt = PT.pt_of_hyp !!tc (FApi.tc1_hyps tc) h in
      process_rewrite1_core ~close:false (s, None, o) pt tc
    in t_seqs [t_intros_i [h]; rwt; t_clear h] tc

  and intro1_unfold (_ : ST.state) (s, o) p tc =
    process_delta ~und_delta:ttenv.tt_und_delta (s, o, p) tc

  and intro1_view (_ : ST.state) pe tc =
    process_view1 pe tc

  and intro1_subst (_ : ST.state) d (tc : tcenv1) =
    try
      t_intros_i_seq ~clear:true [EcIdent.create "_"]
        (EcLowGoal.t_subst ~clear:true ~tside:(d :> tside))
        tc
    with InvalidGoalShape ->
      tc_error !!tc "nothing to substitute"

  and intro1_subst_top (_ : ST.state) (omax, osd) (tc : tcenv1) =
    let t_subst eqid =
      let sk1  = { empty_subst_kind with sk_local = true ; } in
      let sk2  = {  full_subst_kind with sk_local = false; } in
      let side = `All osd in
      FApi.t_or
        (t_subst ~tside:side ~kind:sk1 ~eqid)
        (t_subst ~tside:side ~kind:sk2 ~eqid)
    in

    let togen = ref [] in

    let rec doit i tc =
      match omax with Some max when i >= max -> tcenv_of_tcenv1 tc | _ ->

      try
        let id = EcIdent.create "_" in
        let tc = EcLowGoal.t_intros_i_1 [id] tc in
        FApi.t_switch (t_subst id) ~ifok:(doit (i+1))
          ~iffail:(fun tc -> togen := id :: !togen; doit (i+1) tc)
          tc
      with EcCoreGoal.TcError _ ->
        if is_some omax then
          tc_error !!tc "not enough top-assumptions";
        tcenv_of_tcenv1 tc in

    let tc = doit 0 tc in

    t_generalize_hyps
      ~clear:`Yes ~missing:true
      (List.rev !togen) (FApi.as_tcenv1 tc)

  and intro1_crush (_st : ST.state) (d : crushmode) (gs : tcenv1) =
    let delta, tsolve = process_crushmode d in
    FApi.t_or
      (EcPhlConseq.t_conseqauto ~delta ?tsolve)
      (EcLowGoal.t_crush ~delta ?tsolve)
      gs

  and dointro (logger : (EcProofAst.intro_element -> handle list -> handle list -> unit) option)
      (st : ST.state) nointro pis (gs : tcenv) =
    match pis with [] -> gs | { pl_desc = pi; pl_loc = ploc } :: pis ->
      let rl x = EcCoreGoal.reloc ploc x in
      let located : EcProofAst.intro_token EcLocation.located = mk_loc ploc pi in
      let exec action =
        match logger with
        | None -> action gs
        | Some log ->
            let before = FApi.tc_opened gs in
            let gs' = action gs in
            let after = FApi.tc_opened gs' in
            log (EcProofAst.IEPattern located) before after;
            gs'
      in
      let nointro, gs =
        match pi with
        | `Core ids ->
            (false, exec (fun state -> rl (t_onall (intro1_core st ids)) state))

        | `Dup ->
            (false, exec (fun state -> rl (t_onall (intro1_dup st)) state))

        | `Done b ->
            (nointro, exec (fun state -> rl (t_onall (intro1_done st b)) state))

        | `Smt (b, pi) ->
            (nointro, exec (fun state -> rl (t_onall (intro1_smt st b pi)) state))

        | `Simpl b ->
            (nointro, exec (fun state -> rl (t_onall (intro1_simplify st b)) state))

        | `Clear xs ->
            (nointro, exec (fun state -> rl (t_onall (intro1_clear st xs)) state))

        | `Case (`One, pis) ->
            (false, exec (fun state -> rl (intro1_case st nointro pis) state))

        | `Case (`Full x, pis) ->
            (false, exec (fun state -> rl (t_onall (intro1_full_case st x pis)) state))

        | `Rw (o, s, None) ->
            (false, exec (fun state -> rl (t_onall (intro1_rw st (o, s))) state))

        | `Rw (o, s, Some i) ->
            (false, exec (fun state -> rl (t_onall (t_do `All i (intro1_rw st (o, s)))) state))

        | `Delta ((o, s), p) ->
            (nointro, exec (fun state -> rl (t_onall (intro1_unfold st (o, s) p)) state))

        | `View pe ->
            (false, exec (fun state -> rl (t_onall (intro1_view st pe)) state))

        | `Subst (d, None) ->
            (false, exec (fun state -> rl (t_onall (intro1_subst st d)) state))

        | `Subst (d, Some i) ->
            (false, exec (fun state -> rl (t_onall (t_do `All i (intro1_subst st d))) state))

        | `SubstTop d ->
            (false, exec (fun state -> rl (t_onall (intro1_subst_top st d)) state))

        | `Crush d ->
           (false, exec (fun state -> rl (t_onall (intro1_crush st d)) state))

      in dointro logger st nointro pis gs

  and dointro1 logger st nointro pis tc =
    let cmds, _ = collect pis in
    dointro logger st nointro (List.rev cmds) (FApi.tcenv_of_tcenv1 tc) in

  try
    let st = ST.create () in
    let ip, pis = collect pis in
    let gs = dointro log_elem st true (List.rev ip) gs in
    let gs =
      let ls = ST.listing st in
      let gn = List.pmap (function (`Gen x, y) -> Some (x, y) | _ -> None) ls in
      let cl = List.pmap (function (`Clear, y) -> Some y | _ -> None) ls in
      let apply_cleanup gs =
        let gs = t_onall (t_clears cl) gs in
        t_onall
          (fun tc ->
            t_generalize_hyps_x
              ~missing:true
              ~naming:(ST.naming st)
              gn tc)
          gs
      in
      let needs_bridge = not (List.is_empty gn) || not (List.is_empty cl) in
      if not needs_bridge then
        apply_cleanup gs
      else
        match log_elem with
        | Some log ->
            let before = FApi.tc_opened gs in
            let gs' = apply_cleanup gs in
            let after = FApi.tc_opened gs' in
            log EcProofAst.IEBridge before after;
            gs'
        | None -> apply_cleanup gs
    in

    if List.is_empty pis then gs else
      gs |> t_onall (fun tc ->
        process_mintros_1 ~cf:true ?log_elem ttenv pis (FApi.tcenv_of_tcenv1 tc))

  with IntroCollect e -> begin
    match e with
    | `InternalBreak ->
         tc_error !$gs "cannot use internal break in intro-patterns"
  end

(* -------------------------------------------------------------------- *)
let process_intros_1 ?cf ttenv pis tc =
  process_mintros_1 ?cf ttenv pis (FApi.tcenv_of_tcenv1 tc)

(* -------------------------------------------------------------------- *)
let rec process_mintros ?cf ttenv pis tc =
  match pis with [] -> tc | pi :: pis ->
    let tc = process_mintros_1 ?cf ttenv pi tc in
    process_mintros ~cf:false ttenv pis tc

(* -------------------------------------------------------------------- *)
let process_intros ?cf ttenv pis tc =
  process_mintros ?cf ttenv pis (FApi.tcenv_of_tcenv1 tc)

(* -------------------------------------------------------------------- *)
let process_generalize1 ?(doeq = false) pattern (tc : tcenv1) =
  let env, hyps, concl = FApi.tc1_eflat tc in

  let onresolved ?(tryclear = true) pattern =
    let clear = if tryclear then `Yes else `No in

    match pattern with
    | `Form (occ, pf) -> begin
        match pf.pl_desc with
        | PFident ({pl_desc = ([], s)}, None)
            when not doeq && is_none occ && LDecl.has_name s hyps
          ->
            let id = fst (LDecl.by_name s hyps) in
            t_generalize_hyp ~clear id tc

        | PFmem { pl_loc = loc; pl_desc = m; } -> begin
            if doeq then
              tacuerror "cannot generate an equation when generalizing a memory";

            let m, lc =
              try
                LDecl.by_name m hyps
              with LDecl.LdeclError (LookupError _) ->
                tc_error !!tc ~loc "cannot find memory `%s'" m
            in

            let lc = match lc with LD_mem mt -> mt | _ -> assert false in

            if is_none occ then
              t_generalize_hyp ~clear m tc
            else begin
              let occ = norm_rwocc occ in

              let ptnpos =
                try
                  FPosition.select ?o:occ (fun ctxt f ->
                    if Sid.mem m ctxt then
                      `Continue
                    else
                      match f.f_node with
                      | Fglob (_, m')
                      | Fpvar (_, m')
                      | Fpr   { pr_mem = m' }  when EcIdent.id_equal m m' -> `Accept 0
                      | _ -> `Continue
                  ) concl
                with InvalidOccurence -> tacuerror "invalid occurence selector"
              in

              let m' = EcIdent.fresh m in

              let newconcl =
                concl |> FPosition.map ptnpos (fun f ->
                  match f.f_node with
                  | Fglob (a, _) -> f_glob a m'
                  | Fpvar (p, _) -> f_pvar p f.f_ty m'
                  | Fpr   pr     -> f_pr_r { pr with pr_mem = m' }
                  | _            -> assert false
                ) in

              let newconcl = f_forall [(m', GTmem lc)] newconcl in
              let pt = ptcut ~args:[PAMemory m] newconcl in
      
              EcLowGoal.t_apply pt tc
            end
          end
 
        | _ ->
          let (ptenv, p) =
            let (ps, ue), p = TTC.tc1_process_pattern tc pf in
            let ev = MEV.of_idents (Mid.keys ps) `Form in
              (ptenv !!tc hyps (ue, ev), p)
          in

          (try  ignore (PT.pf_find_occurence ptenv ~ptn:p concl)
           with PT.FindOccFailure _ -> tc_error !!tc "cannot find an occurence");

          let p    = PT.concretize_form ptenv p in
          let occ  = norm_rwocc occ in
          let cpos =
            try  FPosition.select_form ~xconv:`AlphaEq hyps occ p concl
            with InvalidOccurence -> tacuerror "invalid occurence selector"
          in

          let name =
            match EcParsetree.pf_ident pf with
            | None ->
                EcIdent.create "x"
            | Some x when EcIo.is_sym_ident x ->
                EcIdent.create x
            | Some _ ->
                EcIdent.create (EcTypes.symbol_of_ty p.f_ty)
          in

          let name, newconcl = FPosition.topattern ~x:name cpos concl in
          let newconcl =
            if doeq then
              if EcReduction.EqTest.for_type env p.f_ty tbool then
                f_imps [f_iff p (f_local name p.f_ty)] newconcl
              else
                f_imps [f_eq p (f_local name p.f_ty)] newconcl
            else newconcl in
          let newconcl = f_forall [(name, GTty p.f_ty)] newconcl in
          let pt = ptcut ~args:[PAFormula p] newconcl in

          EcLowGoal.t_apply pt tc

    end

    | `ProofTerm fp -> begin
        match fp.fp_head with
        | FPNamed ({ pl_desc = ([], s) }, None)
            when LDecl.has_name s hyps && List.is_empty fp.fp_args
          ->
            let id = fst (LDecl.by_name s hyps) in
            t_generalize_hyp ~clear id tc

        | _ ->
          let pt = PT.tc1_process_full_pterm tc fp in
          if not (PT.can_concretize pt.PT.ptev_env) then
            tc_error !!tc "cannot infer all placeholders";
          let pt, ax = PT.concretize pt in
          t_cutdef pt ax tc
    end

    | `LetIn x ->
        let id =
          let binding =
            try  Some (LDecl.by_name (unloc x) hyps)
            with EcEnv.LDecl.LdeclError _ -> None in

            match binding  with
            | Some (id, LD_var (_, Some _)) -> id
            | _ ->
                let msg = "symbol must reference let-in" in
                tc_error ~loc:(loc x) !!tc "%s" msg

        in t_generalize_hyp ~clear ~letin:true id tc
  in

  match ffpattern_of_genpattern hyps pattern with
  | Some ff ->
     let tryclear =
       match pattern with
       | (`Form (None, { pl_desc = PFident _ })) -> true
       | _ -> false
     in onresolved ~tryclear (`ProofTerm ff)
  | None -> onresolved pattern

(* -------------------------------------------------------------------- *)
let process_generalize ?(doeq = false) patterns (tc : tcenv1) =
  try
    let patterns = List.mapi (fun i p ->
      process_generalize1 ~doeq:(doeq && i = 0) p) patterns in
    FApi.t_seqs (List.rev patterns) tc
  with (EcCoreGoal.ClearError _) as err ->
    tc_error_exn !!tc err

(* -------------------------------------------------------------------- *)
let process_mgenintros ?cf ?log_intro ?log_intro_elem ttenv pis tc =
  (* Walk the list of intro directives [pis], optionally logging:
     - log_intro: per-intro before/after goal trace
     - log_intro_elem: per-element before/after goal trace, keyed by intro idx
     cf: carry/no-progress flag forwarded to intro handling. *)
  let rec aux idx cf_opt tc = function
    | [] -> tc
    | pi :: rest ->
        let before =
          match log_intro with
          | Some _ -> Some (FApi.tc_opened tc)
          | None -> None
        in
        let elem_logger =
          match log_intro_elem with
          | Some log -> Some (log idx)  (* per-intro element logger (ProofAst) *)
          | None -> None
        in
        let tc =
          match pi with
          | `Ip pi ->
              process_mintros_1 ?cf:cf_opt ?log_elem:elem_logger ttenv pi tc
          | `Gen gn ->
              let elem_before =
                match elem_logger with
                | Some _ -> Some (FApi.tc_opened tc)
                | None -> None
              in
              let tc =
                t_onall (
                  t_seqs [
                      process_clear (`Include gn.pr_clear);
                      process_generalize gn.pr_genp
                  ]) tc
              in
              (match elem_logger, elem_before with
               | Some log, Some b ->
                   let after = FApi.tc_opened tc in
                   log (EcProofAst.IEGen gn) b after
               | _ -> ());
              tc
        in
        (match log_intro, before with
         | Some log, Some b ->
             let after = FApi.tc_opened tc in
             (* Per-intro logger (ProofAst): record before/after goal trace. *)
             log pi b after
         | _ -> ());
        aux (idx + 1) (Some false) tc rest
  in
  let initial_cf = match cf with Some v -> Some v | None -> None in
  aux 0 initial_cf tc pis

(* -------------------------------------------------------------------- *)
let process_genintros ?cf ?log_intro ?log_intro_elem ttenv pis tc =
  process_mgenintros ?cf ?log_intro ?log_intro_elem ttenv pis (FApi.tcenv_of_tcenv1 tc)

(* -------------------------------------------------------------------- *)
let process_move ?doeq views pr (tc : tcenv1) =
  t_seqs
    [process_clear (`Include pr.pr_clear);
     process_generalize ?doeq pr.pr_genp;
     process_view views]
    tc

(* -------------------------------------------------------------------- *)
let process_pose xsym bds o p (tc : tcenv1) =
  let (env, hyps, concl) = FApi.tc1_eflat tc in
  let o = norm_rwocc o in

  let (ptenv, p) =
    let ps  = ref Mid.empty in
    let ue  = TTC.unienv_of_hyps hyps in
    let (senv, bds) = EcTyping.trans_binding env ue bds in
    let p = EcTyping.trans_pattern senv ps ue p in
    let ev = MEV.of_idents (Mid.keys !ps) `Form in
    (ptenv !!tc hyps (ue, ev),
     f_lambda (List.map (snd_map gtty) bds) p)
  in

  let dopat =
    try
      ignore (PT.pf_find_occurence ~occmode:PT.om_rigid ptenv ~ptn:p concl);
      true
    with PT.FindOccFailure _ ->
      if not (PT.can_concretize ptenv) then
        if not (EcMatching.MEV.filled !(ptenv.PT.pte_ev)) then
          tc_error !!tc "cannot find an occurence"
        else
          tc_error !!tc "%s - %s"
            "cannot find an occurence"
            "instantiate type variables manually"
      else
        false
  in

  let p = PT.concretize_form ptenv p in

  let (x, letin) =
    match dopat with
    | false -> (EcIdent.create (unloc xsym), concl)
    | true  -> begin
        let cpos =
          try  FPosition.select_form ~xconv:`AlphaEq hyps o p concl
          with InvalidOccurence -> tacuerror "invalid occurence selector"
        in
          FPosition.topattern ~x:(EcIdent.create (unloc xsym)) cpos concl
    end
  in

  let letin = EcFol.f_let1 x p letin in

  FApi.t_seq
    (t_change letin)
    (t_intros [Tagged (x, Some xsym.pl_loc)]) tc

(* -------------------------------------------------------------------- *)
let process_memory (xsym : psymbol) tc =
  let x = EcIdent.create (unloc xsym) in
  let m = EcMemory.empty_local_mt ~witharg:false in

  FApi.t_sub
    [
      t_trivial;
      FApi.t_seqs [
        t_elim_exists ~reduce:`None;
        t_intros [Tagged (x, Some xsym.pl_loc)];
        t_intros_n ~clear:true 1;
      ]
    ]
    (t_cut (f_exists [x, GTmem m] f_true) tc)

(* -------------------------------------------------------------------- *)
type apply_t = EcParsetree.apply_info

let process_apply ~implicits ?log_apply ((infos, orv) : apply_t * prevert option) tc =
  let with_logging idx before process =
    let logging = Option.is_some log_apply in
    let old_flag = !apply_logging_active in
    apply_logging_active := logging;
    EcUtils.try_finally
      (fun () ->
         if logging then clear_apply_paths ();
         let tc' = process () in
         let paths, chosen =
           if logging then take_apply_paths_and_chosen () else ([], None)
         in
         (match log_apply with
          | Some f ->
              let after_goal = FApi.tc_opened tc' in
              f idx chosen paths before after_goal
          | None -> ());
         tc')
      (fun () -> apply_logging_active := old_flag)
  in
  let do_apply tc =
    match infos with
    | `ApplyIn (pe, tg) ->
        let before = FApi.tc_opened (tcenv_of_tcenv1 tc) in
        with_logging 0 before (fun () ->
            process_apply_fwd ~implicits (pe, tg) tc)

    | `Apply (pe, mode) ->
        let step (idx, tc_acc) pe =
          let before = FApi.tc_opened tc_acc in
          let tc_acc =
            with_logging idx before (fun () ->
                t_last (process_apply_bwd ~implicits `Apply pe) tc_acc)
          in
          (idx + 1, tc_acc)
        in
        let _, tc = List.fold_left step (0, tcenv_of_tcenv1 tc) pe in
        if mode = `Exact then t_onall process_done tc else tc

    | `Alpha pe ->
        let before = FApi.tc_opened (tcenv_of_tcenv1 tc) in
        with_logging 0 before (fun () -> process_apply_bwd ~implicits `Alpha pe tc)

    | `ExactType qs ->
        let before = FApi.tc_opened (tcenv_of_tcenv1 tc) in
        with_logging 0 before (fun () -> process_exacttype qs tc)

    | `Top mode ->
        let before = FApi.tc_opened (tcenv_of_tcenv1 tc) in
        let tc = with_logging 0 before (fun () -> process_apply_top tc) in
        if mode = `Exact then t_onall process_done tc else tc

  in

  t_seq
    (fun tc -> ofdfl
       (fun () -> t_id tc)
       (omap (fun rv -> process_move [] rv tc) orv))
    do_apply tc

(* -------------------------------------------------------------------- *)
let process_subst syms (tc : tcenv1) =
  let resolve symp =
    let sym = TTC.tc1_process_form_opt tc None symp in

    match sym.f_node with
    | Flocal id        -> `Local id
    | Fglob  (mp, mem) -> `Glob  (mp, mem)
    | Fpvar  (pv, mem) -> `PVar  (pv, mem)

    | _ ->
      tc_error !!tc ~loc:symp.pl_loc
        "this formula is not subject to substitution"
  in

  let exception NothingToSubstitute of vsubst in

  try
    match List.map resolve syms with
    | []   -> t_repeat t_subst tc
    | syms ->
        FApi.t_seqs
          (List.map
            (fun var tc -> t_subst ~exn:(NothingToSubstitute var) ~var tc)
            syms)
          tc

    with NothingToSubstitute v ->
      tc_error_lazy !!tc (fun fmt ->
        let ppe = EcPrinting.PPEnv.ofenv (FApi.tc1_env tc) in
        Format.fprintf fmt "nothing to substitute for `%a'"
        (EcPrinting.pp_vsubst ppe) v
      )

(* -------------------------------------------------------------------- *)
type cut_t = intropattern * pformula * (ptactics located) option
type cutmode  = [`Have | `Suff]

let process_cut ?(mode = `Have) engine ttenv ((ip, phi, t) : cut_t) tc =
  let phi = TTC.tc1_process_formula tc phi in
  let tc  = EcLowGoal.t_cut phi tc in

  let applytc tc =
    t |> ofold (fun t tc ->
      let t = mk_loc (loc t) (Pby (Some (unloc t))) in
      t_onall (engine t) tc) (FApi.tcenv_of_tcenv1 tc)
  in

  match mode with
  | `Have ->
     FApi.t_first applytc
       (FApi.t_last (process_intros_1 ttenv ip) tc)

  | `Suff ->
     FApi.t_rotate `Left 1
       (FApi.t_on1 0 t_id ~ttout:applytc
         (FApi.t_last (process_intros_1 ttenv ip) tc))

(* -------------------------------------------------------------------- *)
type cutdef_t = intropattern * pcutdef

let cutsolver (ttenv : ttenv) =
  { smt = process_smt ttenv None; done_ = process_trivial; }

let process_cutdef ttenv (ip, pt) (tc : tcenv1) =
  let pt = {
      fp_mode = `Implicit;
      fp_head = FPNamed (pt.ptcd_name, pt.ptcd_tys);
      fp_args = pt.ptcd_args;
  } in

  let pt = PT.tc1_process_full_pterm tc pt in

  if not (PT.can_concretize pt.ptev_env) then
    tc_error !!tc "cannot infer all placeholders";

  let pt, ax = PT.concretize pt in

  FApi.t_sub
    [EcLowGoal.t_apply ~cutsolver:(cutsolver ttenv) pt; process_intros_1 ttenv ip]
    (t_cut ax tc)

(* -------------------------------------------------------------------- *)
let process_left (tc : tcenv1) =
  try
    t_ors [EcLowGoal.t_left; EcLowGoal.t_or_intro_prind `Left] tc
  with InvalidGoalShape ->
    tc_error !!tc "cannot apply `left` on that goal"

(* -------------------------------------------------------------------- *)
let process_right (tc : tcenv1) =
  try
    t_ors [EcLowGoal.t_right; EcLowGoal.t_or_intro_prind `Right] tc
  with InvalidGoalShape ->
    tc_error !!tc "cannot apply `right` on that goal"

(* -------------------------------------------------------------------- *)
let process_split ?(i : int option) (tc : tcenv1) =
  let tactics : FApi.backward list =
    match i with
    | None -> [EcLowGoal.t_split; EcLowGoal.t_split_prind]
    | Some i -> [EcLowGoal.t_split ~i] in

  try  t_ors tactics tc
  with InvalidGoalShape ->
    tc_error !!tc
      "cannot apply `split/%a` on that goal"
      (EcPrinting.pp_opt Format.pp_print_int) i

(* -------------------------------------------------------------------- *)
let process_elim (pe, qs) tc =
  let doelim tc =
    match qs with
    | None    -> t_or (t_elimT_ind `Ind) t_elim tc
    | Some qs ->
        let qs = {
            fp_mode = `Implicit;
            fp_head = FPNamed (qs, None);
            fp_args = [];
        } in process_elimT qs tc
  in
    try
      FApi.t_last doelim (process_move [] pe tc)
    with EcCoreGoal.InvalidGoalShape ->
      tc_error !!tc "don't know what to eliminate"

(* -------------------------------------------------------------------- *)
let process_case ?(doeq = false) gp tc =
  let module E = struct exception LEMFailure end in

  try
    match gp.pr_rev with
    | { pr_genp = [`Form (None, pf)] }
        when List.is_empty gp.pr_view ->

        let env = FApi.tc1_env tc in

        let f =
          try  TTC.process_formula (FApi.tc1_hyps tc) pf
          with TT.TyError _ | LocError (_, TT.TyError _) -> raise E.LEMFailure
        in
          if not (EcReduction.EqTest.for_type env f.f_ty tbool) then
            raise E.LEMFailure;
          begin
            match (fst (destr_app f)).f_node with
            | Fop (p, _) when EcEnv.Op.is_prind env p ->
               raise E.LEMFailure
            | _ -> ()
          end;
          t_seqs
            [process_clear (`Include gp.pr_rev.pr_clear); t_case f;
             t_simplify_with_info EcReduction.betaiota_red]
            tc

    | _ -> raise E.LEMFailure

  with E.LEMFailure ->
    try
      FApi.t_last
        (t_ors [t_elimT_ind `Case; t_elim; t_elim_prind `Case])
        (process_move ~doeq gp.pr_view gp.pr_rev tc)

    with EcCoreGoal.InvalidGoalShape ->
      tc_error !!tc "don't known what to eliminate"

(* -------------------------------------------------------------------- *)
let process_exists args (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let pte  = (TTC.unienv_of_hyps hyps, EcMatching.MEV.empty) in
  let pte  = PT.ptenv !!tc (FApi.tc1_hyps tc) pte in

  let for1 concl arg =
    match TTC.destruct_exists hyps concl with
    | None -> tc_error !!tc "not an existential"
    | Some (`Exists (x, xty, f)) ->
        let arg =
          match xty with
          | GTty    _ -> trans_pterm_arg_value pte arg
          | GTmem   _ -> trans_pterm_arg_mem   pte arg
          | GTmodty _ -> trans_pterm_arg_mod   pte arg
        in
          PT.check_pterm_arg pte (x, xty) f arg.ptea_arg
  in

  let _concl, args = List.map_fold for1 (FApi.tc1_goal tc) args in

  if not (PT.can_concretize pte) then
    tc_error !!tc "cannot infer all placeholders";

  let pte  = PT.concretize_env pte in
  let args = List.map (PT.concretize_e_arg pte) args in

  EcLowGoal.t_exists_intro_s args tc

(* -------------------------------------------------------------------- *)
let process_congr tc =
  let (env, hyps, concl) = FApi.tc1_eflat tc in

  if not (EcFol.is_eq_or_iff concl) then
    tc_error !!tc "goal must be an equality or an equivalence";

  let ((f1, f2), iseq) =
    if   EcFol.is_eq concl
    then (EcFol.destr_eq  concl, true )
    else (EcFol.destr_iff concl, false) in

  let t_ensure_eq =
    if iseq then t_id
    else
      (fun tc ->
        let hyps = FApi.tc1_hyps tc in
        EcLowGoal.Apply.t_apply_bwd_r
          (PT.pt_of_uglobal !!tc hyps LG.p_eq_iff) tc) in

  let t_subgoal = t_ors [t_reflex ~mode:`Alpha; t_assumption `Alpha; t_id] in

  match f1.f_node, f2.f_node with
  | _, _ when EcReduction.is_alpha_eq hyps f1 f2 ->
      FApi.t_seq t_ensure_eq EcLowGoal.t_reflex tc

  | Fapp (o1, a1), Fapp (o2, a2)
      when    EcReduction.is_alpha_eq hyps o1 o2
           && List.length a1 = List.length a2 ->

      let tt1 = t_congr (o1, o2) ((List.combine a1 a2), f1.f_ty) in
      FApi.t_seqs [t_ensure_eq; tt1; t_subgoal] tc

  | Fif (_, { f_ty = cty }, _), Fif _ ->
     let tt0 tc =
       let hyps = FApi.tc1_hyps tc in
       EcLowGoal.Apply.t_apply_bwd_r
         (PT.pt_of_global !!tc hyps LG.p_if_congr [cty]) tc
     in FApi.t_seqs [tt0; t_subgoal] tc

  | Ftuple _, Ftuple _ when iseq ->
      FApi.t_seqs [t_split; t_subgoal] tc

  | Fproj (f1, i1), Fproj (f2, i2)
      when i1 = i2 && EcReduction.EqTest.for_type env f1.f_ty f2.f_ty
    -> EcCoreGoal.FApi.xmutate1 tc `CongrProj [f_eq f1 f2]

  | _, _ -> tacuerror "not a congruence"

(* -------------------------------------------------------------------- *)
let process_wlog ids wlog tc =
  let hyps, _ = FApi.tc1_flat tc in

  let toid s =
    if not (LDecl.has_name (unloc s) hyps) then
      tc_lookup_error !!tc ~loc:s.pl_loc `Local ([], unloc s);
    fst (LDecl.by_name (unloc s) hyps) in

  let ids = List.map toid ids in

  let gen =
    let wlog = TTC.tc1_process_formula tc wlog in
    let tc   = t_rotate `Left 1 (EcLowGoal.t_cut wlog tc) in
    let tc   = t_first (t_generalize_hyps ~clear:`Yes ids) tc in
    FApi.tc_goal tc
  in

  t_rotate `Left 1
    (t_first
       (t_seq (t_clears ids) (t_intros_i ids))
       (t_cut gen tc))

(* -------------------------------------------------------------------- *)
let process_wlog_suff ids wlog tc =
  let hyps, _ = FApi.tc1_flat tc in

  let toid s =
    if not (LDecl.has_name (unloc s) hyps) then
      tc_lookup_error !!tc ~loc:s.pl_loc `Local ([], unloc s);
    fst (LDecl.by_name (unloc s) hyps) in

  let ids = List.map toid ids in

  let wlog =
    let wlog = TTC.tc1_process_formula tc wlog in
    let tc   = t_first (t_generalize_hyps ~clear:`Yes ids) (t_cut wlog tc) in
    FApi.tc_goal tc in

  t_rotate `Left 1
    (t_first
       (t_seq (t_clears ids) (t_intros_i ids))
       (t_cut wlog tc))

(* -------------------------------------------------------------------- *)
let process_wlog ~suff ids wlog tc =
  if   suff
  then process_wlog_suff ids wlog tc
  else process_wlog ids wlog tc

(* -------------------------------------------------------------------- *)
let process_genhave (ttenv : ttenv) ((name, ip, ids, gen) : pgenhave) tc =
  let hyps, _ = FApi.tc1_flat tc in

  let toid s =
    if not (LDecl.has_name (unloc s) hyps) then
      tc_lookup_error !!tc ~loc:s.pl_loc `Local ([], unloc s);
    fst (LDecl.by_name (unloc s) hyps) in

  let ids = List.map toid ids in

  let gen =
    let gen = TTC.tc1_process_formula tc gen in
    let tc  = EcLowGoal.t_cut gen tc in
    let tc  = t_first (t_generalize_hyps ~clear:`Yes ids) tc in
    FApi.tc_goal tc in

  let doip tc =
    let genid = EcIdent.create (unloc name) in
    let tc = t_intros_i_1 [genid] tc in

    match ip with
    | None ->
        t_id tc

    | Some ip ->
        let pt = EcProofTerm.pt_of_hyp !!tc (FApi.tc1_hyps tc) genid in
        let pt = List.fold_left EcProofTerm.apply_pterm_to_local pt ids in
        let tc = t_cutdef pt.ptev_pt pt.ptev_ax tc in
        process_mintros ttenv [ip] tc in

  t_sub [
      t_seq (t_clears ids) (t_intros_i ids);
      doip
  ] (t_cut gen tc)
