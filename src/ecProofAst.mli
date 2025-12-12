(* -------------------------------------------------------------------- *)
val enable : source:string -> unit

(* Reset collected data for a new processing run (e.g. after restart). *)
val reset_run : unit -> unit

(* -------------------------------------------------------------------- *)
val is_enabled : unit -> bool

(** Output configuration toggles. *)
val set_include_intros : bool -> unit
val set_include_emacs_goals : bool -> unit
val set_include_serialized_goals : bool -> unit

(** Intro-pattern instrumentation. *)
type intro_token =
  [ `Core of EcParsetree.ipcore EcLocation.located list
  | `Dup
  | `Done of [`Default | `Variant] option
  | `Smt of (bool * EcParsetree.pprover_infos)
  | `Clear of EcParsetree.psymbol list
  | `Case of EcParsetree.icasemode * EcParsetree.intropattern list
  | `Rw of (EcParsetree.rwocc * EcParsetree.rwside * (int option) option)
  | `Delta of ((EcParsetree.rwside * EcParsetree.rwocc) * EcParsetree.pformula)
  | `View of EcParsetree.ppterm
  | `Subst of (EcParsetree.rwside * (int option) option)
  | `SubstTop of (int option * [`LtoR | `RtoL] option)
  | `Simpl of [`Default | `Variant]
  | `Crush of EcParsetree.crushmode
  ]

type intro_element =
  | IEPattern of intro_token EcLocation.located
  | IEGen of EcParsetree.prevert
  | IEBridge

(** Instrumentation hooks used while executing tactics. *)
val begin_tactic_trace : unit -> unit
val end_tactic_trace : success:bool -> unit
val log_tactic_application :
  EcParsetree.ptactic ->
  EcCoreGoal.handle list ->
  EcCoreGoal.handle list ->
  unit
val log_intro_application :
  EcParsetree.ptactic ->
  int ->
  EcCoreGoal.handle list ->
  EcCoreGoal.handle list ->
  unit
val log_intro_element :
  EcParsetree.ptactic ->
  int ->
  intro_element ->
  EcCoreGoal.handle list ->
  EcCoreGoal.handle list ->
  unit
val log_rewrite_application :
  EcParsetree.ptactic ->
  int ->
  string option ->
  string list ->
  EcCoreGoal.handle list ->
  EcCoreGoal.handle list ->
  unit
val log_apply_application :
  EcParsetree.ptactic ->
  int ->
  string option ->
  string list ->
  EcCoreGoal.handle list ->
  EcCoreGoal.handle list ->
  unit
val update_active_goals : EcCoreGoal.handle list -> unit

(* -------------------------------------------------------------------- *)
val record_clone :
  theory:EcParsetree.theory_cloning ->
  base:string ->
  target:string ->
  unit

val record_block :
  lemma:EcDecl.axiom ->
  lemma_name:EcSymbols.symbol option ->
  lemma_path:string ->
  tactics:EcParsetree.ptactic list -> unit

(* -------------------------------------------------------------------- *)
type completion = [ `Qed | `Admitted | `Aborted ]

val mark_status :
  lemma:EcDecl.axiom ->
  lemma_name:EcSymbols.symbol option ->
  lemma_path:string ->
  status:completion -> unit

(* -------------------------------------------------------------------- *)
val finalize : unit -> unit

