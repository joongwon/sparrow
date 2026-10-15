type snapshot = {
  global : Global.t;
  input_table : ItvDom.Table.t;
  output_table : ItvDom.Table.t;
}
(** Interactive inspection of saved interval-analysis states. *)

val state : snapshot option ref
(** The current snapshot; [None] before [load]. *)

val load : ?prefix:string -> string -> unit
(** [load ~prefix dir] reads [dir/prefix.itv.{global,input,output}]. The default
    prefix is [merged]. A failed load preserves the previous state. *)

val current : unit -> snapshot
val functions : unit -> string list
val nodes : ?func:string -> unit -> InterCfg.Node.t list

val node : string -> InterCfg.Node.t
(** Find an exact [InterCfg.Node.to_string] name, as displayed by sparrow-vis.
*)

val input : InterCfg.Node.t -> ItvDom.Mem.t

val output : InterCfg.Node.t -> ItvDom.Mem.t
(** Return the saved sparse memory. Fail if the node has no recorded entry. *)

val command : InterCfg.Node.t -> IntraCfg.cmd
(** The CFG command, also available for nodes without recorded states. *)

val location : InterCfg.Node.t -> GoblintCil.Cil.location option
(** The command's saved source location, or [None] when unavailable (e.g. skip,
    entry and exit nodes). Paths are preserved as recorded in the snapshot. *)

val pp_command : Format.formatter -> IntraCfg.cmd -> unit

val pp_location : Format.formatter -> GoblintCil.Cil.location -> unit
(** Toplevel printers; locations display as [file:line]. *)
