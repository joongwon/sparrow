(** Interactive inspection of saved interval-analysis states. *)
type snapshot = {
  global : Global.t;
  input_table : ItvDom.Table.t;
  output_table : ItvDom.Table.t;
}

val state : snapshot option ref
(** The current snapshot; [None] before [load]. *)

val load : ?prefix:string -> string -> unit
(** [load ~prefix dir] reads [dir/prefix.itv.{global,input,output}].
    The default prefix is [merged]. A failed load preserves the previous state. *)

val current : unit -> snapshot
val functions : unit -> string list
val nodes : ?func:string -> unit -> InterCfg.Node.t list
val node : string -> InterCfg.Node.t
(** Find an exact [InterCfg.Node.to_string] name, as displayed by sparrow-vis. *)

val input : InterCfg.Node.t -> ItvDom.Mem.t
val output : InterCfg.Node.t -> ItvDom.Mem.t
(** Return the saved sparse memory. Fail if the node has no recorded entry. *)
