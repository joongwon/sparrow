(***********************************************************************)
(*                                                                     *)
(* Copyright (c) 2007-present.                                         *)
(* Programming Research Laboratory (ROPAS), Seoul National University. *)
(* All rights reserved.                                                *)
(*                                                                     *)
(* This software is distributed under the term of the BSD license.     *)
(* See the LICENSE file for details.                                   *)
(*                                                                     *)
(***********************************************************************)

val last_pre_iters : int ref

(** The rounds of the flow-insensitive analysis over the given nodes from the
    given memory: round [k] applies [step ~round:k] to every node in order and
    then [widen ~round:k] to the memories before and after the round.  Returns
    the memory, the global state and the number of rounds. *)
val fixpoint :
  step:(round:int -> 'node -> ItvDom.Mem.t * Global.t -> ItvDom.Mem.t * Global.t) ->
  widen:(round:int -> ItvDom.Mem.t -> ItvDom.Mem.t -> ItvDom.Mem.t) ->
  'node list -> ItvDom.Mem.t -> Global.t -> ItvDom.Mem.t * Global.t * int

(** The fixpoint memory with the call edges and the call graph of the callees
    that [callees] gives at the given nodes *)
val finish :
  callees:(BasicDom.Node.t -> ItvDom.Mem.t -> BasicDom.PowProc.t) ->
  BasicDom.Node.t list -> ItvDom.Mem.t -> Global.t -> Global.t

val perform : Global.t -> Global.t
