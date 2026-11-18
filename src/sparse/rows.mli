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
(** The memories of the widening phase in rows indexed by node *)

module type S = sig
  module Dom : InstrumentedMem.S

  module DUGraph :
    Dug.S with type Loc.t = Dom.A.t and type PowLoc.t = Dom.PowA.t

  module Worklist : Worklist.S with type DUGraph.t = DUGraph.t

  type t

  val make :
    BasicDom.Node.t array ->
    DUGraph.t ->
    defined:(BasicDom.Node.t -> Dom.PowA.t) ->
    t
  (** The rows of the given nodes (all those of the graph) on the graph. A
      node's routes are its outgoing edges by target; its cells are the
      locations on them; [defined] bounds what its transfer writes. *)

  val index : t -> BasicDom.Node.t -> int
  val node : t -> int -> BasicDom.Node.t
  val inputs : t -> Dom.t array
  val outputs : t -> Dom.t array

  val update :
    t ->
    Worklist.t ref ->
    int ->
    (Dom.t * Global.t -> Dom.t * Global.t) ->
    Global.t ->
    Global.t
  (** [update rows works i step global]: the visit of node [i] by [step] from
      its input. The cells whose value rose are stored in its output (widened
      when the node is a loop head of [works]) and joined into the input of
      every target whose route carries them; a target whose input grew is queued
      in [works] once per visit. The global state is the step's when the output
      changed. *)
end

module Make
    (Dom : InstrumentedMem.S)
    (DUGraph : Dug.S with type Loc.t = Dom.A.t and type PowLoc.t = Dom.PowA.t)
    (Worklist : Worklist.S with type DUGraph.t = DUGraph.t) :
  S
    with module Dom = Dom
     and module DUGraph = DUGraph
     and module Worklist = Worklist
