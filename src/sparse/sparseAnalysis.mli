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
(** Sparse analysis framework *)

module type S = sig
  module Dom : InstrumentedMem.S

  module DUGraph :
    Dug.S with type Loc.t = Dom.A.t and type PowLoc.t = Dom.PowA.t

  module Worklist : Worklist.S with type DUGraph.t = DUGraph.t

  module Table :
    MapDom.CPO
      with type t = MapDom.MakeCPO(BasicDom.Node)(Dom).t
       and type A.t = BasicDom.Node.t
       and type B.t = Dom.t

  module Spec :
    Spec.S
      with type Dom.t = Dom.t
       and type Dom.A.t = Dom.A.t
       and type Dom.PowA.t = Dom.PowA.t

  module Rows :
    Rows.S
      with module Dom = Dom
       and module DUGraph = DUGraph
       and module Worklist = Worklist

  type analysis_state = Worklist.t * Global.t

  type step = BasicDom.Node.t -> Dom.t * Global.t -> Dom.t * Global.t
  (** The transfer of a node; [Sem.run Strong spec] in [perform] *)

  type visit = DUGraph.t -> DUGraph.node -> analysis_state -> analysis_state
  (** A visit of a node in the widening phase *)

  val frame_locals_of :
    (Global.t ->
    defs_at:(BasicDom.Node.t -> Dom.PowA.t) ->
    proc_local:(InterCfg.pid -> Dom.PowA.t) ->
    Dom.PowA.t)
    ref
  (** The program's frame locals (FrameLocal) from the global state, the
      definitions of a node and a procedure's proc-local locations, computed
      after the access analysis; none by default. *)

  val variable_of : (Dom.A.t -> (InterCfg.pid * string) option) ref
  (** The procedure and name of the variable a location is rooted at, for the
      def-use routing (SsaDug); the interval instance sets it. *)

  val analyze_node : Rows.t -> step -> visit
  (** The visit by the given step on the rows (Rows.update), its deliveries
      queueing the successors whose input grew *)

  val widening :
    visit ->
    DUGraph.t ->
    DUGraph.node BatSet.t ->
    analysis_state ->
    analysis_state
  (** The widening phase on the def-use graph from the given nodes and the
      state's worklist *)

  val perform_with :
    (Rows.t -> visit) -> Spec.t -> Global.t -> Global.t * Table.t * Table.t
  (** [perform] with the given visit on the rows of the def-use graph, whose
      transfers write only their access definitions *)

  val perform : Spec.t -> Global.t -> Global.t * Table.t * Table.t
end

module Make (Sem : AbsSem.S) :
  S
    with type Dom.t = Sem.Dom.t
     and type Dom.A.t = Sem.Dom.A.t
     and type Dom.PowA.t = Sem.Dom.PowA.t
     and type Spec.t = Sem.Spec.t

module MakeWithAccess (Sem : AccessSem.S) :
  S
    with type Dom.t = Sem.Dom.t
     and type Dom.A.t = Sem.Dom.A.t
     and type Dom.PowA.t = Sem.Dom.PowA.t
     and type Spec.t = Sem.Spec.t
