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
(** Pre-analysis to compute accessibility *)

module type S =
sig
  module Dom : InstrumentedMem.S
  module Loc : AbsDom.SET
  module PowLoc : PowDom.CPO
  module Access : Access.S with type Loc.t = Loc.t
    and type PowLoc.t = PowLoc.t
  val node_access : Global.t -> PowLoc.t -> (BasicDom.Node.t -> Dom.t * Global.t -> Dom.t * Global.t) -> Dom.t
    -> BasicDom.Node.t list -> (BasicDom.Node.t * Access.info) list
  (** The locations of the given set each given node defines and uses when
      the step runs it on the given memory *)
  val summarize : Global.t -> (BasicDom.Node.t * Access.info) list -> Access.t
  (** The access of the program from the accesses of its nodes: per procedure,
      reachable through calls, procedure- and program-local, and the
      definition and use nodes of each location *)
  val perform : Global.t -> PowLoc.t -> (BasicDom.Node.t -> Dom.t * Global.t -> Dom.t * Global.t) -> Dom.t -> Access.t
  (** [summarize] of [node_access] of every node *)
end

module Make(AccessSem : AccessSem.S) : S
  with type Dom.t = AccessSem.Dom.t
  and type Loc.t = AccessSem.Dom.A.t
  and type PowLoc.t = AccessSem.Dom.PowA.t
  and type Access.t = AccessSem.Dom.Access.t
  and type Access.Info.t = AccessSem.Dom.Access.Info.t
