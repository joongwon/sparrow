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
module type S =
sig
  module Access : Access.S
  module DUGraph : Dug.S
  module PowLoc : PowDom.CPO
  type node = BasicDom.Node.t
  type loc
  type routing
  val carried           : Global.t -> Access.t -> frame_locals:PowLoc.t -> InterCfg.pid -> PowLoc.t * PowLoc.t
  (** The locations (defined, used) the call edges of a procedure carry: a non-recursive
      procedure its reach without the proc-locals of itself and its callees,
      a recursive one its reach without the proc-locals of the non-recursive
      procedures and the frame locals (FrameLocal) *)
  val routing           : Global.t -> Access.t -> frame_locals:PowLoc.t
    -> variable:(loc -> (InterCfg.pid * string) option) -> PowLoc.t -> routing
  (** The routing of the given locations through the def-use chains of the
      program; the edges of a call carry [carried] of the callee among them,
      without the variables ([variable]: the procedure and name of the
      variable a location is rooted at) of the procedures no activation of
      which is live at the call, those not reaching the caller; the callee's
      formals stay on the edge to its entry and its return variable on the
      edge from its exit. *)
  val route             : routing -> InterCfg.pid -> DUGraph.t -> DUGraph.t
  (** The def-use edges inside a procedure *)
  val route_call        : routing -> node -> DUGraph.t -> DUGraph.t
  (** The def-use edges of a call node: to its callees' entries and from their
      exits to its return node *)
  val single_definitions : Access.t -> PowLoc.t -> node list -> DUGraph.t -> DUGraph.t
  (** The edges from the definition of each single-definition location of the
      set to its uses, among the given nodes *)
  val bypass            : Access.t -> DUGraph.t -> DUGraph.t
  (** The bypass of every node of the graph, in canonical key order
      (CanonOrder) *)
  val make              : ?skip_nodes : BasicDom.Node.t BatSet.t -> frame_locals:PowLoc.t
    -> variable:(loc -> (InterCfg.pid * string) option) -> Global.t * Access.t * PowLoc.t -> DUGraph.t
  (** The routing of the locations without a single definition, the single
      definitions' edges and the bypass, over the whole program *)
  val to_json_intra     : DUGraph.t -> Access.t -> Yojson.Safe.t
  val to_json_inter     : DUGraph.t -> Access.t -> Yojson.Safe.t
end

module Make (DUGraph : Dug.S) (Access: Access.S
    with type Loc.t = DUGraph.Loc.t and type PowLoc.t = DUGraph.PowLoc.t): S
  with type Access.t = Access.t
  and type DUGraph.t = DUGraph.t
  and type PowLoc.t = DUGraph.PowLoc.t
  and type loc = DUGraph.Loc.t
