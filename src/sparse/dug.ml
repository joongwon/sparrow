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
open Vocab
open Yojson.Safe
open Global
open IntraCfg
open InterCfg
open BasicDom

(* Label interning.  A def-use graph's labels are built one
   location at a time per edge, so edges with the same location set hold
   separate trees; most of the label mass of a large program repeats sets
   that already exist (recursive procedures carry their component's whole
   reach set at every call site).  [intern] returns the resident label with
   the same elements -- in the same (sorted) order, each [E.equal] to the
   argument's, so in particular the same representative of every location --
   or makes the argument resident.  The resident is interchangeable with the
   argument for every set operation; only the physical identity of the
   tree nodes (and possibly the tree's shape, never its elements) differs.
   Residents are held weakly: a label no edge holds any more is collected. *)
module Label_intern_stats = struct
  let calls = ref 0
  let shared = ref 0
end

module Label_intern (P : PowDom.CPO) (E : sig
  val equal : P.elt -> P.elt -> bool
  val hash : P.elt -> int
end) =
struct
  let hash set = P.fold (fun e h -> HashconsKey.mix h (E.hash e)) set 0

  let equal a b =
    a == b ||
    let n = P.cardinal a in
    n = P.cardinal b &&
    (n = 0 ||
     let elements = Array.make n (P.choose a) in
     let i = ref 0 in
     P.iter (fun e -> elements.(!i) <- e; incr i) a;
     i := 0;
     try P.iter (fun e -> if not (E.equal elements.(!i) e) then raise Exit; incr i) b; true
     with Exit -> false)

  module W = Weak.Make (struct type t = P.t let equal = equal let hash = hash end)
  let table = W.create 4096

  let intern set =
    if P.is_empty set then set
    else begin
      let resident = W.merge table set in
      incr Label_intern_stats.calls;
      if resident != set then incr Label_intern_stats.shared;
      resident
    end
end

module type S =
sig
  type t
  type node = BasicDom.Node.t
  module Loc : AbsDom.SET
  module PowLoc : PowDom.CPO with type elt = Loc.t

  val create            : ?size : int -> unit -> t
  val nb_node           : t -> int
  val nb_edge           : t -> int
  val nb_loc            : t -> int
  val nodesof           : t -> node BatSet.t

  val succ              : node -> t -> node list
  val pred              : node -> t -> node list

  val add_node          : node -> t -> t
  val add_edge          : node -> node -> t -> t
  val remove_node       : node -> t -> t
  val get_abslocs       : node -> node -> t -> PowLoc.t
  val add_absloc        : node -> Loc.t -> node -> t -> t
  val add_abslocs       : node -> PowLoc.t -> node -> t -> t
  val remove_absloc     : node -> Loc.t -> node -> t -> t
  val remove_abslocs    : node -> PowLoc.t -> node -> t -> t
  val compact           : t -> t

(** {2 Iterator } *)

  val fold_node         : (node -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_edges        : (node -> node -> 'a -> 'a) -> t -> 'a -> 'a
  val iter_edges        : (node -> node -> unit) -> t -> unit
  val fold_succ         : (node -> 'a ->'a) -> t -> node -> 'a -> 'a

(** {2 Print } *)

  val to_dot            : t -> string
  val to_json           : t -> Yojson.Safe.t
end

module MakeSet (Dom : InstrumentedMem.S) =
struct
  type node = BasicDom.Node.t
  module PowLoc = Dom.PowA
  module Loc = Dom.A
  type loc = Loc.t
  type locset = PowLoc.t
  module G =
  struct
    module I = Graph.Imperative.Digraph.ConcreteBidirectional (BasicDom.Node)
    (* An edge's label, and whether it changed since the last [compact]
       (then it is on [dirty]). *)
    type entry = { mutable locs : locset; mutable pending : bool }
    type t = { graph : I.t; label : ((node * node), entry) Hashtbl.t; mutable dirty : entry list }
    let create ~size () = { graph = I.create ~size (); label = Hashtbl.create (2 * size); dirty = [] }

    let succ g n = I.succ g.graph n
    let pred g n = I.pred g.graph n
    let nb_vertex g = I.nb_vertex g.graph
    let pred_e g n = I.pred g.graph n |> List.map (fun p -> (p, (Hashtbl.find g.label (p,n)).locs, n))
    let fold_vertex f g a = I.fold_vertex f g.graph a
    let fold_edges f g a = I.fold_edges f g.graph a
    let iter_edges f g = I.iter_edges f g.graph
    let fold_succ f g a = I.fold_succ f g.graph a

    let touch g e = if not e.pending then begin e.pending <- true; g.dirty <- e :: g.dirty end
    (* [Hashtbl.replace] of the label row *)
    let set_label g key locs =
      match Hashtbl.find_opt g.label key with
      | Some e -> e.locs <- locs; touch g e
      | None -> let e = { locs; pending = false } in Hashtbl.add g.label key e; touch g e

    let add_vertex g n = I.add_vertex g.graph n; g
    let remove_vertex g n = I.remove_vertex g.graph n; g
    let add_edge g s d = I.add_edge g.graph s d; g
    let add_edge_e g (s,locs,d) =
      set_label g (s,d) locs;
      add_edge g s d
    let remove_edge g s d = I.remove_edge g.graph s d; Hashtbl.remove g.label (s,d); g
    let find_label g s d = (Hashtbl.find g.label (s,d)).locs
    let modify_edge_def def g s d f =
      match Hashtbl.find_opt g.label (s,d) with
      | Some e -> e.locs <- f e.locs; touch g e; g
      | None -> add_edge_e g (s, def, d)
  end

  type t = G.t

  let create ?(size=0) () = G.create ~size ()
  let nodesof dug = G.fold_vertex BatSet.add dug BatSet.empty

  let succ n dug = try G.succ dug n with _ -> []
  let pred n dug = try G.pred dug n with _ -> []
  let nb_node dug = G.nb_vertex dug
  let nb_edge dug = G.fold_edges (fun _ _ n -> n + 1) dug 0

  let remove_node : node -> t -> t
  =fun n dug -> G.remove_vertex dug n

  let add_node : node -> t -> t
  =fun n dug -> G.add_vertex dug n

  let add_edge : node -> node -> t -> t
  =fun src dst dug -> G.add_edge dug src dst

  let remove_edge : node -> node -> t -> t
  =fun src dst dug -> try G.remove_edge dug src dst with _ -> dug

  let get_abslocs : node -> node -> t -> locset
  =fun src dst dug -> try G.find_label dug src dst with _ -> PowLoc.empty

  let add_edge_e dug e = G.add_edge_e dug e

  let add_absloc : node -> Loc.t -> node -> t -> t
  =fun src x dst dug ->
    G.modify_edge_def (PowLoc.singleton x) dug src dst (PowLoc.add x)

  (* A label is interned at compaction, not at each change *)
  let add_abslocs : node -> locset -> node -> t -> t
  =fun src xs dst dug ->
    if PowLoc.is_empty xs then dug else
    G.modify_edge_def xs dug src dst (PowLoc.union_unshared xs)

  let replace_or_remove_abslocs src dst locs dug =
    if PowLoc.is_empty locs then remove_edge src dst dug
    else begin
      G.set_label dug (src, dst) locs;
      dug
    end

  let remove_absloc : node -> Loc.t -> node -> t -> t
  =fun src x dst dug ->
    try
      let locs = PowLoc.remove x (G.find_label dug src dst) in
      replace_or_remove_abslocs src dst locs dug
    with _ -> dug

  let remove_abslocs : node -> locset -> node -> t -> t
  =fun src xs dst dug ->
    if PowLoc.is_empty xs then dug else
    try
      let locs = PowLoc.diff (G.find_label dug src dst) xs in
      replace_or_remove_abslocs src dst locs dug
    with _ -> dug

  (* Label interning (Label_intern): the labels changed since the last
     compaction -- one procedure's intra-procedural edges when SsaDug
     compacts after each procedure, the rest at the final compaction -- each
     become the resident label with the same elements, element for element
     the same physical location.  Such a label is interchangeable with the
     edge's own for every operation but [==] on the set's tree nodes. *)
  module Intern = Label_intern (PowLoc) (struct
    let equal = ( == )
    let hash = (HashconsKey.find Loc.compare).HashconsKey.hash
  end)

  let compact dug =
    List.iter (fun e -> e.G.pending <- false; e.G.locs <- Intern.intern e.G.locs) dug.G.dirty;
    dug.G.dirty <- [];
    dug

  let fold_node = G.fold_vertex
  let fold_edges = G.fold_edges
  let iter_edges = G.iter_edges
  let fold_succ = G.fold_succ

  let nb_loc dug =
    fold_edges (fun src dst size ->
      PowLoc.cardinal (get_abslocs src dst dug) + size
    ) dug 0

  let succ_e : node -> t -> (node * locset) list
  =fun n g -> List.map (fun s -> (s, get_abslocs n s g)) (succ n g)

  let pred_e : node -> t -> (node * locset) list
  =fun n g -> List.map (fun p -> (p, get_abslocs p n g)) (pred n g)

  let to_dot : t -> string
  =fun dug ->
    "digraph dugraph {\n" ^
    fold_edges (fun src dst str ->
      let addrset = get_abslocs src dst dug in
        str ^ "\"" ^ (BasicDom.Node.to_string src) ^ "\"" ^ " -> " ^
              "\"" ^ (BasicDom.Node.to_string dst) ^ "\"" ^
              "[label=\"{" ^
                PowLoc.fold (fun addr s -> (Loc.to_string addr)^","^s) addrset "" ^
              "}\"]" ^ ";\n"
    ) dug ""
    ^ "}"

  let to_json : t -> Yojson.Safe.t
  = fun g ->
    let nodes = `List (fold_node (fun v nodes ->
                  (`String (BasicDom.Node.to_string v))::nodes) g [])
    in
    let edges = `List (fold_edges (fun src dst edges ->
                  let addrset = get_abslocs src dst g in
                  (`List [`String (BasicDom.Node.to_string src); `String (BasicDom.Node.to_string dst);
                          `String (PowLoc.fold (fun addr s -> (Loc.to_string addr)^","^s) addrset "")])
                  ::edges) g [])
    in
    `Assoc [("nodes", nodes); ("edges", edges)]
end

module Make = MakeSet
