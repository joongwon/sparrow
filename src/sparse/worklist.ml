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
open Dug
open BasicDom
open AbsDom

module type S = sig
  module DUGraph : Dug.S

  type t

  type order_entry = {
    node : BasicDom.Node.t;
    order : int;
    rank : int;
    loop_header : bool;
    head_order : int option;
  }

  type snapshot = {
    order : order_entry list;
    sccs : BasicDom.Node.t list list;
    loop_headers : BasicDom.Node.t list;
  }

  val init : DUGraph.t -> t
  val pick : t -> (BasicDom.Node.t * t) option
  val push_init : BasicDom.Node.t BatSet.t -> t -> t
  val push : BasicDom.Node.t -> BasicDom.Node.t -> t -> t
  val push_set : BasicDom.Node.t -> BasicDom.Node.t BatSet.t -> t -> t
  val is_loopheader : BasicDom.Node.t -> t -> bool
  val snapshot : t -> snapshot
end

module Make (DUGraph : Dug.S) = struct
  module DUGraph = DUGraph

  module Workorder = struct
    module H = Hashtbl.Make (Node)

    (* A node's order, head flag, canonical rank and head order (-1: none) *)
    type entry = { order : int; head : bool; rank : int; head_order : int }
    type t = { entries : entry H.t; sccs : DUGraph.node list list }

    let is_loopheader here info =
      match H.find_opt info.entries here with Some e -> e.head | None -> false

    (* The canonical weak topological order (CanonOrder): nodes numbered by
       their canonical key, the graph of the def-use edges that carry a
       location, Sparrow's recursive decomposition with key-order
       enumeration and key-order head tie-break.  Edge-isolated nodes get
       trailing orders in key order. *)
    let perform g =
      let nodes =
        DUGraph.fold_node (fun n acc -> (CanonOrder.key_of n, n) :: acc) g []
        |> List.sort (fun (a, n) (b, m) ->
            let c = CanonOrder.compare_key a b in
            if c <> 0 then c else Node.compare n m)
        |> List.map snd |> Array.of_list
      in
      let count = Array.length nodes in
      let index = Hashtbl.create ((2 * count) + 1) in
      Array.iteri (fun i n -> Hashtbl.replace index n i) nodes;
      let outgoing = Array.make count [] and touched = Array.make count false in
      Profiler.start_event "Worklist.graph";
      DUGraph.iter_edges
        (fun src dst ->
          if not (DUGraph.PowLoc.is_empty (DUGraph.get_abslocs src dst g)) then begin
            let s = Hashtbl.find index src and d = Hashtbl.find index dst in
            outgoing.(s) <- d :: outgoing.(s);
            touched.(s) <- true;
            touched.(d) <- true
          end)
        g;
      let successors =
        Array.map
          (fun xs -> Array.of_list (List.sort_uniq Int.compare xs))
          outgoing
      in
      Profiler.finish_event "Worklist.graph";
      Profiler.start_event "Worklist.get_order";
      let d = CanonOrder.decompose successors touched in
      Profiler.finish_event "Worklist.get_order";
      (* The band condition of the canonical order (report only: the
         whole-program analysis itself does not depend on it). *)
      List.iter
        (fun v ->
          prerr_endline
            ("CANON_ORDER_BAND_VIOLATION scope=worklist "
            ^ CanonOrder.string_of_band_violation
                (fun i ->
                  CanonOrder.string_of_key (CanonOrder.key_of nodes.(i)))
                v))
        d.CanonOrder.band_violations;
      let entries = H.create ((2 * count) + 1) in
      Array.iteri
        (fun i n ->
          H.replace entries n
            {
              order = d.CanonOrder.orders.(i);
              head = d.heads.(i);
              rank = i;
              head_order = d.head_orders.(i);
            })
        nodes;
      let sccs =
        Array.to_list d.top_components
        |> List.map (fun scc ->
            Array.to_list scc |> List.map (fun i -> nodes.(i)))
      in
      { entries; sccs }
  end

  type order_entry = {
    node : BasicDom.Node.t;
    order : int;
    rank : int;
    loop_header : bool;
    head_order : int option;
  }

  type snapshot = {
    order : order_entry list;
    sccs : BasicDom.Node.t list list;
    loop_headers : BasicDom.Node.t list;
  }

  (* (order, head flag), canonical rank, node: the order number first, then
     the canonical rank (the key order), then a head entry before a plain
     one.  The rank is unique per node. *)
  module Ord = struct
    type t = workorder * int * DUGraph.node
    and workorder = int * bool

    let compare ((o1, head1), r1, _) ((o2, head2), r2, _) =
      let cmp_o = o1 - o2 in
      if cmp_o = 0 then
        let c = Int.compare r1 r2 in
        if c = 0 then if head1 = head2 then 0 else if head1 then -1 else 1
        else c
      else cmp_o
  end

  module S = BatSet.Make (Ord)

  type t = { set : S.t; order : Workorder.t }

  (* The entry of node [n] reached along an inner edge (a successor not
     after its source) at a loop head takes the head order. *)
  let entry ?(inner = false) n ws =
    let e = Workorder.H.find ws.order.Workorder.entries n in
    let o =
      if inner && e.Workorder.head && e.head_order >= 0 then e.head_order
      else e.order
    in
    ((o, e.head), e.rank, n)

  let queue is_inneredge n wl =
    { wl with set = S.add (entry ~inner:is_inneredge n wl) wl.set }

  let compare_order succ idx ws =
    match
      ( Workorder.H.find_opt ws.order.Workorder.entries idx,
        Workorder.H.find_opt ws.order.Workorder.entries succ )
    with
    | Some i, Some s ->
        Ord.compare
          ((s.order, s.head), s.rank, succ)
          ((i.order, i.head), i.rank, idx)
        <= 0
    | _ -> false

  let push_init nodes ws =
    BatSet.fold (fun n works -> queue false n works) nodes ws

  let push : Node.t -> Node.t -> t -> t =
   fun idx succ ws ->
    let bInnerLoop = compare_order succ idx ws in
    queue bInnerLoop succ ws

  let push_set : Node.t -> Node.t BatSet.t -> t -> t =
   fun idx succs ws ->
    BatSet.fold
      (fun succ works ->
        let bInnerLoop = compare_order succ idx works in
        queue bInnerLoop succ works)
      succs ws

  let init dug = { set = S.empty; order = Workorder.perform dug }
  let is_loopheader idx ws = Workorder.is_loopheader idx ws.order

  let snapshot ws =
    let entries = ws.order.Workorder.entries in
    let order =
      Workorder.H.fold
        (fun node (e : Workorder.entry) acc ->
          {
            node;
            order = e.order;
            rank = e.rank;
            loop_header = e.head;
            head_order = (if e.head_order >= 0 then Some e.head_order else None);
          }
          :: acc)
        entries []
      |> List.sort (fun (a : order_entry) (b : order_entry) ->
          let cmp = compare a.order b.order in
          if cmp <> 0 then cmp else Int.compare a.rank b.rank)
    in
    let sccs = List.map (List.sort Node.compare) ws.order.Workorder.sccs in
    let loop_headers =
      Workorder.H.fold
        (fun n (e : Workorder.entry) acc -> if e.head then n :: acc else acc)
        entries []
      |> List.sort Node.compare
    in
    { order; sccs; loop_headers }

  let pick ws =
    try
      let (_, _, n), set = S.pop_min ws.set in
      let ws = { ws with set } in
      Some (n, ws)
    with Not_found -> None
end
