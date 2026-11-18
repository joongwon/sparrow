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
end

module Make
    (Dom : InstrumentedMem.S)
    (DUGraph : Dug.S with type Loc.t = Dom.A.t and type PowLoc.t = Dom.PowA.t)
    (Worklist : Worklist.S with type DUGraph.t = DUGraph.t) =
struct
  module Dom = Dom
  module DUGraph = DUGraph
  module Worklist = Worklist
  module Node = BasicDom.Node
  module Index = Hashtbl.Make (Node)

  type change = {
    position : int;
    key : Dom.A.t;
    old : Dom.B.t;
    fresh : Dom.B.t;
  }

  type t = {
    nodes : Node.t array;
    index : int Index.t;
    targets : int array array;
    cells : Dom.A.t array array;
    starts : int array array;
    carriers : int array array;
    defined : int array array;
    inputs : Dom.t array;
    outputs : Dom.t array;
    visited : bool array;
    changed : int list array;
    retry : int list array;
    queued : int array;
    mutable visits : int;
  }

  let position rows i key =
    let cells = rows.cells.(i) in
    let rec search lo hi =
      if lo >= hi then -1
      else
        let mid = (lo + hi) / 2 in
        let c = Dom.A.compare key cells.(mid) in
        if c = 0 then mid
        else if c > 0 then search lo mid
        else search (mid + 1) hi
    in
    search 0 (Array.length cells)

  let make nodes dug ~defined =
    let count = Array.length nodes in
    let index = Index.create (2 * count) in
    Array.iteri (fun i n -> Index.replace index n i) nodes;
    let routes =
      Array.map
        (fun n ->
          DUGraph.succ n dug |> List.sort Node.compare
          |> List.map (fun s ->
              (Index.find index s, DUGraph.get_abslocs n s dug))
          |> Array.of_list)
        nodes
    in
    let cells =
      Array.map
        (fun routes ->
          Array.fold_left
            (fun locs (_, label) -> Dom.PowA.union_unshared label locs)
            Dom.PowA.empty routes
          |> Dom.PowA.elements |> List.rev |> Array.of_list)
        routes
    in
    let rows =
      {
        nodes;
        index;
        targets = Array.map (Array.map fst) routes;
        cells;
        starts = [||];
        carriers = [||];
        defined = [||];
        inputs = Array.make count Dom.bot;
        outputs = Array.make count Dom.bot;
        visited = Array.make count false;
        changed = Array.make count [];
        retry = Array.make count [];
        queued = Array.make count 0;
        visits = 0;
      }
    in
    (* The routes carrying cell p of node i, in route order, are carriers.(i).(k) for
       starts.(i).(p) <= k < starts.(i).(p + 1): the route and the cell's position among
       the target's cells (-1: none), as route * 2^32 + position + 1. *)
    let located =
      Array.mapi
        (fun i routes ->
          let n = Array.length cells.(i) in
          let located =
            Array.map
              (fun (target, label) ->
                Dom.PowA.fold
                  (fun loc l ->
                    (position rows i loc, position rows target loc) :: l)
                  label [])
              routes
          in
          let starts = Array.make (n + 1) 0 in
          Array.iter
            (List.iter (fun (p, _) -> starts.(p + 1) <- starts.(p + 1) + 1))
            located;
          for p = 1 to n do
            starts.(p) <- starts.(p) + starts.(p - 1)
          done;
          let next = Array.sub starts 0 n
          and carriers = Array.make starts.(n) 0 in
          Array.iteri
            (fun route ->
              List.iter (fun (p, at) ->
                  carriers.(next.(p)) <- (route lsl 32) lor (at + 1);
                  next.(p) <- next.(p) + 1))
            located;
          (starts, carriers))
        routes
    in
    let starts = Array.map fst located and carriers = Array.map snd located in
    let defined =
      Array.mapi
        (fun i n ->
          Dom.PowA.fold
            (fun loc ps ->
              let p = position rows i loc in
              if p < 0 then ps else p :: ps)
            (defined n) []
          |> List.sort Int.compare |> Array.of_list)
        nodes
    in
    { rows with starts; carriers; defined }

  let index rows n = Index.find rows.index n
  let node rows i = rows.nodes.(i)
  let inputs rows = rows.inputs
  let outputs rows = rows.outputs

  (* Ascending union of an ascending list and an ascending array, without duplicates *)
  let union xs ys =
    let rec go xs k =
      match xs with
      | [] -> Array.to_list (Array.sub ys k (Array.length ys - k))
      | x :: xs' ->
          if k = Array.length ys || x < ys.(k) then x :: go xs' k
          else if ys.(k) < x then ys.(k) :: go xs (k + 1)
          else x :: go xs' (k + 1)
    in
    go xs 0

  (* The cells a visit checks.  A cell the transfer does not write is its
     input, so it can leave the stored output only if its input changed
     since the last visit, or the last visit stored a value below the
     transfer's (the store's normalization dropped a part); elsewhere it
     stays included.  The first visit checks every cell. *)
  let candidates rows i =
    if not rows.visited.(i) then begin
      rows.visited.(i) <- true;
      List.init (Array.length rows.cells.(i)) Fun.id
    end
    else begin
      let changed =
        List.sort_uniq Int.compare
          (List.rev_append rows.changed.(i) rows.retry.(i))
      in
      rows.changed.(i) <- [];
      rows.retry.(i) <- [];
      union changed rows.defined.(i)
    end

  (* MapDom.unstables at the candidates: an old cell keeps its key, a new
     cell takes the transfer's *)
  let changes rows i previous raw =
    List.filter_map
      (fun position ->
        let key = rows.cells.(i).(position) in
        match Dom.find_binding key raw with
        | None -> None
        | Some (fresh_key, fresh) -> (
            match Dom.find_binding key previous with
            | None -> Some { position; key = fresh_key; old = Dom.B.bot; fresh }
            | Some (key, old) ->
                if Dom.B.le fresh old then None
                else Some { position; key; old; fresh }))
      (candidates rows i)

  let deliver rows target at key value =
    if Dom.B.eq value Dom.B.bot then false
    else
      let input = rows.inputs.(target) in
      let old = Dom.find key input in
      if Dom.B.le value old then false
      else begin
        let joined =
          if Dom.B.le old value then value else Dom.B.join old value
        in
        rows.inputs.(target) <- Dom.add_binding key joined input;
        if at >= 0 && rows.visited.(target) then
          rows.changed.(target) <- at :: rows.changed.(target);
        true
      end

  let push rows works source target at c value =
    if deliver rows target at c.key value && rows.queued.(target) <> rows.visits
    then begin
      rows.queued.(target) <- rows.visits;
      works := Worklist.push rows.nodes.(source) rows.nodes.(target) !works
    end

  let update rows works i step global =
    let widen = Worklist.is_loopheader rows.nodes.(i) !works in
    rows.visits <- rows.visits + 1;
    let previous = rows.outputs.(i) in
    let raw, next =
      Profiler.event "SparseAnalysis.run" step (rows.inputs.(i), global)
    in
    let output, stored =
      Profiler.event "SparseAnalysis.get_unstable"
        (fun () ->
          let changes = changes rows i previous raw in
          let output =
            List.fold_left
              (fun output c ->
                Dom.add_binding c.key
                  (if widen then Dom.B.widen c.old c.fresh else c.fresh)
                  output)
              previous changes
          in
          (* the stored values; one below the transfer's is checked again *)
          let stored = List.map (fun c -> (c, Dom.find c.key output)) changes in
          rows.retry.(i) <-
            List.filter_map
              (fun (c, v) ->
                if Dom.B.le c.fresh v then None else Some c.position)
              stored;
          (output, stored))
        ()
    in
    if stored = [] then global
    else begin
      Profiler.event "SparseAnalysis.propagating"
        (List.iter (fun (c, value) ->
             for
               k = rows.starts.(i).(c.position)
               to rows.starts.(i).(c.position + 1) - 1
             do
               let carrier = rows.carriers.(i).(k) in
               push rows works i
                 rows.targets.(i).(carrier lsr 32)
                 ((carrier land 0xFFFFFFFF) - 1)
                 c value
             done))
        stored;
      rows.outputs.(i) <- output;
      next
    end
end
