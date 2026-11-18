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

module type S =
sig
  module Access : Access.S
  module DUGraph : Dug.S
  module PowLoc : PowDom.CPO
  type node = BasicDom.Node.t
  type loc
  type routing
  val carried           : Global.t -> Access.t -> frame_locals:PowLoc.t -> InterCfg.pid -> PowLoc.t * PowLoc.t
  val routing           : Global.t -> Access.t -> frame_locals:PowLoc.t
    -> variable:(loc -> (InterCfg.pid * string) option) -> PowLoc.t -> routing
  val route             : routing -> InterCfg.pid -> DUGraph.t -> DUGraph.t
  val route_call        : routing -> node -> DUGraph.t -> DUGraph.t
  val single_definitions : Access.t -> PowLoc.t -> node list -> DUGraph.t -> DUGraph.t
  val bypass            : Access.t -> DUGraph.t -> DUGraph.t
  val make              : ?skip_nodes : BasicDom.Node.t BatSet.t -> frame_locals:PowLoc.t
    -> variable:(loc -> (InterCfg.pid * string) option) -> Global.t * Access.t * PowLoc.t -> DUGraph.t
  val to_json_intra     : DUGraph.t -> Access.t -> Yojson.Safe.t
  val to_json_inter     : DUGraph.t -> Access.t -> Yojson.Safe.t
end

module Make (DUGraph : Dug.S) (Access: Access.S
  with type Loc.t = DUGraph.Loc.t and type PowLoc.t = DUGraph.PowLoc.t) =
struct
  module DUGraph = DUGraph
  type node = BasicDom.Node.t
  module Loc = DUGraph.Loc
  module PowLoc = DUGraph.PowLoc
  module LocMap = BatMap.Make(Loc)
  module IntraNodeMap = BatMap.Make(IntraCfg.Node)
  module IntraNodeSet = IntraCfg.NodeSet
  module NodeSetMap = BatMap.Make(IntraNodeSet)
  type loc = Loc.t

  (** Def-use graph construction *)
  module Access = Access
  type access_map = PowLoc.t IntraNodeMap.t

  let get_ordinary_defs : Access.t -> node -> PowLoc.t
  =fun access node -> Access.Info.defof (Access.find_node node access)

  let get_ordinary_uses : Access.t -> node -> PowLoc.t
  =fun access node -> Access.Info.useof (Access.find_node node access)

  (* The locations the call edges of a procedure carry: its entry defines
     and its exit uses them, a call of it uses them and the call's return
     site defines them.  A non-recursive procedure carries its reach without
     the proc-locals of itself and of its callees
     ([Access.find_proc_reach_wo_local]).  A recursive procedure carries its
     reach without the proc-locals of the non-recursive procedures and
     without the frame locals (FrameLocal): a non-recursive procedure's
     proc-local is on no edge of that procedure's own entry or exit, so on
     the edges of a recursive caller it reached no node that accesses it;
     the proc-locals of a recursive procedure stay, since its activations
     nest and its call edges are what joins them.  The reach of a procedure
     holds no proc-local of a procedure it does not reach, so the
     proc-locals of every non-recursive procedure are removed at once. *)
  let carried_info : Global.t -> Access.t -> frame_locals:PowLoc.t -> pid -> Access.Info.t
  =fun global access ~frame_locals ->
    let nonrecursive_locals = lazy (
      Access.fold_proc_local (fun pid locals locs ->
          if Global.is_rec pid global then locs else PowLoc.union locals locs)
        access PowLoc.empty) in
    let memo = Hashtbl.create 10000 in
    fun pid ->
      match Hashtbl.find_opt memo pid with
      | Some info -> info
      | None ->
        let info =
          if Global.is_rec pid global && not !Options.unsound_recursion then
            Access.find_proc_reach pid access
            |> Access.Info.filter_out (Lazy.force nonrecursive_locals)
          else Access.find_proc_reach_wo_local pid access in
        let info = Access.Info.filter_out frame_locals info in
        Hashtbl.add memo pid info;
        info

  let carried : Global.t -> Access.t -> frame_locals:PowLoc.t -> pid -> PowLoc.t * PowLoc.t
  =fun global access ~frame_locals ->
    let carried = carried_info global access ~frame_locals in
    fun pid -> let info = carried pid in Access.Info.defof info, Access.Info.useof info

  (* The routing of a set of locations through the def-use chains: the
     access restricted to them, the frame locals of recursive procedures
     (FrameLocal), which leave every call edge, the locations a procedure's
     call edges carry among the set ([carried], computed once per
     procedure) and those the edges of a call in a given caller carry
     ([edges], computed once per caller and callee). *)
  type routing = {
    global : Global.t;
    access : Access.t;
    locset : PowLoc.t;
    frame_locals : PowLoc.t;
    variable : Loc.t -> (pid * string) option;
    carried : pid -> Access.Info.t;
    uses : (pid, PowLoc.t) Hashtbl.t;
    defs : (pid, PowLoc.t) Hashtbl.t;
    edges : (pid * pid, PowLoc.t * PowLoc.t) Hashtbl.t;
    reaches : (pid, (pid, unit) Hashtbl.t) Hashtbl.t;
  }

  let routing : Global.t -> Access.t -> frame_locals:PowLoc.t
    -> variable:(Loc.t -> (pid * string) option) -> PowLoc.t -> routing
  =fun global access ~frame_locals ~variable locset ->
    { global; access = Access.restrict_access access locset; locset; frame_locals; variable;
      carried = carried_info global access ~frame_locals;
      uses = Hashtbl.create 10000; defs = Hashtbl.create 10000;
      edges = Hashtbl.create 10000; reaches = Hashtbl.create 10000 }

  let without_frame_locals routing locset =
    if PowLoc.is_empty routing.frame_locals then locset
    else PowLoc.diff locset routing.frame_locals

  let uses_of_function : routing -> pid -> PowLoc.t
  =fun routing pid ->
    match Hashtbl.find_opt routing.uses pid with
    | Some locset -> locset
    | None ->
      let locset = PowLoc.inter routing.locset (Access.Info.useof (routing.carried pid)) in
      Hashtbl.add routing.uses pid locset;
      locset

  let defs_of_function : routing -> pid -> PowLoc.t
  =fun routing pid ->
    match Hashtbl.find_opt routing.defs pid with
    | Some locset -> locset
    | None ->
      let locset = PowLoc.inter routing.locset (Access.Info.defof (routing.carried pid)) in
      Hashtbl.add routing.defs pid locset;
      locset

  (* Whether an activation of [q] may be live at a point of [pid]: q is pid or
     reaches it (its transitive callees, tabled once per q). *)
  let reaches routing q pid =
    q = pid ||
    let callees = match Hashtbl.find_opt routing.reaches q with
      | Some callees -> callees
      | None ->
        let callees = Hashtbl.create 64 in
        PowProc.iter (fun r -> Hashtbl.replace callees r ())
          (CallGraph.trans_callees q routing.global.callgraph);
        Hashtbl.add routing.reaches q callees;
        callees in
    Hashtbl.mem callees pid

  (* The locations the edges of a call in [caller] to [callee] carry (to the
     callee's entry, from its exit to the return site): what the callee's
     call edges carry, without the variables of the procedures no activation
     of which is live at the call, those that do not reach the caller.  A
     variable of such a procedure holds no value at the call (the frame
     that will hold it is yet to be made, or every frame that held it has
     returned), so nothing flows through it; the callee's own variables are
     among them when the callee does not reach the caller, except its
     formals, which the call binds, on the edge to the entry, and its
     return variable, which the return site reads, on the edge from the
     exit.  The entry still defines and the exit still uses all the callee's
     call edges carry, the union over its callers. *)
  let edges_of_call : routing -> caller:pid -> pid -> PowLoc.t * PowLoc.t
  =fun routing ~caller callee ->
    match Hashtbl.find_opt routing.edges (caller, callee) with
    | Some edges -> edges
    | None ->
      let formals = List.map (fun (v : Sparrow_cil.varinfo) -> v.vname)
          (InterCfg.argsof routing.global.icfg callee) in
      let live keep loc = match routing.variable loc with
        | Some (q, x) -> reaches routing q caller || (q = callee && keep x)
        | None -> true in
      let edges =
        PowLoc.filter (live (fun x -> List.mem x formals)) (uses_of_function routing callee),
        PowLoc.filter (live (fun x -> x = "__return__")) (defs_of_function routing callee) in
      Hashtbl.add routing.edges (caller, callee) edges;
      edges

  (* locations considered as being used in the given node *)
  let lhsof : routing -> node -> PowLoc.t
  =fun routing node ->
    let { global; access } = routing in
    let (pid,cfgnode) = Node.get_pid node, Node.get_cfgnode node in
    let ordinary_defs = get_ordinary_defs access node in
    (* entry defines use(f) *)
    let defs_at_entry =
      if IntraCfg.is_entry cfgnode
      then uses_of_function routing pid
      else PowLoc.empty in
    (* return nodes define what the edges from the callees' exits carry *)
    let defs_at_return =
      if InterCfg.is_returnnode node global.icfg then
        ProcSet.fold (fun callee ->
          PowLoc.union (snd (edges_of_call routing ~caller:pid callee))
        ) (InterCfg.get_callees (InterCfg.callof node global.icfg) global.icfg) PowLoc.empty
      else PowLoc.empty
    in
      PowLoc.union ordinary_defs (PowLoc.union defs_at_entry defs_at_return)

  (* locations considered as being defined in the given node *)
  let rhsof : routing -> node -> PowLoc.t
  =fun routing node ->
    let { global; access } = routing in
    let (pid,cfgnode) = Node.get_pid node, Node.get_cfgnode node in
    let ordinary_uses = get_ordinary_uses access node in
    (* exit uses defs(f) *)
    let uses_at_exit =
      if IntraCfg.is_exit cfgnode
      then defs_of_function routing pid
      else PowLoc.empty in
    (* return node inside recursive functions uses local variables of pid *)
    let uses_at_rec_return =
      if InterCfg.is_returnnode node global.icfg && Global.is_rec pid global then
        without_frame_locals routing (Access.find_proc_local pid access)
      else PowLoc.empty in
    (* return node uses not-localized variables of call node *)
    let uses_at_return =
      if InterCfg.is_returnnode node global.icfg then
        let call_node = InterCfg.callof node global.icfg in
        let callees = InterCfg.get_callees call_node global.icfg in
        let defs_of_callees =
          let add_defs callee =
            PowLoc.union (snd (edges_of_call routing ~caller:pid callee)) in
          ProcSet.fold add_defs callees PowLoc.empty in
        let add_not_defined callee =
          let defs = snd (edges_of_call routing ~caller:pid callee) in
          PowLoc.union (PowLoc.diff defs_of_callees defs) in
        ProcSet.fold add_not_defined callees PowLoc.empty
      else PowLoc.empty in
    (* call nodes use what the edges to the callees' entries carry *)
    let uses_at_call =
      if InterCfg.is_callnode node global.icfg then
        ProcSet.fold (fun callee ->
          PowLoc.union (fst (edges_of_call routing ~caller:pid callee))
        ) (InterCfg.get_callees node global.icfg) PowLoc.empty
      else PowLoc.empty
    in
    list_fold PowLoc.union
      [ ordinary_uses; uses_at_exit; uses_at_call; uses_at_rec_return;
        uses_at_return ] PowLoc.empty

  let prepare_defs_uses : routing -> IntraCfg.t -> access_map * access_map
  =fun routing cfg ->
    let collect f =
      List.fold_left (fun m node ->
        IntraNodeMap.add node (f routing (Node.make (IntraCfg.get_pid cfg) node)) m
      ) IntraNodeMap.empty (IntraCfg.nodesof cfg) in
      (collect lhsof, collect rhsof)

  (* The locations a procedure defines, in classes of the same definition
     nodes, each with its definition nodes *)
  let classes : IntraCfg.t -> access_map -> (IntraNodeSet.t * PowLoc.t) array
  =fun cfg defs_of ->
    List.fold_left (fun map node ->
        PowLoc.fold (fun loc -> LocMap.modify_def IntraNodeSet.empty loc (IntraNodeSet.add node))
          (IntraNodeMap.find node defs_of) map)
      LocMap.empty (IntraCfg.nodesof cfg)
    |> (fun map -> LocMap.fold (fun loc nodes -> NodeSetMap.modify_def PowLoc.empty nodes (PowLoc.add loc))
           map NodeSetMap.empty)
    |> NodeSetMap.bindings |> Array.of_list

  (* The phi nodes of locations defined at the given nodes: their iterated
     dominance frontier *)
  let phi_nodes : IntraCfg.t -> IntraNodeSet.t -> IntraNodeSet.t
  =fun cfg defnodes ->
    let rec iterate phis = function
      | [] -> phis
      | node :: rest ->
        let (phis, rest) =
          IntraNodeSet.fold (fun y (phis, rest) ->
              if IntraNodeSet.mem y phis then (phis, rest)
              else (IntraNodeSet.add y phis, if IntraNodeSet.mem y defnodes then rest else y :: rest))
            (IntraCfg.dom_fronts node cfg) (phis, rest) in
        iterate phis rest
    in
    iterate IntraNodeSet.empty (IntraNodeSet.elements defnodes)

  (* The def-use edges inside a procedure by SSA.  Locations with the same
     definition nodes have the same phi nodes and the same last definition
     at every node, so both are computed per class of such locations. *)
  let cfg2dug : routing -> IntraCfg.t -> DUGraph.t -> DUGraph.t
  =fun routing cfg dug ->
    let pid = IntraCfg.get_pid cfg in
    let (defs_of, uses_of) = prepare_defs_uses routing cfg in
    let classes = classes cfg defs_of in
    let class_of = ref LocMap.empty in
    let defined = Hashtbl.create 64 and phis = Hashtbl.create 64 in
    Array.iteri (fun c (nodes, locs) ->
        class_of := PowLoc.fold (fun loc -> LocMap.add loc c) locs !class_of;
        IntraNodeSet.iter (fun n -> Hashtbl.add defined n c) nodes;
        IntraNodeSet.iter (fun n -> Hashtbl.add phis n c) (phi_nodes cfg nodes)) classes;
    let last = Array.make (Array.length classes) None in
    let draw src locs dst dug = DUGraph.add_abslocs (Node.make pid src) locs (Node.make pid dst) dug in
    let rec search node dug =
      let here = Hashtbl.find_all phis node in
      (* 1: the uses but the phi locations from their last definitions *)
      let phi_locs = List.fold_left (fun locs c -> PowLoc.union (snd classes.(c)) locs) PowLoc.empty here in
      let dug =
        PowLoc.fold (fun loc sources ->
            match LocMap.find_opt loc !class_of with
            | Some c -> (match last.(c) with
                | Some src -> IntraNodeMap.modify_def PowLoc.empty src (PowLoc.add loc) sources
                | None -> sources)
            | None -> sources)
          (PowLoc.diff (IntraNodeMap.find node uses_of) phi_locs) IntraNodeMap.empty
        |> (fun sources -> IntraNodeMap.fold (fun src locs -> draw src locs node) sources dug) in
      (* 2: the classes defined here *)
      let updated = Hashtbl.find_all defined node @ here in
      let saved = List.map (fun c -> (c, last.(c))) updated in
      List.iter (fun c -> last.(c) <- Some node) updated;
      (* 3: the phi locations of the successors from their last definitions *)
      let dug =
        List.fold_left (fun dug succ ->
            List.fold_left (fun dug c ->
                match last.(c) with Some src -> draw src (snd classes.(c)) succ dug | None -> dug)
              dug (Hashtbl.find_all phis succ))
          dug (IntraCfg.succ node cfg) in
      (* 4: the children in the dominator tree *)
      let dug = IntraNodeSet.fold search (IntraCfg.children_of_dom_tree node cfg) dug in
      List.iter (fun (c, previous) -> last.(c) <- previous) saved;
      dug
    in
    search IntraCfg.Node.entry dug

  (* The def-use edges inside one procedure *)
  let route : routing -> pid -> DUGraph.t -> DUGraph.t
  =fun routing pid dug ->
    cfg2dug routing (InterCfg.cfgof routing.global.icfg pid) dug |> DUGraph.compact

  let draw_intraedges : routing -> DUGraph.t -> DUGraph.t
  =fun routing dug ->
    Profiler.start_event "DugGen.draw_intraedges";
    let n_pids = List.length (InterCfg.pidsof routing.global.icfg) in
    my_prerr_endline "draw intra-procedural edges";
    let r =snd (
        InterCfg.fold_cfgs (fun pid _cfg (k,dug) ->
          prerr_progressbar k n_pids;
          (k+1, route routing pid dug)
        ) routing.global.icfg (1,dug)) in
    Profiler.finish_event "DugGen.draw_intraedges";
    r

  (* The def-use edges of one call: to the callees' entries and from their
     exits to the return node *)
  let route_call : routing -> node -> DUGraph.t -> DUGraph.t
  =fun routing call dug ->
    let icfg = routing.global.icfg in
    let callees = InterCfg.get_callees call icfg in
    (* no-callee call nodes (e.g. the synthetic `sparrow_array_init`, which
       is a Ccall with succ-count <> 1) draw no inter-procedural edges --
       guard so `returnof` (which asserts a single successor) is only taken
       for real calls.  Identical to the old behaviour on real calls. *)
    if ProcSet.is_empty callees then dug
    else
      let return = InterCfg.returnof call icfg in
      ProcSet.fold (fun callee dug ->
        let entry = InterCfg.entryof icfg callee in
        let exit  = InterCfg.exitof  icfg callee in
        let locs_on_call, locs_on_return = edges_of_call routing ~caller:(Node.get_pid call) callee in
          dug
          |> DUGraph.add_abslocs call locs_on_call entry
          |> DUGraph.add_abslocs exit locs_on_return return
      ) callees dug

  let draw_interedges : routing -> DUGraph.t -> DUGraph.t
  =fun routing dug ->
    let calls = InterCfg.callnodesof routing.global.icfg in
    let n_calls = List.length calls in
    my_prerr_endline "draw inter-procedural edges";
    list_fold (fun call (k,dug) ->
      prerr_progressbar k n_calls;
      (k+1, route_call routing call dug)
    ) calls (1,dug)
    |> snd

  (* The edges of the single-definition locations, from the definition
     directly to every use among the given nodes *)
  let single_definitions : Access.t -> PowLoc.t -> InterCfg.Node.t list -> DUGraph.t -> DUGraph.t
  =fun access locset nodes dug ->
    let nodes = PowNode.of_list nodes in
    let single_defs = PowLoc.inter locset (Access.find_single_defs access) in
      PowLoc.fold (fun x dug ->
        let def_points = Access.find_def_nodes x access in
        let _ = assert (PowNode.cardinal def_points = 1) in
        let def_point = PowNode.choose def_points in
        let use_points = Access.find_use_nodes x access in
          PowNode.fold (fun use_point ->
            if PowNode.mem def_point nodes && PowNode.mem use_point nodes
            then DUGraph.add_absloc def_point x use_point
            else id
          ) use_points dug
      ) single_defs dug

  (* The bypass of a node, for each location on its edges that it does not
     access: a location that enters or leaves on no edge leaves the node's
     edges; one that enters and leaves, on exactly one edge either way, also
     goes from each of its sources to each of its targets directly.  Each
     location's step touches only that location, so all are done at once
     from the node's edges as they are when its turn comes.  A bypassed
     cycle remains a cycle (a self edge stays), so the WTO still selects a
     widening point. *)
  let optimize_node access node dug =
    let union = PowLoc.union_unshared and inter = PowLoc.inter_unshared in
    let preds = List.map (fun p -> (p, DUGraph.get_abslocs p node dug)) (DUGraph.pred node dug) in
    let succs = List.map (fun s -> (s, DUGraph.get_abslocs node s dug)) (DUGraph.succ node dug) in
    (* the locations on some edge, and on two or more *)
    let on edges =
      List.fold_left (fun (some, many) (_, label) ->
          (union label some, union (inter label some) many))
        (PowLoc.empty, PowLoc.empty) edges
    in
    let (inward, inward_many) = on preds and (outward, outward_many) = on succs in
    let passing =
      PowLoc.diff (union inward outward)
        (Access.Info.accessof (Access.find_node node access)) in
    let through = inter passing (inter inward outward) in
    let bypassed = PowLoc.diff through (inter inward_many outward_many) in
    let removed = union (PowLoc.diff passing through) bypassed in
    if PowLoc.is_empty removed then dug else
    let dug = List.fold_left (fun dug (p, _) -> DUGraph.remove_abslocs p removed node dug) dug preds in
    let dug = List.fold_left (fun dug (s, _) -> DUGraph.remove_abslocs node removed s dug) dug succs in
    List.fold_left (fun dug (p, label) ->
        let locs = inter label bypassed in
        List.fold_left (fun dug (s, out) -> DUGraph.add_abslocs p (inter locs out) s dug)
          dug succs)
      dug preds


  (* The bypass is not confluent (the two-node cycle u->v->u): the graph it leaves depends on the order the
     nodes are visited in.  Visit every node once, in the canonical key order
     the worklist numbers nodes by (CanonOrder.key_of, then Node.compare),
     each with the edges it has when its turn comes; never the iteration
     order of the graph's hash table. *)
  let canonical_nodes dug =
    DUGraph.fold_node (fun n acc -> (CanonOrder.key_of n, n) :: acc) dug []
    |> List.sort (fun (a, n) (b, m) ->
        let c = CanonOrder.compare_key a b in
        if c <> 0 then c else Node.compare n m)
    |> List.map snd

  (* Graph compression: the self-edge-keeping bypass of every node, in
     canonical key order. *)
  let bypass : Access.t -> DUGraph.t -> DUGraph.t
  =fun access dug ->
    Profiler.event "DugGen.optimize_dug.all"
      (fun dug ->
         List.fold_left (fun dug node -> optimize_node access node dug)
           dug (canonical_nodes dug))
      dug

  let make ?(skip_nodes = BatSet.empty) ~frame_locals ~variable : Global.t * Access.t * PowLoc.t -> DUGraph.t
  =fun (global,access,locset) ->
    let nodes = InterCfg.nodesof global.icfg in
    let access = Access.restrict_access access locset in
    (* single-definition locations are connected directly to their uses *)
    let graph_locs = PowLoc.diff locset (Access.find_single_defs access) in
    let routing = routing global access ~frame_locals ~variable graph_locs in
    DUGraph.create ~size:(List.length nodes) ()
    |> draw_intraedges routing
    |> draw_interedges routing
    |> single_definitions access locset nodes
    |> bypass access
    |> DUGraph.compact

  let to_json_intra : DUGraph.t -> Access.t -> Yojson.Safe.t
  = fun g access ->
    let nodes = `List (DUGraph.fold_node (fun v nodes ->
                  (`String (Node.to_string v))::nodes) g [])
    in
    let edges = `List (DUGraph.fold_edges (fun src dst edges ->
                  let spid = InterCfg.Node.get_pid src in
                  let dpid = InterCfg.Node.get_pid dst in
                  if spid = dpid then
                    let addrset = DUGraph.get_abslocs src dst g in
                    let access_proc = Access.find_proc spid access in
                    let localset = PowLoc.filter (fun x ->
                                    Access.Info.mem x access_proc) addrset in
                    if PowLoc.is_empty localset then edges
                    else
                      (`List [`String (Node.to_string src); `String (Node.to_string dst);
                              `String (PowLoc.fold (fun addr s -> (Loc.to_string addr)^","^s) localset "")])
                      ::edges
                  else edges
                  ) g [])
    in
    `Assoc [("nodes", nodes); ("edges", edges)]

    let to_json_inter : DUGraph.t -> Access.t -> Yojson.Safe.t
    = fun g access ->
      let nodes = `List (DUGraph.fold_node (fun v nodes ->
                    (`String (Node.to_string v))::nodes) g [])
      in
      let edges = `List (DUGraph.fold_edges (fun src dst edges ->
                    let spid = InterCfg.Node.get_pid src in
                    let dpid = InterCfg.Node.get_pid dst in
                    if not (spid = dpid) then
                      let addrset = DUGraph.get_abslocs src dst g in
                      let access_proc = Access.find_proc spid access in
                      let localset = PowLoc.filter (fun x ->
                                      Access.Info.mem x access_proc) addrset in
                      if PowLoc.is_empty localset then edges
                      else
                        (`List [`String (Node.to_string src); `String (Node.to_string dst);
                                `String (PowLoc.fold (fun addr s -> (Loc.to_string addr)^","^s) localset "")])
                        ::edges
                    else edges
                    ) g [])
      in
      `Assoc [("nodes", nodes); ("edges", edges)]
end
