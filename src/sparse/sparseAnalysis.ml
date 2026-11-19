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
open Global
open BasicDom
open AbsSem
open Dug

let total_iterations = ref 0
let g_clock = ref 0.0
let l_clock = ref 0.0

(* cost metrics captured per phase *)

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
  type visit = DUGraph.t -> DUGraph.node -> analysis_state -> analysis_state

  val frame_locals_of :
    (Global.t ->
    defs_at:(BasicDom.Node.t -> Dom.PowA.t) ->
    proc_local:(InterCfg.pid -> Dom.PowA.t) ->
    Dom.PowA.t)
    ref

  val variable_of : (Dom.A.t -> (InterCfg.pid * string) option) ref
  val analyze_node : Rows.t -> step -> visit

  val widening :
    visit ->
    DUGraph.t ->
    DUGraph.node BatSet.t ->
    analysis_state ->
    analysis_state

  val perform_with :
    (Rows.t -> visit) -> Spec.t -> Global.t -> Global.t * Table.t * Table.t

  val perform : Spec.t -> Global.t -> Global.t * Table.t * Table.t
end

module MakeWithAccess (Sem : AccessSem.S) = struct
  module Dom = Sem.Dom
  module AccessAnalysis = AccessAnalysis.Make (Sem)
  module Access = AccessAnalysis.Access
  module DUGraph = Dug.Make (Dom)
  module SsaDug = SsaDug.Make (DUGraph) (Access)
  module Worklist = Worklist.Make (DUGraph)
  module Table = MapDom.MakeCPO (Node) (Sem.Dom)
  module Spec = Sem.Spec
  module PowLoc = Sem.Dom.PowA
  module Rows = Rows.Make (Dom) (DUGraph) (Worklist)

  type analysis_state = Worklist.t * Global.t
  type step = Node.t -> Dom.t * Global.t -> Dom.t * Global.t
  type visit = DUGraph.t -> DUGraph.node -> analysis_state -> analysis_state

  (* The frame locals of the program (FrameLocal), from the global state and
     the access; the interval instance sets it (ItvAnalysis), others have
     none. *)
  let frame_locals_of :
      (Global.t ->
      defs_at:(BasicDom.Node.t -> PowLoc.t) ->
      proc_local:(InterCfg.pid -> PowLoc.t) ->
      PowLoc.t)
      ref =
    ref (fun _ ~defs_at:_ ~proc_local:_ -> PowLoc.empty)

  (* The procedure and name of the variable a location is rooted at (SsaDug
     routing); the interval instance sets it (ItvAnalysis, FrameLocal.variable),
     others know no variables. *)
  let variable_of : (Dom.A.t -> (InterCfg.pid * string) option) ref =
    ref (fun _ -> None)

  let print_iteration idx =
    total_iterations := !total_iterations + 1;
    if !total_iterations = 1 then (
      g_clock := Sys.time ();
      l_clock := Sys.time ())
    else if !total_iterations mod 10000 = 0 then begin
      let g_time = Format.sprintf "%.2f" (Sys.time () -. !g_clock) in
      let l_time = Format.sprintf "%.2f" (Sys.time () -. !l_clock) in
      my_prerr_string
        ("\r#iters: "
        ^ string_of_int !total_iterations
        ^ " took " ^ g_time ^ "s  (" ^ l_time ^ "s / last 10000 iters)");
      flush stderr;
      l_clock := Sys.time ()
    end

  (* The visit of a node in the widening phase on the rows *)
  let analyze_node : Rows.t -> step -> visit =
   fun rows step _ idx (works, global) ->
    print_iteration idx;
    let i = Rows.index rows idx in
    let works = ref works in
    let global = Rows.update rows works i (step idx) global in
    (!works, global)

  (* fixpoint iterator that can be used in both widening and narrowing phases *)
  let analyze_node_with_otable (widen, order) :
      Spec.t ->
      DUGraph.t ->
      DUGraph.node ->
      Worklist.t * (Global.t * Table.t * Table.t) ->
      Worklist.t * (Global.t * Table.t * Table.t) =
   fun spec dug idx (works, (global, inputof, outputof)) ->
    print_iteration idx;
    let pred = DUGraph.pred idx dug in
    let input =
      List.fold_left
        (fun m p ->
          let pmem = Table.find p outputof in
          let locs_on_edge = DUGraph.get_abslocs p idx dug in
          PowLoc.fold
            (fun l m ->
              let v1 = Dom.find l pmem in
              let v2 = Dom.find l m in
              Dom.add l (Dom.B.join v1 v2) m)
            locs_on_edge m)
        Dom.bot pred
    in
    let inputof = Table.add idx input inputof in
    let old_output = Table.find idx outputof in
    let new_output, global = Sem.run Strong spec idx (input, global) in
    let widened = widen old_output new_output in
    if order widened old_output then (works, (global, inputof, outputof))
    else
      let works =
        Worklist.push_set idx (BatSet.of_list (DUGraph.succ idx dug)) works
      in
      (works, (global, inputof, Table.add idx new_output outputof))

  let rec iterate f dug (works, state) =
    match Worklist.pick works with
    | None -> (works, state)
    | Some (idx, rest) -> iterate f dug (f dug idx (rest, state))

  (* the widening phase from the given nodes, each visit by [visit] *)
  let widening :
      visit ->
      DUGraph.t ->
      DUGraph.node BatSet.t ->
      analysis_state ->
      analysis_state =
   fun visit dug nodes (worklist, global) ->
    total_iterations := 0;
    ( worklist |> Worklist.push_init nodes |> fun init_worklist ->
      iterate visit dug (init_worklist, global) )
    |> fun x ->
    my_prerr_endline
      ("\n#iteration in widening : " ^ string_of_int !total_iterations);
    x

  let narrowing ?(initnodes = BatSet.empty) :
      Spec.t ->
      DUGraph.t ->
      Worklist.t * (Global.t * Table.t * Table.t) ->
      Worklist.t * (Global.t * Table.t * Table.t) =
   fun spec dug (worklist, state) ->
    total_iterations := 0;
    ( worklist
    |> Worklist.push_init
         (if BatSet.is_empty initnodes then DUGraph.nodesof dug else initnodes)
    |> fun init_worklist ->
      iterate
        (analyze_node_with_otable (Dom.narrow, fun x y -> Dom.le y x) spec)
        dug (init_worklist, state) )
    |> fun x ->
    my_prerr_endline
      ("#iteration in narrowing : " ^ string_of_int !total_iterations);
    x

  let print_dug (access, global, dug) =
    if !Options.dug then begin
      `Assoc
        [
          ("callgraph", CallGraph.to_json global.callgraph);
          ("cfgs", InterCfg.to_json global.icfg);
          ("dugraph", DUGraph.to_json dug);
          (*          ("dugraph-inter", DUGraph.to_json_inter dug access);*)
        ]
      |> Yojson.Safe.pretty_to_channel stdout;
      exit 0
    end
    else begin
      prerr_memory_usage ();
      prerr_endline ("#Nodes in def-use graph : " ^ i2s (DUGraph.nb_node dug));
      prerr_endline ("#Edges in def-use graph : " ^ i2s (DUGraph.nb_edge dug));
      prerr_endline ("#Locs on def-use graph : " ^ i2s (DUGraph.nb_loc dug))
    end

  let bind_fi_locs global mem_fi dug access inputof =
    DUGraph.fold_node
      (fun n t ->
        let used = Access.Info.useof (Access.find_node n access) in
        let pred = DUGraph.pred n dug in
        let locs_on_edge =
          list_fold
            (fun p -> PowLoc.union (DUGraph.get_abslocs p n dug))
            pred PowLoc.empty
        in
        let locs_not_on_edge = PowLoc.diff used locs_on_edge in
        let mem_with_locs_not_on_edge =
          PowLoc.fold
            (fun loc mem -> Dom.add loc (Dom.find loc mem_fi) mem)
            locs_not_on_edge (Table.find n inputof)
        in
        Table.add n mem_with_locs_not_on_edge t)
      dug inputof

  (* add pre-analysis memory to unanalyzed nodes *)
  let bind_unanalyzed_node global mem_fi dug access inputof =
    let nodes = InterCfg.nodesof global.icfg in
    let nodes_in_dug = DUGraph.nodesof dug in
    list_fold
      (fun node t ->
        if BatSet.mem node nodes_in_dug then t
        else
          let mem_with_access =
            PowLoc.fold
              (fun loc -> Dom.add loc (Dom.find loc mem_fi))
              (Access.Info.useof (Access.find_node node access))
              Dom.bot
          in
          Table.add node mem_with_access t)
      nodes inputof

  let initialize : Spec.t -> Global.t -> DUGraph.t -> Access.t -> Table.t =
   fun spec global dug access ->
    Table.add InterCfg.start_node (Sem.initial spec.Spec.locset) Table.empty
    |> cond (!Options.pfs < 100)
         (bind_fi_locs global spec.Spec.premem dug access)
         id

  let finalize spec global dug access (worklist, (global, inputof, outputof)) =
    let inputof =
      if !Options.pfs < 100 then
        bind_unanalyzed_node global spec.Spec.premem dug access inputof
      else inputof
    in
    (worklist, (global, inputof, outputof))

  let print_spec : Spec.t -> unit =
   fun spec ->
    my_prerr_endline
      ("#total abstract locations  = "
      ^ string_of_int (PowLoc.cardinal spec.Spec.locset));
    my_prerr_endline
      ("#flow-sensitive abstract locations  = "
      ^ string_of_int (PowLoc.cardinal spec.Spec.locset_fs))

  let perform_with visit spec global =
    print_spec spec;
    let access =
      StepManager.stepf false "Access Analysis"
        (fun premem ->
          FrameLocal.without (fun () ->
              AccessAnalysis.perform global spec.Spec.locset
                (Sem.run Strong spec) premem))
        spec.Spec.premem
    in
    let frame_locals =
      !frame_locals_of global
        ~defs_at:(fun node -> Access.Info.defof (Access.find_node node access))
        ~proc_local:(fun pid -> Access.find_proc_local pid access)
    in
    let dug =
      StepManager.stepf false "Def-use graph construction"
        (SsaDug.make ~frame_locals ~variable:!variable_of)
        (global, access, spec.Spec.locset_fs)
    in
    print_dug (access, global, dug);
    let worklist =
      StepManager.stepf false "Workorder computation" Worklist.init dug
    in
    let nodes =
      DUGraph.fold_node (fun n ns -> n :: ns) dug []
      |> List.sort Node.compare |> Array.of_list
    in
    let rows =
      Rows.make nodes dug ~defined:(fun node ->
          Access.Info.defof (Access.find_node node access))
    in
    let init_inputof = initialize spec global dug access in
    Array.iteri
      (fun i n -> (Rows.inputs rows).(i) <- Table.find n init_inputof)
      nodes;
    let worklist, global =
      StepManager.stepf false "Fixpoint iteration with widening"
        (widening (visit rows) dug (DUGraph.nodesof dug))
        (worklist, global)
    in
    let table memories init =
      list_fold
        (fun (n, m) -> Table.add n m)
        (BatArray.combine nodes memories |> Array.to_list)
        init
    in
    ( worklist,
      ( global,
        table (Rows.inputs rows) init_inputof,
        table (Rows.outputs rows) Table.empty ) )
    |> finalize spec global dug access
    |> StepManager.stepf_opt !Options.narrow false
         "Fixpoint iteration with narrowing" (narrowing spec dug)
    |> fun (_, (global, inputof, outputof)) -> (global, inputof, outputof)

  let perform : Spec.t -> Global.t -> Global.t * Table.t * Table.t =
   fun spec global ->
    perform_with
      (fun rows -> analyze_node rows (Sem.run Strong spec))
      spec global
end

module Make (Sem : AbsSem.S) = MakeWithAccess (AccessSem.Make (Sem))
