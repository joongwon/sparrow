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
open ItvDom

(* ***************************** *
 * Flow-insensitive pre-analysis *
 * ***************************** *)
(* number of fixpoint rounds of the last pre-analysis run (cost metric) *)
let last_pre_iters = ref 0

(* One round: the step of every node in order, then the round's widening of
   the memory.  The rounds stop when neither the memory nor the dump grows. *)
let fixpoint :
  step:(round:int -> 'node -> Mem.t * Global.t -> Mem.t * Global.t) ->
  widen:(round:int -> Mem.t -> Mem.t -> Mem.t) ->
  'node list -> Mem.t -> Global.t -> Mem.t * Global.t * int
=fun ~step ~widen nodes mem global ->
  let rec iterate k (mem,global) =
    my_prerr_string ("\riteration : " ^ string_of_int k);
    flush stderr;
    let (mem',global') = list_fold (step ~round:k) nodes (mem,global) in
    let mem' = widen ~round:k mem mem' in
      if Mem.le mem' mem && Dump.le global'.dump global.dump
      then (my_prerr_newline (); (mem',global',k))
      else iterate (k+1) (mem',global')
  in
  iterate 1 (mem,global)

let callees_of : InterCfg.t -> InterCfg.Node.t -> Mem.t -> PowProc.t
= fun icfg node mem ->
  let pid = InterCfg.Node.get_pid node in
  let c = InterCfg.cmdof icfg node in
  match c with
  | IntraCfg.Cmd.Ccall (_, e, _, _) ->
    Val.pow_proc_of_val (ItvSem.eval pid e mem)
  | _ -> PowProc.bot

let draw_call_edges : (Node.t -> PowProc.t) -> Node.t list -> Global.t -> Global.t
= fun callees nodes global ->
  let icfg =
    List.fold_left (fun icfg node ->
        if InterCfg.is_callnode node icfg then
          PowProc.fold (InterCfg.add_call_edge node) (callees node) icfg
        else icfg) global.icfg nodes
  in
  { global with icfg = icfg }

let draw_callgraph : (Node.t -> PowProc.t) -> Node.t list -> Global.t -> Global.t
=fun callees nodes global ->
  let callgraph = List.fold_left (fun callgraph node ->
      PowProc.fold (fun callee callgraph ->
        CallGraph.add_edge (InterCfg.Node.get_pid node) callee callgraph) (callees node) callgraph)
    global.callgraph nodes
    |> CallGraph.compute_trans_calls
  in
  { global with callgraph = callgraph }

(* The call edges and the call graph of the callees the fixpoint memory gives *)
let finish : callees:(Node.t -> Mem.t -> PowProc.t) -> Node.t list -> Mem.t -> Global.t -> Global.t
= fun ~callees nodes mem global ->
  let callees node = callees node mem in
  { global with mem = mem }
  |> draw_call_edges callees nodes
  |> draw_callgraph callees nodes

let perform : Global.t -> Global.t
= fun global ->
  let nodes = InterCfg.nodesof global.icfg in
  let (mem, global, rounds) =
    fixpoint ~step:(fun ~round:_ -> ItvSem.run AbsSem.Weak ItvSem.Spec.empty)
      ~widen:(fun ~round:_ -> Mem.widen) nodes Mem.bot global in
  last_pre_iters := rounds;
  my_prerr_endline ("mem size : " ^ i2s (Mem.cardinal mem));
  finish ~callees:(callees_of global.icfg) nodes mem global
  |> Global.remove_unreachable_functions
