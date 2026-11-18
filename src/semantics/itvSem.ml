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
(** Semantics of interval analysis *)
open Vocab
open Sparrow_cil
open IntraCfg
open AbsSem
open BasicDom
open ItvDom
open Global
open ArrayBlk
open BatTuple

module Dom = ItvDom.Mem
module Access = Dom.Access
module Spec = Spec.Make(Dom)

(* ********************** *
 * Abstract memory access *
 * ********************** *)
module Shared = ItvSemantics.Direct

(* Only recursion information crosses the shared update boundary. Models and
   callers keep the Global.t API; other instances receive the same call
   graph as an explicit argument. *)
let can_strong_update mode spec global locs =
  Shared.can_strong_update mode spec global.callgraph locs

let lookup = Shared.lookup

let update mode spec global locs value memory =
  Shared.update mode spec global.callgraph locs value memory

let transfer_hook = ref (fun _ _ _ _ _ -> None)

let with_transfer_hook hook f =
  let previous = !transfer_hook in
  transfer_hook := hook;
  try
    let result = f () in
    transfer_hook := previous;
    result
  with exn ->
    transfer_hook := previous;
    raise exn

(* ********************************** *
 * Semantic functions for expressions *
 * ********************************** *)

(* The direct interpretation of the ItvSemantics composition. Keep optional
   Spec.empty at the public/model boundary: some API models deliberately
   evaluate operands with that default. *)
let eval_const = ItvSemantics.eval_const
let eval_uop = Shared.eval_uop
let eval_bop = Shared.eval_bop
let resolve_offset = Shared.resolve_offset
let var_of_varinfo = ItvSemantics.variable_loc
let eval_lv ?(spec=Spec.empty) pid lv mem = Shared.eval_lv spec pid lv mem
let eval ?(spec=Spec.empty) pid e mem = Shared.eval spec pid e mem
let eval_list spec pid exps mem = List.map (fun e -> eval ~spec pid e mem) exps
let eval_array_alloc ?(spec=Spec.empty) node e is_static mem =
  Shared.array_alloc spec node e is_static mem
let eval_struct_alloc = Shared.struct_alloc
let eval_string_alloc node s _mem = Shared.string_alloc node s
let eval_string _s = Val.of_itv Itv.nat
let prune mode spec global pid cond mem =
  Shared.prune mode spec global.callgraph pid cond mem

(* ******************************* *
 * Semantic functions for commands *
 * ******************************* *)
(* Default update option is weak update. *)
let run : update_mode -> Spec.t -> Node.t -> Mem.t * Global.t -> Mem.t * Global.t
= fun mode spec node (mem, global) ->
  let pid = Node.get_pid node in
  match !transfer_hook mode spec node mem global with
  | Some result -> result
  | None ->
  match InterCfg.cmdof global.icfg node with
  | IntraCfg.Cmd.Cset (l, e, _) ->
    (Shared.assign mode spec global.callgraph pid l e mem, global)
  | IntraCfg.Cmd.Cexternal (l, _) ->
    (Shared.external_store mode spec global.callgraph pid l mem, global)
  | IntraCfg.Cmd.Calloc (l, IntraCfg.Cmd.Array e, is_static, _) ->
    (Shared.array_assign mode spec global.callgraph node l e is_static mem, global)
  | IntraCfg.Cmd.Calloc (l, IntraCfg.Cmd.Struct s, _, _) ->
    (Shared.struct_assign mode spec global.callgraph pid l s mem, global)
  | IntraCfg.Cmd.Csalloc (l, s, _) ->
    (Shared.string_assign mode spec global.callgraph node l s mem, global)
  | IntraCfg.Cmd.Cfalloc (l, fd, _) ->
    (Shared.function_assign mode spec global.callgraph pid l fd.svar.vname mem, global)
  | IntraCfg.Cmd.Cassume (e, _) ->
    (Shared.assume mode spec global.callgraph pid e mem, global)
  | IntraCfg.Cmd.Ccall (lvo, Sparrow_cil.Lval (Sparrow_cil.Var f, Sparrow_cil.NoOffset), arg_exps, loc)
    when Global.is_undef f.vname global -> (* undefined library functions *)
    (ItvModelSemantics.Direct.undefined_call mode spec global.callgraph node pid
      lvo f arg_exps mem loc, global)
  | IntraCfg.Cmd.Ccall (lvo, f, arg_exps, _) -> (* user functions *)
    let formals target =
      List.map (fun x -> Loc.of_lvar target x.Sparrow_cil.vname x.Sparrow_cil.vtype)
        (InterCfg.argsof global.icfg target) in
    let mem, dump = Shared.user_call mode spec global.callgraph formals pid
      lvo f arg_exps mem global.dump in
    (mem, {global with dump})
  | IntraCfg.Cmd.Creturn (ret_opt, _) ->
    (Shared.return_store spec global.callgraph pid ret_opt mem, global)
  | IntraCfg.Cmd.Cskip when InterCfg.is_returnnode node global.icfg ->
    let callnode = InterCfg.callof node global.icfg in
    (match InterCfg.cmdof global.icfg callnode with
       IntraCfg.Cmd.Ccall (Some lv, f, _, _) ->
        Shared.call_return spec global.callgraph pid lv f mem
     | _ -> mem)
    |> (fun mem -> (mem, global))
  | IntraCfg.Cmd.Cskip -> (mem, global)
  | IntraCfg.Cmd.Casm _ -> (mem, global)    (* Not supported *)
  | _ -> invalid_arg "itvSem.ml: run_cmd"

let initial _ = Mem.bot
