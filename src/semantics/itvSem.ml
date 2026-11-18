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
(** Semantics of interval analysis *)

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
module Spec = Spec.Make (Dom)

(* ********************** *
 * Abstract memory access *
 * ********************** *)
module Sem = ItvSemantics

let can_strong_update mode spec global locs =
  Sem.can_strong_update mode spec global.callgraph locs

let lookup = Mem.lookup

let update mode spec global locs value memory =
  Sem.update mode spec global.callgraph locs value memory

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

(* Some API models deliberately evaluate operands with the default
   Spec.empty. *)
let eval_const = Sem.eval_const
let var_of_varinfo = Sem.var_of_varinfo
let eval_lv ?(spec = Spec.empty) pid lv mem = Sem.eval_lv spec pid lv mem
let eval ?(spec = Spec.empty) pid e mem = Sem.eval spec pid e mem

let eval_array_alloc ?(spec = Spec.empty) node e mem =
  Sem.array_alloc spec node e mem

let eval_string_alloc node s _mem = Sem.string_alloc node s

(* ******************************* *
 * Semantic functions for commands *
 * ******************************* *)
(* Default update option is weak update. *)
let run :
    update_mode -> Spec.t -> Node.t -> Mem.t * Global.t -> Mem.t * Global.t =
 fun mode spec node (mem, global) ->
  let pid = Node.get_pid node in
  match !transfer_hook mode spec node mem global with
  | Some result -> result
  | None -> (
      match InterCfg.cmdof global.icfg node with
      | IntraCfg.Cmd.Cset (l, e, _) ->
          (Sem.assign mode spec global.callgraph pid l e mem, global)
      | IntraCfg.Cmd.Calloc (l, e, _) ->
          (Sem.array_assign mode spec global.callgraph node l e mem, global)
      | IntraCfg.Cmd.Csalloc (l, s, _) ->
          (Sem.string_assign mode spec global.callgraph node l s mem, global)
      | IntraCfg.Cmd.Cfalloc (l, fd, _) ->
          ( Sem.function_assign mode spec global.callgraph pid l fd.svar.vname
              mem,
            global )
      | IntraCfg.Cmd.Cassume (e, _) ->
          (Sem.assume mode spec global.callgraph pid e mem, global)
      | IntraCfg.Cmd.Ccall
          ( lvo,
            Sparrow_cil.Lval (Sparrow_cil.Var f, Sparrow_cil.NoOffset),
            arg_exps,
            loc )
        when Global.is_undef f.vname global ->
          (* undefined library functions *)
          ( ItvModelSemantics.undefined_call mode spec global.callgraph node pid
              lvo f arg_exps mem loc,
            global )
      | IntraCfg.Cmd.Ccall (lvo, f, arg_exps, _) ->
          (* user functions *)
          let formals target =
            List.map
              (fun x ->
                Loc.of_lvar target x.Sparrow_cil.vname x.Sparrow_cil.vtype)
              (InterCfg.argsof global.icfg target)
          in
          let mem, dump =
            Sem.user_call mode spec global.callgraph formals pid lvo f arg_exps
              mem global.dump
          in
          (mem, { global with dump })
      | IntraCfg.Cmd.Creturn (ret_opt, _) ->
          (Sem.return_store spec global.callgraph pid ret_opt mem, global)
      | IntraCfg.Cmd.Cskip when InterCfg.is_returnnode node global.icfg ->
          let callnode = InterCfg.callof node global.icfg in
          (match InterCfg.cmdof global.icfg callnode with
            | IntraCfg.Cmd.Ccall (Some lv, f, _, _) ->
                Sem.call_return spec global.callgraph pid lv f mem
            | _ -> mem)
          |> fun mem -> (mem, global)
      | IntraCfg.Cmd.Cskip -> (mem, global)
      | IntraCfg.Cmd.Casm _ -> (mem, global) (* Not supported *)
      | _ -> invalid_arg "itvSem.ml: run_cmd")

let initial _ = Mem.bot
