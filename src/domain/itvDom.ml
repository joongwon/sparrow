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
open BasicDom
open Vocab

module Val = struct
  include ProdDom.Make4 (Itv) (PowLoc) (ArrayBlk) (PowProc)

  let null = (Itv.bot, PowLoc.null, ArrayBlk.bot, PowProc.bot)
  let is_itv (i, _, _, _) = not (Itv.is_bot i)
  let is_array (_, _, a, _) = not (ArrayBlk.is_empty a)
  let make (i, p, a, proc) = (i, p, a, proc)
  let itv_of_val : t -> Itv.t = fst
  let pow_loc_of_val : t -> PowLoc.t = snd
  let array_of_val : t -> ArrayBlk.t = trd
  let pow_proc_of_val : t -> PowProc.t = frth

  let allocsites_of_val : t -> Allocsite.t BatSet.t =
   fun v -> v |> array_of_val |> ArrayBlk.allocsites_of_array

  let all_loc_of_val (_, p, a, _) = PowLoc.join p (ArrayBlk.pow_loc_of_array a)
  let of_itv : Itv.t -> t = fun x -> (x, PowLoc.bot, ArrayBlk.bot, PowProc.bot)

  let of_pow_loc : PowLoc.t -> t =
   fun x -> (Itv.bot, x, ArrayBlk.bot, PowProc.bot)

  let of_array : ArrayBlk.t -> t = fun x -> (Itv.bot, PowLoc.bot, x, PowProc.bot)

  let of_pow_proc : PowProc.t -> t =
   fun x -> (Itv.bot, PowLoc.bot, ArrayBlk.bot, x)

  let modify_itv : Itv.t -> t -> t =
   fun i x -> (i, pow_loc_of_val x, array_of_val x, pow_proc_of_val x)

  let modify_arr : ArrayBlk.t -> t -> t =
   fun a x -> (itv_of_val x, pow_loc_of_val x, a, pow_proc_of_val x)

  let external_value : Allocsite.t -> t =
   fun allocsite -> (Itv.top, PowLoc.bot, ArrayBlk.extern allocsite, PowProc.bot)

  let itv_top : t = (Itv.top, PowLoc.bot, ArrayBlk.bot, PowProc.bot)

  let cast from_typ to_typ v =
    let from_typ, to_typ =
      BatTuple.Tuple2.mapn Sparrow_cil.unrollTypeDeep (from_typ, to_typ)
    in
    if v = of_itv Itv.zero && Sparrow_cil.isPointerType to_typ then
      (* char* x = (char* ) 0 *)
      null
    else if Sparrow_cil.isIntegralType to_typ then
      v |> itv_of_val |> Itv.cast from_typ to_typ |> of_itv
    else
      v |> array_of_val
      |> ArrayBlk.cast_array ~from:from_typ ~into:to_typ
      |> flip modify_arr v
end

(* What operations may change about the object a cell holds, kept in memory
   so that every reference sees the change (weak updates included); what is
   fixed when a pointer is made (an array's size) stays in the pointer. *)
module CellInfo = struct
  (* The null position of the char array whose elements the cell holds: the
     index of its first null character (bot: unknown). *)
  type t = { null_pos : Itv.t } [@@deriving compare]

  let bot = { null_pos = Itv.bot }
  let of_null null_pos = { null_pos }
  let le a b = Itv.le a.null_pos b.null_pos
  let eq a b = Itv.eq a.null_pos b.null_pos

  let join a b =
    if a == b then a else { null_pos = Itv.join a.null_pos b.null_pos }

  let meet a b = { null_pos = Itv.meet a.null_pos b.null_pos }
  let widen a b = { null_pos = Itv.widen a.null_pos b.null_pos }
  let narrow a b = { null_pos = Itv.narrow a.null_pos b.null_pos }
  let to_string a = "null: " ^ Itv.to_string a.null_pos
  let pp fmt a = Format.fprintf fmt "null: %a" Itv.pp a.null_pos
end

(* The contents of a cell: the value stored there and the cell's info. *)
module Cell = ProdDom.Make (Val) (CellInfo)

module Mem = struct
  include InstrumentedMem.Make (MapDom.MakeCPO (Loc) (Cell))

  let normalize_store_value k v =
    match Loc.typ k with
    | Some t when Sparrow_cil.isArithmeticType t ->
        Val.itv_of_val v |> Val.of_itv
    | _ -> v

  let add k (v, info) m = add k (normalize_store_value k v, info) m
  let weak_add k (v, info) m = weak_add k (normalize_store_value k v, info) m

  let lookup_cells locs mem =
    if eq mem bot then Cell.bot
    else
      PowLoc.fold
        (fun loc acc ->
          observe_read loc mem;
          Cell.join acc (find_unobserved loc mem))
        locs Cell.bot

  let lookup locs mem = Cell.fst (lookup_cells locs mem)
  let lookup_info locs mem = Cell.snd (lookup_cells locs mem)

  (* A strong value update leaves no info: info lives in array cells, which
     values never update strongly. *)
  let strong_update : PowLoc.t -> Val.t -> t -> t =
   fun locs v mem -> PowLoc.fold (fun x -> add x (v, CellInfo.bot)) locs mem

  let weak_update : PowLoc.t -> Val.t -> t -> t =
   fun locs v mem ->
    PowLoc.fold (fun x -> weak_add x (v, CellInfo.bot)) locs mem

  (* Set the cells' info, keeping their values. *)
  let strong_update_info : PowLoc.t -> CellInfo.t -> t -> t =
   fun locs info mem ->
    PowLoc.fold
      (fun x mem -> add x (lookup (PowLoc.singleton x) mem, info) mem)
      locs mem

  let weak_update_info : PowLoc.t -> CellInfo.t -> t -> t =
   fun locs info mem ->
    PowLoc.fold (fun x -> weak_add x (Val.bot, info)) locs mem
end

module Table = MapDom.MakeCPO (Node) (Mem)
