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
(* Abstract Array Block *)

open AbsDom
open BasicDom
open Vocab

(* A pointer into an array: its offset and the array's size, both counted in
   elements of the pointer's static pointee type. *)
module ArrInfo = struct
  type t = { offset : Itv.t; size : Itv.t } [@@deriving compare]

  let bot = { offset = Itv.bot; size = Itv.bot }
  let top = { offset = Itv.top; size = Itv.top }
  let input = { offset = Itv.zero; size = Itv.pos }

  let join a1 a2 =
    if a1 == a2 then a2
    else
      { offset = Itv.join a1.offset a2.offset; size = Itv.join a1.size a2.size }

  let meet a1 a2 =
    if a1 == a2 then a2
    else
      { offset = Itv.meet a1.offset a2.offset; size = Itv.meet a1.size a2.size }

  let widen a1 a2 =
    if a1 == a2 then a2
    else
      {
        offset = Itv.widen a1.offset a2.offset;
        size = Itv.widen a1.size a2.size;
      }

  let narrow a1 a2 =
    if a1 == a2 then a2
    else
      {
        offset = Itv.narrow a1.offset a2.offset;
        size = Itv.narrow a1.size a2.size;
      }

  let eq a1 a2 =
    a1 == a2 || (Itv.eq a1.offset a2.offset && Itv.eq a1.size a2.size)

  let le a1 a2 =
    a1 == a2 || (Itv.le a1.offset a2.offset && Itv.le a1.size a2.size)

  (* Elements of [from] bytes counted as elements of [into] bytes. *)
  let resize from into x = Itv.divide (Itv.times x from) into

  let cast from into arr =
    { offset = resize from into arr.offset; size = resize from into arr.size }

  let plus_offset arr i = { arr with offset = Itv.plus arr.offset i }
  let minus_offset arr i = { arr with offset = Itv.minus arr.offset i }

  let to_string arr =
    "(" ^ Itv.to_string arr.offset ^ ", " ^ Itv.to_string arr.size ^ ")"

  let pp fmt arr =
    Format.fprintf fmt "@[<hov 2>( %a, %a )@]" Itv.pp arr.offset Itv.pp arr.size
end

include MapDom.MakeLAT (Loc) (ArrInfo)

let make : Loc.t -> Itv.t -> Itv.t -> t =
 fun cell offset size -> add cell { ArrInfo.offset; size } bot

let offsetof : t -> Itv.t =
 fun a -> fold (fun _ arr -> Itv.join arr.ArrInfo.offset) a Itv.bot

let sizeof : t -> Itv.t =
 fun a -> fold (fun _ arr -> Itv.join arr.ArrInfo.size) a Itv.bot

let extern allocsite =
  if !Options.top_location then top
  else add (Loc.of_allocsite allocsite) ArrInfo.top empty

let input allocsite =
  if !Options.top_location then top
  else add (Loc.of_allocsite allocsite) ArrInfo.input empty

let plus_offset : t -> Itv.t -> t =
 fun arr i -> map (fun a -> ArrInfo.plus_offset a i) arr

let minus_offset : t -> Itv.t -> t =
 fun arr i -> map (fun a -> ArrInfo.minus_offset a i) arr

(* The byte size of the type a pointer or array type points to; an unknown
   size is any non-negative one. *)
let element_size typ =
  match Sparrow_cil.unrollTypeDeep typ with
  | Sparrow_cil.TPtr (t, _) | Sparrow_cil.TArray (t, _, _) -> (
      try Some (Itv.of_int (CilHelper.byteSizeOf t)) with _ -> Some Itv.nat)
  | _ -> None

let is_cmd_arg = function
  | Loc.Allocsite a -> Allocsite.is_cmd_arg a
  | _ -> false

(* A cast between pointer types counts the offset and size in elements of
   the new pointee type. *)
let cast_array ~from ~into a =
  (* A non-pointer source (an integer holding an address) counts bytes. *)
  let from = match element_size from with Some f -> f | None -> Itv.one in
  match element_size into with
  | Some i when not (Itv.eq from i) ->
      mapi (fun cell -> if is_cmd_arg cell then id else ArrInfo.cast from i) a
  | _ -> a

let allocsites_of_array a =
  foldi
    (fun k _ acc ->
      match k with Loc.Allocsite site -> BatSet.add site acc | _ -> acc)
    a BatSet.empty

let pow_loc_of_array : t -> PowLoc.t =
 fun array -> foldi (fun k _ -> PowLoc.add k) array PowLoc.bot

let to_string : t -> string =
 fun x ->
  if is_empty x then "bot"
  else
    foldi
      (fun a b s ->
        let str = A.to_string a ^ " -> " ^ B.to_string b in
        link_by_sep "\n\t" str s)
      x ""
