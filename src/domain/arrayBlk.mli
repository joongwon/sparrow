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
(** Array domain: pointers into arrays, keyed by the cell that holds the array's
    elements. *)

(** A pointer's offset and the array's size, both counted in elements of the
    pointer's static pointee type. *)
module ArrInfo : sig
  type t = { offset : Itv.t; size : Itv.t }

  val top : t
  val input : t
end

include MapDom.LAT with type A.t = BasicDom.Loc.t and type B.t = ArrInfo.t

val make : BasicDom.Loc.t -> Itv.t -> Itv.t -> t
(** [make cell offset size] *)

val offsetof : t -> Itv.t
val sizeof : t -> Itv.t
val extern : BasicDom.Allocsite.t -> t
val input : BasicDom.Allocsite.t -> t
val plus_offset : t -> Itv.t -> t
val minus_offset : t -> Itv.t -> t

val element_size : Sparrow_cil.typ -> Itv.t option
(** The byte size of the type a pointer or array type points to ([[0, +oo]] when
    unknown); [None] for other types. *)

val cast_array : from:Sparrow_cil.typ -> into:Sparrow_cil.typ -> t -> t
(** Count offsets and sizes in elements of [into]'s pointee type instead of
    [from]'s. *)

val allocsites_of_array : t -> BasicDom.Allocsite.t BatSet.t
val pow_loc_of_array : t -> BasicDom.PowLoc.t
