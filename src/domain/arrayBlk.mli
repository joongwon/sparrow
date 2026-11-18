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
(** Array domain *)

(** The byte size of an element: one known non-negative size or unknown.
    [Size n] is built only by [of_int], which rejects negative [n]; [Top]
    stands for any non-negative size. *)
module Stride : sig
  type t = private Bot | Size of int | Top

  val bot : t
  val top : t
  val of_int : int -> t
  (** Raises [Invalid_argument] on a negative size. *)
  val one : t
  val join : t -> t -> t
  val meet : t -> t -> t
  val le : t -> t -> bool
  val eq : t -> t -> bool
  val widen : t -> t -> t
  val narrow : t -> t -> t
  val to_itv : t -> Itv.t
  (** [Top] is [\[0, +oo\]]. *)
  val to_string : t -> string
end

module ArrInfo : sig
  type t = {
    offset : Itv.t;
    size : Itv.t;
    stride : Stride.t;
    null_pos : Itv.t;
    structure : StructBlk.PowStruct.t;
  }

  val top : t
  val input : t
end

include MapDom.LAT with type A.t = BasicDom.Allocsite.t and type B.t = ArrInfo.t

val make : BasicDom.Allocsite.t -> Itv.t -> Itv.t -> Stride.t -> Itv.t -> t
val offsetof : t -> Itv.t
val sizeof : t -> Itv.t
val nullof : t -> Itv.t
val extern : BasicDom.Allocsite.t -> t
val input : BasicDom.Allocsite.t -> t
val weak_plus_size : t -> Itv.t -> t
val plus_offset : t -> Itv.t -> t
val minus_offset : t -> Itv.t -> t
val set_null_pos : t -> Itv.t -> t
val plus_null_pos : t -> Itv.t -> t
val cast_array : Sparrow_cil.typ -> t -> t
val allocsites_of_array : t -> BasicDom.Allocsite.t BatSet.t
val pow_loc_of_array : t -> BasicDom.PowLoc.t
val append_field : t -> Sparrow_cil.fieldinfo -> BasicDom.PowLoc.t
