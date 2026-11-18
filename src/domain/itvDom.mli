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
(** Abstract domains of interval analysis *)
module Val : sig
  include AbsDom.CPO

  val null : t
  val make : Itv.t * BasicDom.PowLoc.t * ArrayBlk.t * BasicDom.PowProc.t -> t
  val itv_of_val : t -> Itv.t
  val pow_loc_of_val : t -> BasicDom.PowLoc.t
  val array_of_val : t -> ArrayBlk.t
  val pow_proc_of_val : t -> BasicDom.PowProc.t
  val allocsites_of_val : t -> BasicDom.Allocsite.t BatSet.t
  val all_loc_of_val : t -> BasicDom.PowLoc.t
  val of_itv : Itv.t -> t
  val of_pow_loc : BasicDom.PowLoc.t -> t
  val of_array : ArrayBlk.t -> t
  val of_pow_proc : BasicDom.PowProc.t -> t
  val modify_itv : Itv.t -> t -> t
  val modify_arr : ArrayBlk.t -> t -> t
  val external_value : BasicDom.Allocsite.t -> t
  val itv_top : t
  val cast : Sparrow_cil.typ -> Sparrow_cil.typ -> t -> t
end

(** What operations may change about the object a cell holds, kept in memory so
    that every reference sees the change; what is fixed when a pointer is made
    (an array's size) stays in the pointer. *)
module CellInfo : sig
  type t = { null_pos : Itv.t }
  (** [null_pos]: the index of the first null character of the char array whose
      elements the cell holds (bot: unknown). *)

  include AbsDom.CPO with type t := t

  val of_null : Itv.t -> t
end

(** The contents of a cell: the stored value and the cell's info. *)
module Cell : sig
  include AbsDom.CPO with type t = Val.t * CellInfo.t

  val make : Val.t -> CellInfo.t -> t
  val fst : t -> Val.t
  val snd : t -> CellInfo.t
end

module Mem : sig
  include InstrumentedMem.S

  val lookup : BasicDom.PowLoc.t -> t -> Val.t
  val lookup_info : BasicDom.PowLoc.t -> t -> CellInfo.t
  val strong_update : BasicDom.PowLoc.t -> Val.t -> t -> t
  val weak_update : BasicDom.PowLoc.t -> Val.t -> t -> t
  val strong_update_info : BasicDom.PowLoc.t -> CellInfo.t -> t -> t
  val weak_update_info : BasicDom.PowLoc.t -> CellInfo.t -> t -> t
end
with type A.t = BasicDom.Loc.t
 and type B.t = Cell.t
 and type PowA.t = BasicDom.PowLoc.t

module Table :
  MapDom.CPO
    with type t = MapDom.MakeCPO(BasicDom.Node)(Mem).t
     and type A.t = BasicDom.Node.t
     and type B.t = Mem.t
