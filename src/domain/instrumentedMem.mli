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
type 'keys read_log = {
  read_keys : 'keys;
  read_whole_memory : string list;
  read_bottom_true : bool;
}
(** A pure-read log (observation only; see instrumentedMem.ml). *)

module type S = sig
  include MapDom.CPO
  module Access : Access.S with type Loc.t = A.t and type PowLoc.t = PowA.t

  val init_access : unit -> unit
  val return_access : unit -> Access.info
  val observe_read : A.t -> t -> unit
  val find_unobserved : A.t -> t -> B.t
  val start_read_log : unit -> unit
  val stop_read_log : unit -> PowA.t read_log
end

module Make (Mem : MapDom.CPO) :
  S
    with type t = Mem.t
     and type A.t = Mem.A.t
     and type B.t = Mem.B.t
     and type PowA.t = Mem.PowA.t
