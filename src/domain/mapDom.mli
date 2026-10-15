(** Map domain *)
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

module type CPO = sig
  include AbsDom.CPO
  module A : AbsDom.SET
  module B : AbsDom.CPO
  module PowA : PowDom.CPO with type elt = A.t

  val empty : t
  val is_empty : t -> bool
  val find : A.t -> t -> B.t
  val add : A.t -> B.t -> t -> t
  val weak_add : A.t -> B.t -> t -> t
  val remove : A.t -> t -> t

  val map : (B.t -> B.t) -> t -> t
  (** When calling [map f m], function [f] should preserve the bottom value for
      consistency, i.e. [f B.bot = B.bot]. Since [[x |-> B.bot]] and [[ ]] are
      the same map, it is natural that [map f [x |-> B.bot]] and [map f [ ]]
      return the same value. *)

  val mapi : (A.t -> B.t -> B.t) -> t -> t

  val fold : (A.t -> B.t -> 'a -> 'a) -> t -> 'a -> 'a
  (** When calling [fold f m acc], function [f] should ignore the bottom value
      for consistency, i.e. [f x B.bot acc = acc]. Since [[x |-> B.bot]] and
      [[ ]] are the same map, it is natural that [fold f [x |-> B.bot] acc] and
      [fold f [ ] acc] return the same value. *)

  val foldi : (A.t -> B.t -> 'a -> 'a) -> t -> 'a -> 'a
  (** Same as [fold] *)

  val iter : (A.t -> B.t -> unit) -> t -> unit
  val mem : A.t -> t -> bool
  val filter : (A.t -> B.t -> bool) -> t -> t
  val cardinal : t -> int
  val choose : t -> A.t * B.t
  val to_string : t -> string
  val for_all : (A.t -> B.t -> bool) -> t -> bool
  val exists : (A.t -> B.t -> bool) -> t -> bool
  val keys : t -> PowA.t

  val unstables :
    t -> t -> (B.t -> B.t -> bool) -> PowA.t -> (A.t * B.t * B.t) list
  (** [unstable old_m new_m is_unstb candidate] calculate unstable memory
      entries and values. Returns a list of triples, (key, old value, new
      value).
      @param old_m old memory
      @param new_m new memory
      @param is_unstb
        [is_unstb old_v new_v] returns true if the value is unstable
      @param candidate candidate keys to check for instability *)

  val join_pairs : (A.t * B.t) list -> t -> t
  val widen_pairs : (A.t * B.t) list -> t -> t
  val meet_big_small : t -> t -> t
end

module type LAT = sig
  include AbsDom.LAT
  include CPO with type t := t
end

module MakeCPO (A : AbsDom.SET) (B : AbsDom.CPO) :
  CPO
    with type t = B.t BatMap.Make(A).t
     and type PowA.t = PowDom.MakeCPO(A).t
     and type A.t = A.t
     and type B.t = B.t

module MakeLAT (A : AbsDom.SET) (B : AbsDom.CPO) :
  LAT with type A.t = A.t and type B.t = B.t
