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
(** Powset domain *)
open AbsDom
open Vocab

module type CPO =
sig
  include CPO
  type elt


  val empty : t
  val filter : (elt -> bool) -> t -> t
  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
  val fold2 : (elt -> elt -> 'a -> 'a) -> t -> t -> 'a -> 'a
  val map : (elt -> elt) -> t -> t
  val iter : (elt -> unit) -> t -> unit

  val singleton : elt -> t
  val subset : t -> t -> bool
  val cardinal : t -> int

  val mem : elt -> t -> bool

  val add : elt -> t -> t
  val diff : t -> t -> t

  val choose : t -> elt

  val remove : elt -> t -> t

  val is_empty : t -> bool

  val union : t -> t -> t
  val union_small_big : t -> t -> t
  (* [union] and [inter] without hash-consing, for sets that are not kept *)
  val union_unshared : t -> t -> t
  val inter_unshared : t -> t -> t

  val inter : t -> t -> t
  val for_all : (elt -> bool) -> t -> bool
  val exists : (elt -> bool) -> t -> bool
  val of_list : elt list -> t
  val elements : t -> elt list
end

module type LAT =
sig
  include AbsDom.LAT
  include CPO with type t := t
end

(* Mirror of the [Stdlib.Set] tree layout, read by [MakeCPO.rep_equal]. *)
type 'a set_tree = Set_empty | Set_node of 'a set_tree * 'a * 'a set_tree * int
[@@warning "-37"] (* built only by Stdlib.Set, read through %identity *)

let () =
  let module S = Set.Make (Int) in
  let set = S.of_list [5; 1; 9; 3; 7; 2] in
  let rec walk acc = function
    | Set_empty -> acc
    | Set_node (l, v, r, h) -> if h < 1 then raise Exit; walk (v :: walk acc r) l in
  let elements = try Some (walk [] (Obj.magic set : int set_tree)) with Exit -> None in
  if elements <> Some (S.elements set) then
    failwith "PowDom: unexpected Set representation for hash-consing"

module MakeCPO (A:SET) =
struct
  module BatSet = BatSet.Make(A)
  type elt = A.t
  type t = BatSet.t

  let compare = BatSet.compare

  let to_string : t -> string = fun x ->
    if BatSet.is_empty x then "bot" else
      let add_string_of_v v acc = link_by_sep "," (A.to_string v) acc in
      "{" ^ BatSet.fold add_string_of_v x "" ^ "}"

  let le : t -> t -> bool = fun x y ->
    if x == y then true else BatSet.subset x y

  let eq : t -> t -> bool = fun x y ->
    if x == y then true else BatSet.equal x y

  (* The layout of [Stdlib.Set.Make(_).t], which [BatSet.Make] includes:
     [Empty | Node of {l; v; r; h}].  Batteries reads the same layout through
     its own [%identity] casts; [check_tree_layout] re-reads it at start-up. *)
  external tree_of_set : t -> elt set_tree = "%identity"

  let element = HashconsKey.find A.compare

  (* Representation identity (HashconsKey): the same tree shape and heights
     with representation-equal elements. *)
  let rep_equal : t -> t -> bool = fun x y ->
    let rec equal x y =
      x == y ||
      match x, y with
      | Set_empty, Set_empty -> true
      | Set_node (l1, v1, r1, h1), Set_node (l2, v2, r2, h2) ->
        h1 = h2 && element.HashconsKey.equal v1 v2 && equal l1 l2 && equal r1 r2
      | _, _ -> false in
    equal (tree_of_set x) (tree_of_set y)

  (* The top three tree levels: at most seven elements. *)
  let rep_hash : t -> int = fun x ->
    let rec hash depth = function
      | Set_empty -> 0
      | Set_node (l, v, r, h) ->
        if depth = 0 then h else
          HashconsKey.mix
            (HashconsKey.mix (HashconsKey.mix h (element.HashconsKey.hash v)) (hash (depth - 1) l))
            (hash (depth - 1) r) in
    hash 3 (tree_of_set x)

  let () = HashconsKey.register compare { HashconsKey.equal = rep_equal; hash = rep_hash }

  (* Hash-cons location sets: each distinct set becomes one physical object
     shared across all node memories.  The table is global and never cleared.
     The key is representation identity, never a polymorphic comparison that
     could walk a cyclic CIL type, so the table also serves values whose
     types were decoded separately (marshaled values). *)
  let table = HashconsKey.create { HashconsKey.equal = rep_equal; hash = rep_hash }
  let hashcons x = HashconsKey.intern table x

  let bot = BatSet.empty
  let empty = bot

  let join : t -> t -> t = fun x y ->
    if le x y then y else
    if le y x then x else
      hashcons (BatSet.union x y)
  let union = join
  let union_small_big small big = BatSet.fold BatSet.add small big
  let union_unshared = BatSet.union
  let inter_unshared = BatSet.inter

  let meet : t -> t -> t = fun x y ->
    if le x y then x else
    if le y x then y else
      hashcons (BatSet.inter x y)
  let inter = meet

  (* Since module A is finite,  widening is defined as union which is
     sufficient to guarantee analysis termination.  *)
  let widen : t -> t -> t = fun x y ->
    if x == y then x else
      hashcons (BatSet.union x y)

  let narrow : t -> t -> t = fun x y ->
    if x == y then x else
      hashcons (BatSet.inter x y)


  let filter : (elt -> bool) -> t -> t = fun f s ->
    BatSet.filter f s

  let fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a = BatSet.fold
  let fold2 : (elt -> elt -> 'a -> 'a) -> t -> t -> 'a -> 'a
  = fun f s1 s2 -> BatSet.fold (fun x -> BatSet.fold (f x) s2) s1

  let map = BatSet.map

  let iter : (elt -> unit) -> t -> unit = BatSet.iter

  let singleton : elt -> t = fun e ->
    BatSet.singleton e

  let subset : t -> t -> bool = BatSet.subset

  let cardinal : t -> int = BatSet.cardinal

  let mem : elt -> t -> bool = BatSet.mem

  let add e s = BatSet.add e s
  let diff = BatSet.diff

  let choose = BatSet.choose

  let remove = BatSet.remove

  let elements = BatSet.elements
  let is_empty = BatSet.is_empty

  let for_all = BatSet.for_all
  let exists = BatSet.exists
  let of_list = BatSet.of_list

  let pp fmt x =
    let rec pp_elt fmt x =
      if cardinal x = 1 then Format.fprintf fmt "@[<h>%a@]" A.pp (choose x)
      else iter (fun elt -> Format.fprintf fmt "@[<h>%a,@]" A.pp elt) x
    in
    if is_empty x then Format.fprintf fmt "bot"
    else Format.fprintf fmt "@[<hov 2>{%a}@]" pp_elt x
end

module MakeLAT (A:SET) =
struct
  module PowCPO = MakeCPO(A)
  type t = V of PowCPO.t | Top [@@deriving compare]
  type elt = A.t


  let () =
    let set = HashconsKey.find PowCPO.compare in
    HashconsKey.register compare {
      HashconsKey.equal = (fun x y -> x == y || match x, y with
        | V x, V y -> set.HashconsKey.equal x y
        | Top, Top -> true
        | _, _ -> false);
      hash = (function V x -> set.HashconsKey.hash x | Top -> 1) }

  exception Error

  let to_string = function
    | Top -> "top"
    | V x -> PowCPO.to_string x

  let le x y =
    match x, y with
    | V x, V y -> PowCPO.le x y
    | _, Top -> true
    | _, _ -> false

  let eq x y =
    match x, y with
    | V x, V y -> PowCPO.eq x y
    | Top, Top -> true
    | _, _ -> false

  let bot = V PowCPO.bot
  let top = Top
  let empty = bot

  let join x y =
    match x, y with
    | V x, V y -> V (PowCPO.join x y)
    | Top, _ | _, Top -> top

  let union = join

  let union_small_big small big =
    match small, big with
    | V small, V big -> V (PowCPO.union_small_big small big)
    | Top, _ | _, Top -> top

  let union_unshared x y =
    match x, y with
    | V x, V y -> V (PowCPO.union_unshared x y)
    | Top, _ | _, Top -> top

  let inter_unshared x y =
    match x, y with
    | V x, V y -> V (PowCPO.inter_unshared x y)
    | Top, _ -> y
    | _, Top -> x

  let meet x y =
    match x, y with
    | V x, V y -> V (PowCPO.meet x y)
    | Top, _ -> y
    | _, Top -> x

  let inter = meet

  (* Since module A is finite,  widening is defined as union which is
     sufficient to guarantee analysis termination.  *)
  let widen = join

  let narrow = meet

  let filter f = function
    | V s -> V (PowCPO.filter f s)
    | Top -> top

  let fold f s a =
    match s with
    | V s -> PowCPO.fold f s a
    | Top -> a


  let fold2 : (elt -> elt -> 'a -> 'a) -> t -> t -> 'a -> 'a
  = fun f s1 s2 -> fold (fun x -> fold (f x) s2) s1

  let map f s =
    match s with
    | Top -> top
    | V s -> V (PowCPO.map f s)

  let iter : (elt -> unit) -> t -> unit
  = fun f s ->
    match s with
    | Top -> ()
    | V s -> PowCPO.iter f s

  let singleton e = V (PowCPO.singleton e)

  let subset = le

  let cardinal = function
    | V s -> PowCPO.cardinal s
    | Top -> -1

  let mem e = function
    | V s -> PowCPO.mem e s
    | Top -> true

  let add e = function
    | V s -> V (PowCPO.add e s)
    | Top -> Top

  let diff x y =
    match x, y with
    | V x, V y -> V (PowCPO.diff x y)
    | Top, _ -> top
    | _, Top -> bot

  let choose = function
    | V s -> PowCPO.choose s
    | Top -> raise (Failure "Error: choose")

  let remove e = function
    | V s -> V (PowCPO.remove e s)
    | Top -> top

  let elements = function
    | V s -> PowCPO.elements s
    | Top -> raise (Failure "Error: elements")

  let is_empty = function
    | V s -> PowCPO.is_empty s
    | _ -> false

  let for_all f = function
    | V s -> PowCPO.for_all f s
    | _ -> false

  let exists f = function
    | V s -> PowCPO.exists f s
    | _ -> false

  let of_list s = V (PowCPO.of_list s)

  let pp fmt = function
    | V s -> PowCPO.pp fmt s
    | _ -> Format.fprintf fmt "top"
end
