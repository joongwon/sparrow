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
(** Map domain *)
open AbsDom
open Vocab

module type CPO =
sig
  include AbsDom.CPO
  module A : AbsDom.SET
  module B : AbsDom.CPO
  module PowA : PowDom.CPO with type elt = A.t

  (* reset this instance's value hash-cons table; see mapDom.mli *)
  val clear_b_table : unit -> unit

  val empty : t
  val is_empty : t -> bool
  val find : A.t -> t -> B.t
  val find_binding : A.t -> t -> (A.t * B.t) option
  val add_binding : A.t -> B.t -> t -> t
  val add : A.t -> B.t -> t -> t
  val weak_add : A.t -> B.t -> t -> t
  val remove : A.t -> t -> t
  val map : (B.t -> B.t) -> t -> t
  val mapi : (A.t -> B.t -> B.t) -> t -> t
  val fold : (A.t -> B.t -> 'a -> 'a) -> t -> 'a -> 'a
  val foldi : (A.t -> B.t -> 'a -> 'a) -> t -> 'a -> 'a
  val iter : (A.t -> B.t -> unit) -> t -> unit
  val mem : A.t -> t -> bool
  val filter : (A.t -> B.t -> bool) -> t -> t
  val cardinal : t -> int
  val choose : t -> (A.t * B.t)
  val to_string : t -> string
  val for_all : (A.t -> B.t -> bool) -> t -> bool
  val exists : (A.t -> B.t -> bool) -> t -> bool
  val keys : t -> PowA.t

  val unstables : t -> t -> (B.t -> B.t -> bool) -> PowA.t
    -> (A.t * B.t * B.t) list

  val join_pairs : (A.t * B.t) list -> t -> t
  val widen_pairs : (A.t * B.t) list -> t -> t
  val meet_big_small : t -> t -> t
end

module type LAT =
sig
  include AbsDom.LAT
  include CPO with type t := t
end

(* Mirror of the [Stdlib.Map] tree layout, read by [MakeCPO.rep_equal]. *)
type ('k, 'v) map_tree =
  | Map_empty
  | Map_node of ('k, 'v) map_tree * 'k * 'v * ('k, 'v) map_tree * int
[@@warning "-37"] (* built only by Stdlib.Map, read through %identity *)

let () =
  let module M = Map.Make (Int) in
  let map = List.fold_left (fun m k -> M.add k (k * 10) m) M.empty [5; 1; 9; 3; 7; 2] in
  let rec walk acc = function
    | Map_empty -> acc
    | Map_node (l, k, v, r, h) -> if h < 1 then raise Exit; walk ((k, v) :: walk acc r) l in
  let bindings = try Some (walk [] (Obj.magic map : (int, int) map_tree)) with Exit -> None in
  if bindings <> Some (M.bindings map) then
    failwith "MapDom: unexpected Map representation for hash-consing"

module MakeCPO (A:AbsDom.SET) (B:AbsDom.CPO) =
struct
  module BatMap = BatMap.Make(A)
  module PowA = PowDom.MakeCPO(A)

  type t = B.t BatMap.t [@@deriving compare]
  module A = A
  module B = B

  (* The layout of [Stdlib.Map.Make(_).t], which [BatMap.Make] includes:
     [Empty | Node of {l; v; d; r; h}].  Batteries reads the same layout
     through its own [%identity] casts; [check_map_layout] re-reads it. *)
  external tree_of_map : t -> (A.t, B.t) map_tree = "%identity"

  let key = HashconsKey.find A.compare
  let value = HashconsKey.find B.compare

  (* Representation identity (HashconsKey) of a map: the same tree shape and
     heights, representation-equal keys and values. *)
  let rep_equal : t -> t -> bool = fun x y ->
    let rec equal x y =
      x == y ||
      match x, y with
      | Map_empty, Map_empty -> true
      | Map_node (l1, k1, v1, r1, h1), Map_node (l2, k2, v2, r2, h2) ->
        h1 = h2 && key.HashconsKey.equal k1 k2 && value.HashconsKey.equal v1 v2
        && equal l1 l2 && equal r1 r2
      | _, _ -> false in
    equal (tree_of_map x) (tree_of_map y)

  (* The top three tree levels: at most seven bindings. *)
  let rep_hash : t -> int = fun x ->
    let mix = HashconsKey.mix in
    let rec hash depth = function
      | Map_empty -> 0
      | Map_node (l, k, v, r, h) ->
        if depth = 0 then h else
          mix (mix (mix (mix h (key.HashconsKey.hash k)) (value.HashconsKey.hash v))
                 (hash (depth - 1) l)) (hash (depth - 1) r) in
    hash 3 (tree_of_map x)

  let () = HashconsKey.register compare { HashconsKey.equal = rep_equal; hash = rep_hash }

  (* Hash-cons abstract values so identical B.t objects (e.g. the same interval
     held at thousands of CFG nodes) are physically shared across all per-node
     memories instead of duplicated. Values are
     immutable, so sharing is semantics-preserving; the table holds one copy per
     distinct value (bounded in practice for the interval lattice).
     The key is B's representation identity (HashconsKey), never a polymorphic
     comparison: a value's locations carry CIL types that may be cyclic and,
     in separately marshaled values, decoded separately, so a
     structural lookup could walk them forever. *)
  let b_table = HashconsKey.create value
  let b_hashcons (v : B.t) : B.t = HashconsKey.intern b_table v
  (* drop the accumulated hash-cons table; sound (values are immutable and stay
     valid), only loses cross-solve sharing.  See mapDom.mli. *)
  let clear_b_table () = HashconsKey.clear b_table

  let to_string : t -> string = fun x ->
    let add_string_of_k_v k v acc =
      let str = A.to_string k ^ " -> " ^ B.to_string v in
      acc ^ "\n" ^ str
    in
    if BatMap.is_empty x then "bot"
    else "{" ^ BatMap.fold add_string_of_k_v x "" ^ "}"

  let cardinal = BatMap.cardinal
  let choose = BatMap.choose

  (* [le] and [eq] walk both maps in ascending key order in lockstep and
     apply [B.le]/[B.eq] to exactly the pairs, in exactly the order, that
     the [BatMap.enum] walk did, with the same early exits.  Each map's
     cursor is an explicit stack of the nodes whose key is still to come
     (at most the tree height), so a step allocates nothing. *)
  let tree_height = function Map_empty -> 0 | Map_node (_, _, _, _, h) -> h

  (* Push [node] and its left spine above [top]; the new top. *)
  let rec push_left stack top = function
    | Map_empty -> top
    | Map_node (l, _, _, _, _) as node ->
      Array.unsafe_set stack top node;
      push_left stack (top + 1) l

  (* Drop the current binding (the node below [top]) and move to its
     successor. *)
  let advance stack top =
    match Array.unsafe_get stack (top - 1) with
    | Map_node (_, _, _, r, _) -> push_left stack (top - 1) r
    | Map_empty -> assert false

  let cursor tree =
    let stack = Array.make (tree_height tree + 1) Map_empty in
    (stack, push_left stack 0 tree)

  (* [x] against the empty map: every remaining binding of [x] must satisfy
     [test v B.bot], in ascending order. *)
  let rec all_bot test = function
    | Map_empty -> true
    | Map_node (l, _, v, r, _) -> all_bot test l && test v B.bot && all_bot test r

  let le : t -> t -> bool = fun x y ->
    if x == y then true else
    let tx = tree_of_map x and ty = tree_of_map y in
    match tx, ty with
    | _, Map_empty -> all_bot B.le tx
    | Map_empty, _ -> true
    | _, _ ->
      let s1, top1 = cursor tx and s2, top2 = cursor ty in
      let rec loop t1 t2 =
        if t1 = 0 then true
        else
          match Array.unsafe_get s1 (t1 - 1) with
          | Map_empty -> assert false
          | Map_node (_, k1, v1, _, _) ->
            if t2 = 0 then
              if B.le v1 B.bot then loop (advance s1 t1) t2 else false
            else
              match Array.unsafe_get s2 (t2 - 1) with
              | Map_empty -> assert false
              | Map_node (_, k2, v2, _, _) ->
                let c = if k1 == k2 then 0 else A.compare k1 k2 in
                if c = 0 then
                  if B.le v1 v2 then loop (advance s1 t1) (advance s2 t2) else false
                else if c < 0 then
                  if B.le v1 B.bot then loop (advance s1 t1) t2 else false
                else loop t1 (advance s2 t2)
      in
      loop top1 top2

  let eq : t -> t -> bool = fun x y ->
    if x == y then true else
    let tx = tree_of_map x and ty = tree_of_map y in
    match tx, ty with
    | _, Map_empty -> all_bot B.eq tx
    | Map_empty, _ -> all_bot B.eq ty
    | _, _ ->
      let s1, top1 = cursor tx and s2, top2 = cursor ty in
      let rec loop t1 t2 =
        if t1 = 0 then
          if t2 = 0 then true
          else
            match Array.unsafe_get s2 (t2 - 1) with
            | Map_empty -> assert false
            | Map_node (_, _, v2, _, _) ->
              if B.eq v2 B.bot then loop t1 (advance s2 t2) else false
        else
          match Array.unsafe_get s1 (t1 - 1) with
          | Map_empty -> assert false
          | Map_node (_, k1, v1, _, _) ->
            if t2 = 0 then
              if B.eq v1 B.bot then loop (advance s1 t1) t2 else false
            else
              match Array.unsafe_get s2 (t2 - 1) with
              | Map_empty -> assert false
              | Map_node (_, k2, v2, _, _) ->
                let c = if k1 == k2 then 0 else A.compare k1 k2 in
                if c = 0 then
                  if B.eq v1 v2 then loop (advance s1 t1) (advance s2 t2) else false
                else if c < 0 then
                  if B.eq v1 B.bot then loop (advance s1 t1) t2 else false
                else if B.eq v2 B.bot then loop t1 (advance s2 t2) else false
      in
      loop top1 top2

  let bot : t = BatMap.empty

  let filter = BatMap.filter
  let join : t -> t -> t = fun x y ->
    if x == y then y else
    if le x y then y else
    if le y x then x else
      let join' k opt_v1 opt_v2 =
        match opt_v1, opt_v2 with
        | None, None -> None
        | None, Some v
        | Some v, None -> if B.eq v B.bot then None else Some v
        | Some v1, Some v2 ->
          let joined_v = b_hashcons (B.join v1 v2) in
          if B.eq joined_v B.bot then None else Some joined_v in
      BatMap.merge join' x y

  let meet : t -> t -> t = fun x y ->
    if x == y then y else
    if le x y then x else
    if le y x then y else
      let meet' k opt_v1 opt_v2 =
        match opt_v1, opt_v2 with
        | None, _
        | _, None -> None
        | Some v1, Some v2 ->
          let meeted_v = b_hashcons (B.meet v1 v2) in
          if B.eq meeted_v B.bot then None else Some meeted_v in
      BatMap.merge meet' x y

  let widen : t -> t -> t = fun x y ->
    if x == y then x else
      let widen' k opt_v1 opt_v2 =
        match opt_v1, opt_v2 with
        | None, None -> None
        | None, Some v
        | Some v, None -> if B.eq v B.bot then None else Some v
        | Some v1, Some v2 ->
          let widened_v = b_hashcons (B.widen v1 v2) in
          if B.eq widened_v B.bot then None else Some widened_v in
      BatMap.merge widen' x y

  let narrow : t -> t -> t = fun x y ->
    if x == y then x else
      let narrow' k opt_v1 opt_v2 =
        match opt_v1, opt_v2 with
        | _, None | None, _ -> None
        | Some v1, Some v2 ->
          let narrowed_v = b_hashcons (B.narrow v1 v2) in
          if B.eq narrowed_v B.bot then None else Some narrowed_v in
      BatMap.merge narrow' x y


  (** {6 Functions for map} *)


  let empty : t = BatMap.empty

  let is_empty : t -> bool = BatMap.is_empty

  let find : A.t -> t -> B.t = fun k a -> try BatMap.find k a with _ -> B.bot

  let find_binding : A.t -> t -> (A.t * B.t) option = fun k a ->
    match BatMap.find_first_opt (fun candidate -> A.compare candidate k >= 0) a with
    | Some (resident, value) when A.compare resident k = 0 ->
      Some (resident, value)
    | Some _ | None -> None

  let add_binding : A.t -> B.t -> t -> t = fun k v x ->
    if B.eq v B.bot then BatMap.remove k x else BatMap.add k v x

  let add : A.t -> B.t -> t -> t = fun k v x ->
    if B.eq v B.bot then BatMap.remove k x else BatMap.add k (b_hashcons v) x

  let weak_add : A.t -> B.t -> t -> t = fun k v x ->
    if B.eq v B.bot then x else
      BatMap.modify_def (b_hashcons v) k (fun orig_v ->
        if B.le v orig_v then orig_v
        else if B.le orig_v v then b_hashcons v
        else b_hashcons (B.join orig_v v)) x

  let widen_add : A.t -> B.t -> t -> t = fun k v x ->
    if B.eq v B.bot then x else
      BatMap.modify_def (b_hashcons v) k (fun orig_v ->
        if B.le v orig_v then orig_v
        else b_hashcons (B.widen orig_v v)) x

  let remove : A.t -> t -> t = BatMap.remove
  let iter = BatMap.iter

  (* Type of map is restricted to return the same type.  *)
  (** The first argument of map,  function f,  should preserve the
      bottom value for consistency,  e.g. [f B.bot = B.bot].  Since
      [\[x |-> B.bot\]] and [\[ \]] are the same map,  it is natural
      that [map f \[x |-> B.bot\]] and [map f \[ \]] return the same
      value.  *)
  let map f = BatMap.map (fun v -> b_hashcons (f v))

  let mapi f = BatMap.mapi (fun k v -> b_hashcons (f k v))

  (** The first argument of map,  function f,  should preserve the
      bottom value for consistency,  e.g. [f B.bot acc = acc].  Since
      [\[x |-> B.bot\]] and [\[ \]] are the same map,  it is natural
      that [fold f \[x |-> B.bot\] acc] and [fold f \[ \] acc] return
      the same value.  *)
  let fold : (A.t -> B.t -> 'a -> 'a) -> t -> 'a -> 'a = BatMap.fold

  let foldi : (A.t -> B.t -> 'a -> 'a) -> t -> 'a -> 'a = BatMap.fold

  (** {6 Functions for an efficient fixpoint iteration} *)

  (** Calculate unstable memory entries and values.

      Returns a list of triples, (key, old value, new value).
  *)
  let unstables : t -> t -> (B.t -> B.t -> bool) -> PowA.t
    -> (A.t * B.t * B.t) list
  = fun old_m new_m is_unstb candidate ->
    let e_old = BatMap.enum old_m in
    let e_new = BatMap.enum new_m in

    (* loop (old memory) (new memory) candiate (unstable keys) *)
    let rec loop kv1 kv2 unstb =
      match kv1, kv2 with
      | _, None -> unstb
      | None, Some (k2, v2) ->
        if PowA.mem k2 candidate then loop kv1 (BatEnum.get e_new) ((k2,B.bot,v2)::unstb)
        else loop kv1 (BatEnum.get e_new) unstb
      | Some (k1, v1), Some (k2, v2) ->
        let cmp = A.compare k1 k2 in
        if cmp < 0 then
          loop (BatEnum.get e_old) kv2 unstb
        else if cmp > 0 then
          if v2 <> B.bot && PowA.mem k2 candidate then
            loop kv1 (BatEnum.get e_new) ((k2,B.bot,v2)::unstb)
          else
            loop kv1 (BatEnum.get e_new) unstb
        else
          if is_unstb v1 v2 && PowA.mem k2 candidate then
            loop (BatEnum.get e_old) (BatEnum.get e_new) ((k1,v1,v2)::unstb)
          else
            loop (BatEnum.get e_old) (BatEnum.get e_new) unstb
    in
    let init_old = BatEnum.get e_old in
    let init_new = BatEnum.get e_new in
    loop init_old init_new []

  let add_pairs : (A.t -> B.t -> t -> t) -> (A.t * B.t) list -> t -> t
  = fun add_f pairs m ->
    let add_pair (k, v) m = if B.eq v B.bot then m else add_f k v m in
    list_fold add_pair pairs m

  let join_pairs : (A.t * B.t) list -> t -> t = add_pairs weak_add

  let widen_pairs : (A.t * B.t) list -> t -> t = add_pairs widen_add

  let keys m = foldi (fun k _ -> PowA.add k) m PowA.empty

  let mem = BatMap.mem

  let for_all = BatMap.for_all

  let exists = BatMap.exists

  let bindings = BatMap.bindings

  let le_small_big : t -> t -> bool = fun small_x big_y ->
    let le_a_map k v acc = acc && B.le v (find k big_y) in
    foldi le_a_map small_x true

  let meet_big_small : t -> t -> t = fun big_x small_y ->
    let meet_a_map k v = B.meet v (find k big_x) in
    if le_small_big small_y big_x then small_y else
      mapi meet_a_map small_y

  let pp fmt m =
    let rec pp_map fmt = function
      | [] -> ()
      | [(k, v)] -> Format.fprintf fmt "@[<h>%a -> %a@]" A.pp k B.pp v
      | (k, v)::t -> Format.fprintf fmt "@[<h>%a -> %a@\n@]" A.pp k B.pp v; pp_map fmt t
    in
    if is_empty m then Format.fprintf fmt "bot"
    else Format.fprintf fmt "@[<hov 2>{ %a }@]" pp_map (bindings m)
end

module MakeLAT (A:AbsDom.SET) (B:AbsDom.CPO) =
struct
  module A = A
  module B = B
  module MapCPO = MakeCPO(A)(B)
  module PowA = PowDom.MakeCPO(A)

  type t = V of MapCPO.t | Top [@@deriving compare]

  let bot = V MapCPO.bot
  let top = Top

  let clear_b_table () = MapCPO.clear_b_table ()

  let () =
    let map = HashconsKey.find MapCPO.compare in
    HashconsKey.register compare {
      HashconsKey.equal = (fun x y -> x == y || match x, y with
        | V x, V y -> map.HashconsKey.equal x y
        | Top, Top -> true
        | _, _ -> false);
      hash = (function V x -> map.HashconsKey.hash x | Top -> 1) }

  let to_string = function
    | V x -> MapCPO.to_string x
    | Top -> "top"

  let cardinal = function
    | V m -> MapCPO.cardinal m
    | Top -> raise (Failure "Error: cardinal")

  let choose = function
    | V m -> MapCPO.choose m
    | Top -> raise (Failure "Error: choose")

  let le x y =
    match x, y with
    | V x, V y -> MapCPO.le x y
    | _, Top -> true
    | _, _ -> false


  let eq x y =
    match x, y with
    | V x, V y -> MapCPO.eq x y
    | Top, Top -> true
    | _, _ -> false

  let filter p = function
    | V m -> V (MapCPO.filter p m)
    | Top -> raise (Failure "Error: filter")

  let join x y =
    match x, y with
    | V x, V y -> V (MapCPO.join x y)
    | _, Top | Top, _ -> top

  let meet x y =
    match x, y with
    | V x, V y -> V (MapCPO.meet x y)
    | _, Top -> x
    | Top, y -> y

  let widen x y =
    match x, y with
    | V x, V y -> V (MapCPO.widen x y)
    | _, Top | Top, _ -> top

  let narrow x y =
    match x, y with
    | V x, V y -> V (MapCPO.narrow x y)
    | Top, _ -> y
    | _, Top -> x

  (** {6 Functions for map} *)

  let empty = V MapCPO.empty

  let is_empty = function
    | Top -> false | V m -> MapCPO.is_empty m

  let find k = function
    | V m -> MapCPO.find k m
    | Top -> raise (Failure "Error: find")

  let find_binding k = function
    | V m -> MapCPO.find_binding k m
    | Top -> raise (Failure "Error: find_binding")

  let add_binding k v = function
    | V m -> V (MapCPO.add_binding k v m)
    | Top -> top

  let add k v = function
    | V x -> V (MapCPO.add k v x)
    | Top -> top

  let weak_add k v = function
    | V m -> V (MapCPO.weak_add k v m)
    | Top -> top

  let widen_add k v = function
    | V m -> V (MapCPO.widen_add k v m)
    | Top -> top

  let remove k = function
    | V m -> V (MapCPO.remove k m)
    | Top -> top

  let iter f = function
    | V m -> MapCPO.iter f m
    | Top -> ()

  (* Type of map is restricted to return the same type.  *)
  (** The first argument of map,  function f,  should preserve the
      bottom value for consistency,  e.g. [f B.bot = B.bot].  Since
      [\[x |-> B.bot\]] and [\[ \]] are the same map,  it is natural
      that [map f \[x |-> B.bot\]] and [map f \[ \]] return the same
      value.  *)
  let map f = function
    | V m -> V (MapCPO.map f m)
    | Top -> Top

  let mapi f = function
    | V m -> V (MapCPO.mapi f m)
    | Top -> Top

  (** The first argument of map,  function f,  should preserve the
      bottom value for consistency,  e.g. [f B.bot acc = acc].  Since
      [\[x |-> B.bot\]] and [\[ \]] are the same map,  it is natural
      that [fold f \[x |-> B.bot\] acc] and [fold f \[ \] acc] return
      the same value.  *)
  let fold f x a =
    match x with
    | V m -> MapCPO.fold f m a
    | Top -> a

  let foldi = fold

  (** {6 Functions for an efficient fixpoint iteration} *)

  (** Calculate unstable memory entries and values.

      Returns a list of triples, (key, old value, new value).
  *)
  let unstables old_m new_m is_unstb candidate =
    match old_m, new_m with
    | V old_m, V new_m -> MapCPO.unstables old_m new_m is_unstb candidate
    | _, _ -> raise (Failure "unstable")

  let add_pairs add_f pairs m =
    let add_pair (k, v) m = if B.eq v B.bot then m else add_f k v m in
    list_fold add_pair pairs m

  let join_pairs = add_pairs weak_add

  let widen_pairs = add_pairs widen_add

  let keys m = foldi (fun k _ -> PowA.add k) m PowA.empty

  let mem k = function
    | V m -> MapCPO.mem k m
    | Top -> raise (Failure "Error: mem")

  let for_all f = function
    | V m -> MapCPO.for_all f m
    | Top -> raise (Failure "Error: for_all")

  let exists f = function
    | V m -> MapCPO.exists f m
    | Top -> raise (Failure "Error: for_all")

  let bindings = function
    | V m -> MapCPO.bindings m
    | Top -> raise (Failure "Error: bindings")

  let le_small_big : t -> t -> bool = fun small_x big_y ->
    let le_a_map k v acc = acc && B.le v (find k big_y) in
    foldi le_a_map small_x true

  let meet_big_small : t -> t -> t = fun big_x small_y ->
    let meet_a_map k v = B.meet v (find k big_x) in
    if le_small_big small_y big_x then small_y else
      mapi meet_a_map small_y

  let pp fmt = function
    | V m -> MapCPO.pp fmt m
    | Top -> Format.fprintf fmt "top"
end
