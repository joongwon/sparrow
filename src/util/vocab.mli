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
(** Vocabularies *)

val ( <<< ) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
val ( >>> ) : ('a -> 'b) -> ('b -> 'c) -> 'a -> 'c
val ( $> ) : 'a option -> ('a -> 'b option) -> 'b option
val ( &> ) : 'a option -> ('a -> 'b) -> 'b option
val ( @ ) : 'a list -> 'a list -> 'a list
val id : 'a -> 'a
val flip : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c

val cond : bool -> ('a -> 'b) -> ('a -> 'b) -> 'a -> 'b
(** [cond b f1 f2 x] returns [f1 x] if [b] is true, and [f2 x] otherwise. *)

val opt : bool -> ('a -> 'a) -> 'a -> 'a
(** [opt b f x] returns [f x] if [b] is true, and [x] otherwise. *)

val case : (bool * ('a -> 'b)) list -> ('a -> 'b) -> 'a -> 'b
(** [case [(cond1, f1); (cond2, f2); ...] default x] returns [f1 x] if [cond1]
    is true, [f2 x] if [cond2] is true, and so on, or [default x] if none of the
    conditions are true. *)

val tuple : 'a -> 'a * 'a
val compare_string : string -> string -> int
val compare_bool : bool -> bool -> int
val compare_int : int -> int -> int
val domof : ('a, 'b) BatMap.t -> 'a BatSet.t

val list_fold : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
(** [init |> list_fold f [a1; a2; ...; an]] computes
    [init |> f a1 |> f a2 |> ... |> f an]. *)

val list_fold2 : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
val list_rev : 'a list -> 'a list
val append_opt : 'a option -> 'a list -> 'a list
val find_opt : 'a -> ('a, 'b) BatMap.t -> 'b option
val find_def : 'a -> ('a, 'b) BatMap.t -> 'b -> 'b
val link_by_sep : string -> string -> string -> string

val string_of_list :
  ?first:string ->
  ?last:string ->
  ?sep:string ->
  ('a -> string) ->
  'a list ->
  string

val string_of_set :
  ?first:string ->
  ?last:string ->
  ?sep:string ->
  ('a -> string) ->
  'a BatSet.t ->
  string

val string_of_map :
  ?first:string ->
  ?last:string ->
  ?sep:string ->
  ?indent:string ->
  ('a -> string) ->
  ('b -> string) ->
  ('a, 'b) BatMap.t ->
  string

val i2s : int -> string
val list2set : 'a list -> 'a BatSet.t
val set2list : 'a BatSet.t -> 'a list
val set_union_small_big : 'a BatSet.t -> 'a BatSet.t -> 'a BatSet.t
val prerr_progressbar : ?itv:int -> int -> int -> unit
val fix : ('a BatSet.t -> 'a BatSet.t) -> 'a BatSet.t -> 'a BatSet.t
val my_prerr_endline : string -> unit
val my_prerr_newline : unit -> unit
val my_prerr_string : string -> unit

val prerr_memory_usage : unit -> unit
(** [prerr_memory_usage ()] prints the current memory usage of the program to
    stderr, when the [Options.verbose] level is set to 1 or higher. *)
