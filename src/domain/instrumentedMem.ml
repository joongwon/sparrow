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
(* A pure-read log: observation only, separate from the DEF/USE access
   record.  [read_keys] are the keys [observe_read], [mem] and [find_binding]
   saw while the log was on; a weak write's join base is not a read here (the
   access record files it as ALL, i.e. also as USE).  [read_whole_memory]
   names, in first-seen order, every operation that inspected a memory of
   this instance as a whole (fold, map, join, comparison, ...): such a read
   is not a finite set of keys.  A bottom test ([eq]/[le] with an empty
   side) is the one whole-memory question kept apart: [read_bottom_true]
   says whether one answered true. *)
type 'keys read_log = {
  read_keys : 'keys;
  read_whole_memory : string list;
  read_bottom_true : bool;
}

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

module Make (Mem : MapDom.CPO) = struct
  include Mem
  module Loc = A
  module Val = B
  module Access = Access.Make (Mem)

  let access = ref Access.Info.empty
  let access_mode = ref false

  let init_access : unit -> unit =
   fun () ->
    access_mode := true;
    access := Access.Info.empty;
    ()

  let return_access : unit -> Access.info =
   fun () ->
    access_mode := false;
    !access

  let observe_write ~weak k =
    if !access_mode then
      access :=
        Access.Info.add
          (if weak then Access.Info.all else Access.Info.def)
          k !access

  let add k v m =
    observe_write ~weak:false k;
    add k v m

  let weak_add k v m =
    observe_write ~weak:true k;
    weak_add k v m

  let observe_read k m =
    if !access_mode && not (eq m bot) then
      access := Access.Info.add Access.Info.use k !access

  let find_unobserved = find

  let find : A.t -> t -> B.t =
   fun k m ->
    observe_read k m;
    find k m

  (* The pure-read log (see [read_log]).  The access record above keeps its
     own rules; the [eq] in [observe_read]'s guard is not logged. *)
  let read_log_on = ref false
  let read_log_keys = ref PowA.empty
  let read_log_whole = ref []
  let read_log_bottom_true = ref false

  let start_read_log () =
    read_log_on := true;
    read_log_keys := PowA.empty;
    read_log_whole := [];
    read_log_bottom_true := false

  let stop_read_log () =
    read_log_on := false;
    {
      read_keys = !read_log_keys;
      read_whole_memory = List.rev !read_log_whole;
      read_bottom_true = !read_log_bottom_true;
    }

  let log_whole name =
    if !read_log_on && not (List.mem name !read_log_whole) then
      read_log_whole := name :: !read_log_whole

  let observe_read k m =
    if !read_log_on then read_log_keys := PowA.add k !read_log_keys;
    observe_read k m

  let find : A.t -> t -> B.t =
   fun k m ->
    if !read_log_on then read_log_keys := PowA.add k !read_log_keys;
    find k m

  let mem k m =
    if !read_log_on then read_log_keys := PowA.add k !read_log_keys;
    mem k m

  let find_binding k m =
    if !read_log_on then read_log_keys := PowA.add k !read_log_keys;
    find_binding k m

  let bottom_test name compare a b =
    let answer = compare a b in
    if !read_log_on then
      if is_empty a || is_empty b then (
        if answer then read_log_bottom_true := true)
      else log_whole name;
    answer

  let eq a b = bottom_test "eq" eq a b
  let le a b = bottom_test "le" le a b

  let join a b =
    log_whole "join";
    join a b

  let meet a b =
    log_whole "meet";
    meet a b

  let widen a b =
    log_whole "widen";
    widen a b

  let narrow a b =
    log_whole "narrow";
    narrow a b

  let is_empty m =
    log_whole "is_empty";
    is_empty m

  let map f m =
    log_whole "map";
    map f m

  let mapi f m =
    log_whole "mapi";
    mapi f m

  let fold f m a =
    log_whole "fold";
    fold f m a

  let foldi f m a =
    log_whole "foldi";
    foldi f m a

  let iter f m =
    log_whole "iter";
    iter f m

  let filter f m =
    log_whole "filter";
    filter f m

  let cardinal m =
    log_whole "cardinal";
    cardinal m

  let choose m =
    log_whole "choose";
    choose m

  let to_string m =
    log_whole "to_string";
    to_string m

  let for_all f m =
    log_whole "for_all";
    for_all f m

  let exists f m =
    log_whole "exists";
    exists f m

  let keys m =
    log_whole "keys";
    keys m

  let unstables a b f locs =
    log_whole "unstables";
    unstables a b f locs

  let join_pairs pairs m =
    log_whole "join_pairs";
    join_pairs pairs m

  let widen_pairs pairs m =
    log_whole "widen_pairs";
    widen_pairs pairs m

  let meet_big_small a b =
    log_whole "meet_big_small";
    meet_big_small a b
end
