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
(** Alarm report of interval analysis *)
type target = BO | ND | DZ

type status = Proven | UnProven | BotAlarm

type query = {
  node : InterCfg.node;
  exp : AlarmExp.t;
  loc : Sparrow_cil.location;
  allocsite : BasicDom.Loc.t option;  (** the array's cell *)
  src : (InterCfg.node * Sparrow_cil.location) option;
  status : status;
  desc : string;
}

type part_unit = Sparrow_cil.location

val sort_partition :
  (part_unit * query list) list -> (part_unit * query list) list

val string_of_alarminfo : Itv.t -> Itv.t -> string
val string_of_query : query -> string
val partition : query list -> (part_unit, query list) BatMap.t
val get : query list -> status -> query list

(** The alarm counts {!print} reports: queries, alarm points (source
    locations), and points proven, unproven (after the [-filter_*] options)
    and involving bottom. *)
type counts = {
  queries : int;
  points : int;
  proven_points : int;
  unproven_points : int;
  bot_points : int;
}

val counts : Global.t -> query list -> counts
val print : Global.t -> query list -> unit
