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
(* Pretty printer for each step *)
val make_istr : string -> string

val step : bool -> string -> 'a -> ('a -> 'b) -> 'b
(** [step s stg i fn] runs the function [fn] with input [i], while logging the
    start and completion of the task with timing information. *)

val stepf : bool -> string -> ('a -> 'b) -> 'a -> 'b
(** [stepf s stg fn i] is similar to [step], except the logging is conditional
    on the verbosity level set in [Options.verbose]. *)

val stepf_opt : bool -> bool -> string -> ('a -> 'a) -> 'a -> 'a
val stepf_cond : bool -> bool -> string -> ('a -> 'b) -> ('a -> 'b) -> 'a -> 'b
val stepf_switch : bool -> string -> (bool * ('a -> 'b)) list -> 'a -> 'b
val stepf_opt_unit : bool -> bool -> string -> ('a -> unit) -> 'a -> unit
