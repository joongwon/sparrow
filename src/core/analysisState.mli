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
(** The final state of the interval analysis, marshaled to one file
    ([-marshal_state]) and read back by [sparrow-server].

    The file is a text header line followed by one marshaled value, so the
    CIL objects the parts share (types, varinfos) are stored once.  The
    header names the format version and the OCaml version that wrote it;
    {!load} refuses a file whose header differs.  Marshaled data is not
    type-checked: a reader built from different sources than the writer
    must bump {!format_version}. *)

type t = {
  files : string list;  (** the source files given to the analyzer *)
  global : Global.t;  (** program, CFGs, call graph, pre-analysis memory *)
  inputof : ItvAnalysis.Table.t;  (** memory before each node *)
  outputof : ItvAnalysis.Table.t;  (** memory after each node *)
  alarms : Report.query list;  (** every query, with its status *)
  counts : Report.counts;  (** the alarm counts of the analysis' report *)
}

val format_version : int

val save : string -> t -> unit
(** [save path state] writes [state] to [path]. *)

val load : string -> t
(** [load path] reads a state written by {!save}.
    @raise Failure if the header is missing or does not match. *)
