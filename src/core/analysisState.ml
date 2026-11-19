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
type t = {
  files : string list;
  global : Global.t;
  inputof : ItvAnalysis.Table.t;
  outputof : ItvAnalysis.Table.t;
  alarms : Report.query list;
  counts : Report.counts;
}

let magic = "SPARROW-ITV-STATE"
let format_version = 2

let header () =
  Printf.sprintf "%s %d %s" magic format_version Sys.ocaml_version

let save path state =
  let oc = open_out_bin path in
  Fun.protect
    ~finally:(fun () -> close_out_noerr oc)
    (fun () ->
      output_string oc (header ());
      output_char oc '\n';
      (* no [Closures]: a closure could not be read by another executable *)
      Marshal.to_channel oc state [])

let load path =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () ->
      let found =
        try input_line ic
        with End_of_file -> failwith (path ^ ": empty file")
      in
      if found <> header () then
        failwith
          (Printf.sprintf "%s: header %S, expected %S" path
             (if String.length found > 80 then String.sub found 0 80 ^ "..."
              else found)
             (header ()));
      (Marshal.from_channel ic : t))
