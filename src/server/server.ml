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
(* sparrow-server: serves the final interval-analysis state written by
   [sparrow -marshal_state FILE] for inspection in a browser (/) or over a
   JSON API (/api/...).  The state is read once and never changes. *)

module H = Tiny_httpd
module J = Yojson.Safe
open BasicDom
open ItvDom

let state_path = ref ""
let addr = ref "127.0.0.1"
let port = ref 8080
let dot_path = ref "dot"

(* ------------------------------------------------------------------ *)
(* The loaded state and the indexes built from it                      *)

type loaded = {
  state : AnalysisState.t;
  nodes : (string, InterCfg.Node.t) Hashtbl.t;  (* by Node.to_string *)
  procs : (string * int) list;  (* name, #nodes; sorted by name *)
  node_status : (string, Report.status) Hashtbl.t;
      (* the worst status of a node's alarms: bot, then unproven, then proven *)
}

let load path =
  let t0 = Unix.gettimeofday () in
  let state = AnalysisState.load path in
  let icfg = state.AnalysisState.global.Global.icfg in
  let nodes = Hashtbl.create 65536 in
  List.iter
    (fun n -> Hashtbl.replace nodes (InterCfg.Node.to_string n) n)
    (InterCfg.nodesof icfg);
  let procs =
    InterCfg.pidsof icfg
    |> List.map (fun pid ->
        (pid, List.length (IntraCfg.nodesof (InterCfg.cfgof icfg pid))))
    |> List.sort compare
  in
  let rank = function
    | Report.BotAlarm -> 2
    | Report.UnProven -> 1
    | Report.Proven -> 0
  in
  let node_status = Hashtbl.create 4096 in
  List.iter
    (fun q ->
      let key = InterCfg.Node.to_string q.Report.node in
      match Hashtbl.find_opt node_status key with
      | Some s when rank s >= rank q.Report.status -> ()
      | _ -> Hashtbl.replace node_status key q.Report.status)
    state.AnalysisState.alarms;
  Printf.eprintf "loaded %s in %.2fs: %d procedures, %d nodes, %d alarms\n%!"
    path
    (Unix.gettimeofday () -. t0)
    (List.length procs) (Hashtbl.length nodes)
    (List.length state.AnalysisState.alarms);
  { state; nodes; procs; node_status }

(* Location name -> the nodes whose output (definitions) and input (uses)
   hold it.  Built on first use: it walks every memory of both tables. *)
type loc_index = {
  defs : (string, InterCfg.Node.t list) Hashtbl.t;
  uses : (string, InterCfg.Node.t list) Hashtbl.t;
  names : string array;  (* sorted *)
}

let index_lock = Mutex.create ()
let index_cache : loc_index option ref = ref None

let loc_index l =
  Mutex.lock index_lock;
  Fun.protect
    ~finally:(fun () -> Mutex.unlock index_lock)
    (fun () ->
      match !index_cache with
      | Some index -> index
      | None ->
          let t0 = Unix.gettimeofday () in
          let defs = Hashtbl.create 65536 and uses = Hashtbl.create 65536 in
          let add table node loc _ =
            let key = Loc.to_string loc in
            Hashtbl.replace table key
              (node :: Option.value (Hashtbl.find_opt table key) ~default:[])
          in
          let fill table memories =
            ItvAnalysis.Table.iter
              (fun node mem -> Mem.iter (add table node) mem)
              memories
          in
          fill defs l.state.AnalysisState.outputof;
          fill uses l.state.AnalysisState.inputof;
          let names = Hashtbl.create 65536 in
          Hashtbl.iter (fun k _ -> Hashtbl.replace names k ()) defs;
          Hashtbl.iter (fun k _ -> Hashtbl.replace names k ()) uses;
          let names = Hashtbl.fold (fun k () acc -> k :: acc) names [] in
          let names = Array.of_list (List.sort String.compare names) in
          Printf.eprintf "location index: %d locations in %.2fs\n%!"
            (Array.length names)
            (Unix.gettimeofday () -. t0);
          let index = { defs; uses; names } in
          index_cache := Some index;
          index)

(* ------------------------------------------------------------------ *)
(* JSON of the analysis objects                                        *)

let contains ~sub s =
  sub = ""
  ||
  let n = String.length sub and m = String.length s in
  let sub = String.lowercase_ascii sub and s = String.lowercase_ascii s in
  let rec go i = i + n <= m && (String.sub s i n = sub || go (i + 1)) in
  go 0

let location_json (loc : Sparrow_cil.location) =
  `Assoc
    [
      ("file", `String loc.Sparrow_cil.file);
      ("line", `Int loc.Sparrow_cil.line);
      ("text", `String (CilHelper.s_location loc));
    ]

let cell_json loc (v, info) =
  let parts =
    List.filter_map Fun.id
      [
        (let i = Val.itv_of_val v in
         if Itv.is_bot i then None else Some ("itv", `String (Itv.to_string i)));
        (let p = Val.pow_loc_of_val v in
         if PowLoc.is_empty p then None
         else
           Some
             ( "points_to",
               `List
                 (PowLoc.fold (fun l acc -> `String (Loc.to_string l) :: acc) p []
                 |> List.rev) ));
        (let a = Val.array_of_val v in
         if ArrayBlk.is_empty a then None
         else Some ("array", `String (ArrayBlk.to_string a)));
        (let p = Val.pow_proc_of_val v in
         if PowProc.is_empty p then None
         else Some ("procs", `String (PowProc.to_string p)));
        (if CellInfo.eq info CellInfo.bot then None
         else Some ("info", `String (CellInfo.to_string info)));
      ]
  in
  `Assoc
    ([ ("loc", `String (Loc.to_string loc)); ("value", `String (Val.to_string v)) ]
    @ parts)

(* the entries of [mem] whose location matches [q], by location name *)
let memory_json ~q ~offset ~limit mem =
  let entries =
    Mem.foldi
      (fun loc cell acc ->
        let name = Loc.to_string loc in
        if contains ~sub:q name then (name, loc, cell) :: acc else acc)
      mem []
    |> List.sort (fun (a, _, _) (b, _, _) -> String.compare a b)
  in
  let total = List.length entries in
  let page =
    entries
    |> List.filteri (fun i _ -> i >= offset && i < offset + limit)
    |> List.map (fun (_, loc, cell) -> cell_json loc cell)
  in
  `Assoc
    [
      ("size", `Int (Mem.cardinal mem));
      ("matching", `Int total);
      ("offset", `Int offset);
      ("entries", `List page);
    ]

(* How a command is shown.  An assume shows the condition the interval
   analysis prunes with ([CilHelper.make_cond_simple], as in [ItvSem.prune]),
   with the condition as written in [original] when they differ; a condition
   it cannot simplify does not prune: it is shown as written and [ignored]. *)
type shown_cmd = { text : string; ignored : bool; original : string option }

let shown_cmd cmd =
  let written = IntraCfg.Cmd.to_string cmd in
  match cmd with
  | IntraCfg.Cmd.Cassume (e, _) -> (
      match CilHelper.make_cond_simple e with
      | Some simple ->
          let text = "assume(" ^ CilHelper.s_exp simple ^ ")" in
          {
            text;
            ignored = false;
            original = (if text = written then None else Some written);
          }
      | None -> { text = written; ignored = true; original = None })
  | _ -> { text = written; ignored = false; original = None }

let ignored_mark = " (ignored)"

let cmd_json cmd =
  let shown = shown_cmd cmd in
  `Assoc
    [
      ("text", `String (shown.text ^ if shown.ignored then ignored_mark else ""));
      ("ignored", `Bool shown.ignored);
      ( "original",
        match shown.original with Some o -> `String o | None -> `Null );
      ("location", location_json (IntraCfg.Cmd.location_of cmd));
    ]

let node_ref_json l node =
  let icfg = l.state.AnalysisState.global.Global.icfg in
  `Assoc
    [
      ("id", `String (InterCfg.Node.to_string node));
      ("proc", `String (InterCfg.Node.get_pid node));
      ("cmd", cmd_json (InterCfg.cmdof icfg node));
    ]

let status_string = function
  | Report.Proven -> "proven"
  | Report.UnProven -> "unproven"
  | Report.BotAlarm -> "bot"

let alarm_json index (q : Report.query) =
  `Assoc
    [
      ("index", `Int index);
      ("status", `String (status_string q.Report.status));
      ("node", `String (InterCfg.Node.to_string q.Report.node));
      ("proc", `String (InterCfg.Node.get_pid q.Report.node));
      ("location", location_json q.Report.loc);
      ("exp", `String (AlarmExp.to_string q.Report.exp));
      ( "allocsite",
        match q.Report.allocsite with
        | Some a -> `String (Loc.to_string a)
        | None -> `Null );
      ("desc", `String q.Report.desc);
    ]

(* ------------------------------------------------------------------ *)
(* A procedure's CFG as SVG, laid out by Graphviz                      *)

(* The SVG [g] element of a node has the node's id as its [id] and the
   classes [entry], [exit], [call], [ignored] (an assume whose condition is
   not pruned with, see [shown_cmd]) and [alarm-<status>] that apply. *)

let dot_string s =
  let b = Buffer.create (String.length s + 8) in
  Buffer.add_char b '"';
  String.iter
    (function
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | '\n' | '\r' | '\t' -> Buffer.add_char b ' '
      | c -> Buffer.add_char b c)
    s;
  Buffer.add_char b '"';
  Buffer.contents b

let max_label = 72

(* Above this many nodes, Graphviz's network simplex and crossing
   minimization are cut short: luaV_execute (3511 nodes) takes 1.3s instead
   of 33s, with a layout as readable. *)
let large_cfg = 500

let shorten s =
  if String.length s <= max_label then s
  else String.sub s 0 (max_label - 3) ^ "..."

let cfg_dot l name =
  let icfg = l.state.AnalysisState.global.Global.icfg in
  let cfg = InterCfg.cfgof icfg name in
  let id n = InterCfg.Node.to_string (InterCfg.Node.make name n) in
  let nodes = IntraCfg.nodesof cfg in
  let b = Buffer.create 65536 in
  Printf.bprintf b
    "digraph cfg {\n\
     graph [rankdir=TB, nodesep=0.25, ranksep=0.3, bgcolor=transparent%s];\n\
     node [shape=box, style=rounded, fontname=monospace, fontsize=10, \
     height=0.25, margin=\"0.08,0.03\"];\n\
     edge [arrowsize=0.6];\n"
    (if List.length nodes > large_cfg then
       ", nslimit=0.5, nslimit1=0.5, mclimit=0.1"
     else "");
  List.iter
    (fun n ->
      let node = InterCfg.Node.make name n in
      let shown = shown_cmd (IntraCfg.find_cmd n cfg) in
      let classes =
        List.filter_map Fun.id
          [
            (if IntraCfg.Node.equal n IntraCfg.Node.entry then Some "entry"
             else None);
            (if IntraCfg.Node.equal n IntraCfg.Node.exit then Some "exit"
             else None);
            (if InterCfg.is_callnode node icfg then Some "call" else None);
            (if shown.ignored then Some "ignored" else None);
            Option.map
              (fun s -> "alarm-" ^ status_string s)
              (Hashtbl.find_opt l.node_status (id n));
          ]
      in
      let label =
        match IntraCfg.find_cmd n cfg with
        | IntraCfg.Cmd.Cskip -> IntraCfg.Node.to_string n
        | _ ->
            IntraCfg.Node.to_string n ^ ": " ^ shorten shown.text
            ^ if shown.ignored then ignored_mark else ""
      in
      Printf.bprintf b "%s [id=%s, class=%s, label=%s];\n" (dot_string (id n))
        (dot_string (id n))
        (dot_string (String.concat " " classes))
        (dot_string label);
      List.iter
        (fun s -> Printf.bprintf b "%s -> %s;\n" (dot_string (id n)) (dot_string (id s)))
        (IntraCfg.succ n cfg))
    nodes;
  Buffer.add_string b "}\n";
  Buffer.contents b

let run_dot source =
  let tmp = Filename.temp_file "sparrow-cfg" ".dot" in
  Fun.protect
    ~finally:(fun () -> try Sys.remove tmp with Sys_error _ -> ())
    (fun () ->
      Out_channel.with_open_bin tmp (fun oc -> output_string oc source);
      let ic = Unix.open_process_args_in !dot_path [| !dot_path; "-Tsvg"; tmp |] in
      let svg = In_channel.input_all ic in
      match Unix.close_process_in ic with
      | Unix.WEXITED 0 -> svg
      | Unix.WEXITED code ->
          failwith
            (Printf.sprintf
               "%s exited with %d (is Graphviz installed? see -dot)" !dot_path
               code)
      | Unix.WSIGNALED n | Unix.WSTOPPED n ->
          failwith (Printf.sprintf "%s killed by signal %d" !dot_path n))

let cfg_lock = Mutex.create ()
let cfg_cache : (string, string) Hashtbl.t = Hashtbl.create 64

(* Layouts are cached; two requests for one procedure may both lay it out. *)
let cfg_svg l name =
  let cached =
    Mutex.lock cfg_lock;
    let r = Hashtbl.find_opt cfg_cache name in
    Mutex.unlock cfg_lock;
    r
  in
  match cached with
  | Some svg -> svg
  | None ->
      let t0 = Unix.gettimeofday () in
      let svg = run_dot (cfg_dot l name) in
      Printf.eprintf "cfg %s laid out in %.2fs\n%!" name
        (Unix.gettimeofday () -. t0);
      Mutex.lock cfg_lock;
      Hashtbl.replace cfg_cache name svg;
      Mutex.unlock cfg_lock;
      svg

(* ------------------------------------------------------------------ *)
(* Handlers                                                            *)

exception Not_found_ of string

let param req name = List.assoc_opt name (H.Request.query req)
let param_or req name default = Option.value (param req name) ~default

let int_param req name default =
  match param req name with
  | None -> default
  | Some s -> (
      match int_of_string_opt s with
      | Some n when n >= 0 -> n
      | _ -> raise (H.Response.Bad_req (400, name ^ ": not a natural number")))

let required req name =
  match param req name with
  | Some v -> v
  | None -> raise (H.Response.Bad_req (400, "missing parameter " ^ name))

let json_response json =
  H.Response.make_string
    ~headers:[ ("Content-Type", "application/json; charset=utf-8") ]
    (Ok (J.to_string json))

let handle_with respond f req =
  try respond (f req) with
  | Not_found_ what -> H.Response.make_string (Error (404, what ^ " not found"))
  | H.Response.Bad_req (code, msg) -> H.Response.make_string (Error (code, msg))
  | e ->
      H.Response.make_string
        (Error (500, "internal error: " ^ Printexc.to_string e))

let handle f = handle_with json_response f

let svg_response svg =
  H.Response.make_string
    ~headers:[ ("Content-Type", "image/svg+xml; charset=utf-8") ]
    (Ok svg)

let find_node l id =
  match Hashtbl.find_opt l.nodes id with
  | Some n -> n
  | None -> raise (Not_found_ ("node " ^ id))

let summary l _req =
  let s = l.state in
  let count status =
    List.length
      (List.filter (fun q -> q.Report.status = status) s.AnalysisState.alarms)
  in
  `Assoc
    [
      ("state_file", `String !state_path);
      ("format_version", `Int AnalysisState.format_version);
      ("files", `List (List.map (fun f -> `String f) s.AnalysisState.files));
      ("procedures", `Int (List.length l.procs));
      ("nodes", `Int (Hashtbl.length l.nodes));
      ( "nodes_with_input",
        `Int (ItvAnalysis.Table.cardinal s.AnalysisState.inputof) );
      ( "premem_locations",
        `Int (Mem.cardinal s.AnalysisState.global.Global.mem) );
      ( "alarms",
        let c = s.AnalysisState.counts in
        `Assoc
          [
            ("queries", `Int c.Report.queries);
            ("proven_queries", `Int (count Report.Proven));
            ("unproven_queries", `Int (count Report.UnProven));
            ("bot_queries", `Int (count Report.BotAlarm));
            ("points", `Int c.Report.points);
            ("proven_points", `Int c.Report.proven_points);
            ("unproven_points", `Int c.Report.unproven_points);
            ("bot_points", `Int c.Report.bot_points);
          ] );
    ]

let procs l req =
  let q = param_or req "q" "" in
  `List
    (l.procs
    |> List.filter (fun (name, _) -> contains ~sub:q name)
    |> List.map (fun (name, n) ->
        `Assoc [ ("name", `String name); ("nodes", `Int n) ]))

(* A procedure's nodes from the entry, depth first with successors in id
   order, then whatever that walk does not reach. *)
let proc l req =
  let name = required req "name" in
  let icfg = l.state.AnalysisState.global.Global.icfg in
  if not (InterCfg.mem_cfg name icfg) then raise (Not_found_ ("procedure " ^ name));
  let cfg = InterCfg.cfgof icfg name in
  let by_id a b = compare (IntraCfg.Node.id a) (IntraCfg.Node.id b) in
  let succs n = List.sort by_id (IntraCfg.succ n cfg) in
  let seen = Hashtbl.create 256 in
  let rec visit order = function
    | [] -> order
    | n :: rest when Hashtbl.mem seen n -> visit order rest
    | n :: rest ->
        Hashtbl.add seen n ();
        visit (n :: order) (succs n @ rest)
  in
  let order = List.rev (visit [] [ IntraCfg.entryof cfg ]) in
  let rest =
    IntraCfg.nodesof cfg
    |> List.filter (fun n -> not (Hashtbl.mem seen n))
    |> List.sort by_id
  in
  let inputof = l.state.AnalysisState.inputof
  and outputof = l.state.AnalysisState.outputof in
  let node_json n =
    let node = InterCfg.Node.make name n in
    let size table =
      if ItvAnalysis.Table.mem node table then
        `Int (Mem.cardinal (ItvAnalysis.Table.find node table))
      else `Null
    in
    let ids ns =
      `List (List.map (fun s -> `String (InterCfg.Node.to_string (InterCfg.Node.make name s))) ns)
    in
    `Assoc
      [
        ("id", `String (InterCfg.Node.to_string node));
        ("cmd", cmd_json (IntraCfg.find_cmd n cfg));
        ("succ", ids (succs n));
        ("pred", ids (List.sort by_id (IntraCfg.pred n cfg)));
        ( "callees",
          if InterCfg.is_callnode node icfg then
            `List
              (InterCfg.ProcSet.elements (InterCfg.get_callees node icfg)
              |> List.map (fun p -> `String p))
          else `Null );
        ("input_size", size inputof);
        ("output_size", size outputof);
      ]
  in
  `Assoc
    [
      ("name", `String name);
      ("undefined", `Bool (Global.is_undef name l.state.AnalysisState.global));
      ("nodes", `List (List.map node_json (order @ rest)));
    ]

let node l req =
  let node = find_node l (required req "id") in
  let q = param_or req "q" "" in
  let offset = int_param req "offset" 0 and limit = int_param req "limit" 500 in
  let memory table =
    if ItvAnalysis.Table.mem node table then
      memory_json ~q ~offset ~limit (ItvAnalysis.Table.find node table)
    else `Null
  in
  let alarms =
    List.mapi (fun i a -> (i, a)) l.state.AnalysisState.alarms
    |> List.filter (fun (_, a) -> InterCfg.Node.equal a.Report.node node)
    |> List.map (fun (i, a) -> alarm_json i a)
  in
  match node_ref_json l node with
  | `Assoc fields ->
      `Assoc
        (fields
        @ [
            ("input", memory l.state.AnalysisState.inputof);
            ("output", memory l.state.AnalysisState.outputof);
            ("alarms", `List alarms);
          ])
  | j -> j

let locs l req =
  let q = param_or req "q" "" in
  let limit = int_param req "limit" 200 in
  let index = loc_index l in
  let count table name =
    List.length (Option.value (Hashtbl.find_opt table name) ~default:[])
  in
  let matches = ref [] and n = ref 0 in
  Array.iter
    (fun name ->
      if !n < limit && contains ~sub:q name then begin
        incr n;
        matches :=
          `Assoc
            [
              ("loc", `String name);
              ("defs", `Int (count index.defs name));
              ("uses", `Int (count index.uses name));
            ]
          :: !matches
      end)
    index.names;
  `List (List.rev !matches)

(* where a location is defined (node outputs) and used (node inputs) *)
let loc l req =
  let name = required req "name" in
  let limit = int_param req "limit" 500 in
  let index = loc_index l in
  let entries table memories =
    let nodes =
      Option.value (Hashtbl.find_opt table name) ~default:[]
      |> List.sort InterCfg.Node.compare
    in
    let total = List.length nodes in
    let page = List.filteri (fun i _ -> i < limit) nodes in
    `Assoc
      [
        ("count", `Int total);
        ( "nodes",
          `List
            (List.map
               (fun node ->
                 let mem = ItvAnalysis.Table.find node memories in
                 let cell =
                   Mem.foldi
                     (fun loc cell found ->
                       match found with
                       | None when Loc.to_string loc = name -> Some (loc, cell)
                       | _ -> found)
                     mem None
                 in
                 match (node_ref_json l node, cell) with
                 | `Assoc fields, Some (loc, cell) ->
                     `Assoc (fields @ [ ("cell", cell_json loc cell) ])
                 | j, _ -> j)
               page) );
      ]
  in
  if not (Hashtbl.mem index.defs name || Hashtbl.mem index.uses name) then
    raise (Not_found_ ("location " ^ name));
  `Assoc
    [
      ("loc", `String name);
      ("defs", entries index.defs l.state.AnalysisState.outputof);
      ("uses", entries index.uses l.state.AnalysisState.inputof);
    ]

(* [format=dot] gives the Graphviz source instead of the layout *)
let cfg l req =
  let name = required req "name" in
  if not (InterCfg.mem_cfg name l.state.AnalysisState.global.Global.icfg) then
    raise (Not_found_ ("procedure " ^ name));
  match param_or req "format" "svg" with
  | "svg" -> svg_response (cfg_svg l name)
  | "dot" ->
      H.Response.make_string
        ~headers:[ ("Content-Type", "text/vnd.graphviz; charset=utf-8") ]
        (Ok (cfg_dot l name))
  | f -> raise (H.Response.Bad_req (400, "format: svg or dot, not " ^ f))

let premem l req =
  let q = param_or req "q" "" in
  let offset = int_param req "offset" 0 and limit = int_param req "limit" 500 in
  memory_json ~q ~offset ~limit l.state.AnalysisState.global.Global.mem

let alarms l req =
  let status = param_or req "status" "unproven" in
  let q = param_or req "q" "" in
  let offset = int_param req "offset" 0 and limit = int_param req "limit" 200 in
  let selected =
    List.mapi (fun i a -> (i, a)) l.state.AnalysisState.alarms
    |> List.filter (fun (_, a) ->
        (status = "all" || status_string a.Report.status = status)
        && (q = ""
           || contains ~sub:q (CilHelper.s_location a.Report.loc)
           || contains ~sub:q (InterCfg.Node.get_pid a.Report.node)
           || contains ~sub:q (AlarmExp.to_string a.Report.exp)))
  in
  `Assoc
    [
      ("matching", `Int (List.length selected));
      ("offset", `Int offset);
      ( "alarms",
        `List
          (selected
          |> List.filteri (fun i _ -> i >= offset && i < offset + limit)
          |> List.map (fun (i, a) -> alarm_json i a)) );
    ]

(* ------------------------------------------------------------------ *)

let usage =
  "Usage: sparrow-server [-addr ADDR] [-port PORT] STATE\n\
   Serve STATE, written by `sparrow -marshal_state STATE ...`, at \
   http://ADDR:PORT/."

let () =
  Arg.parse
    [
      ("-addr", Arg.Set_string addr, "ADDR Address to listen on (default: 127.0.0.1)");
      ("-port", Arg.Set_int port, "PORT Port to listen on (default: 8080)");
      ( "-dot",
        Arg.Set_string dot_path,
        "PATH Graphviz dot, to lay out CFGs (default: dot, from PATH)" );
    ]
    (fun f ->
      if !state_path = "" then state_path := f
      else raise (Arg.Bad "only one state file"))
    usage;
  if !state_path = "" then (
    prerr_endline usage;
    exit 2);
  let l =
    try load !state_path
    with Failure msg | Sys_error msg ->
      prerr_endline ("sparrow-server: " ^ msg);
      exit 1
  in
  let server = H.create ~addr:!addr ~port:!port () in
  let get route f =
    H.add_route_handler ~meth:`GET server
      H.Route.(exact "api" @/ exact route @/ return)
      (handle (f l))
  in
  get "summary" summary;
  get "procs" procs;
  get "proc" proc;
  get "node" node;
  get "locs" locs;
  get "loc" loc;
  get "premem" premem;
  get "alarms" alarms;
  H.add_route_handler ~meth:`GET server
    H.Route.(exact "api" @/ exact "cfg" @/ return)
    (handle_with Fun.id (cfg l));
  H.add_route_handler ~meth:`GET server H.Route.return (fun _ ->
      H.Response.make_string
        ~headers:[ ("Content-Type", "text/html; charset=utf-8") ]
        (Ok ServerPage.html));
  match
    H.run server ~after_init:(fun () ->
        Printf.eprintf "serving on http://%s:%d/\n%!" (H.addr server)
          (H.port server))
  with
  | Ok () -> ()
  | Error e ->
      prerr_endline ("sparrow-server: " ^ Printexc.to_string e);
      exit 1
