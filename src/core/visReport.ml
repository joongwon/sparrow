(* Generate an offline report from the same snapshots used by inspect.ml. *)
open Printf

let display_text s =
  (* C string literals can contain arbitrary bytes, not just UTF-8/XML text. *)
  let b = Buffer.create (String.length s) in
  String.iter (fun c ->
    let code = Char.code c in
    if (code >= 32 && code < 127) || c = '\n' || c = '\t' then
      Buffer.add_char b c
    else Buffer.add_string b (sprintf "\\x%02x" code)) s;
  Buffer.contents b

let html s =
  let s = display_text s in
  let b = Buffer.create (String.length s) in
  String.iter (function
    | '&' -> Buffer.add_string b "&amp;" | '<' -> Buffer.add_string b "&lt;"
    | '>' -> Buffer.add_string b "&gt;" | '"' -> Buffer.add_string b "&quot;"
    | '\'' -> Buffer.add_string b "&#39;" | c -> Buffer.add_char b c) s;
  Buffer.contents b

let json j =
  (* JSON is embedded in HTML and executable data files. Escape HTML delimiters. *)
  let rec printable = function
    | `String s -> `String (display_text s)
    | `Assoc fields -> `Assoc (List.map (fun (k, v) -> display_text k, printable v) fields)
    | `List values -> `List (List.map printable values)
    | other -> other in
  let j = printable j in
  let s = Yojson.Safe.to_string j in
  let b = Buffer.create (String.length s) in
  String.iter (function '<' -> Buffer.add_string b "\\u003c"
    | '>' -> Buffer.add_string b "\\u003e" | '&' -> Buffer.add_string b "\\u0026"
    | c -> Buffer.add_char b c) s;
  Buffer.contents b

let write path f =
  let ch = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out ch) (fun () -> f ch)

let read path =
  let ch = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in ch)
    (fun () -> really_input_string ch (in_channel_length ch))

let unmarshal path =
  let ch = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in ch) (fun () -> Marshal.from_channel ch)

let run argv =
  let pid = Unix.create_process argv.(0) argv Unix.stdin Unix.stdout Unix.stderr in
  match snd (Unix.waitpid [] pid) with
  | Unix.WEXITED 0 -> ()
  | _ -> failwith ("Command failed: " ^ String.concat " " (Array.to_list argv))

let page ch title body =
  fprintf ch "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\"><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\"><title>%s · Sparrow</title><link rel=\"stylesheet\" href=\"style.css\"><script defer src=\"app.js\"></script></head><body>" (html title);
  body ch;
  fprintf ch "</body></html>\n"

let function_file pid = "fn-" ^ Digest.to_hex (Digest.string pid) ^ ".html"
let node_id node = "node-" ^ Digest.to_hex (Digest.string (InterCfg.Node.to_string node))

let save_state out text =
  let key = Digest.to_hex (Digest.string text) in
  let path = Filename.concat (Filename.concat out "states") (key ^ ".js") in
  if not (Sys.file_exists path) then
    write path (fun ch -> fprintf ch "window.sparrowState(%s,%s);\n"
      (json (`String key)) (json (`String text)));
  key

let load_states ~out ~analysis path =
  let refs = Hashtbl.create 16384 in
  let add node text = Hashtbl.replace refs node (save_state out text) in
  (match analysis with
  | "itv" ->
      let table : ItvDom.Table.t = unmarshal path in
      ItvDom.Table.iter (fun node mem -> add node (Format.asprintf "%a" ItvDom.Mem.pp mem)) table
  | "oct" ->
      (* Deserialize one memory at a time: retaining both Apron tables is costly. *)
      let nodes = unmarshal path in
      List.iter (fun ((node, _) as entry) ->
        let table = OctAnalysis.deserialize_table [entry] in
        let mem = OctAnalysis.Table.find node table in
        add node (Format.asprintf "%a" OctDom.Mem.pp mem)) nodes
  | _ -> invalid_arg "analysis must be itv or oct");
  refs

let direct_callee = function
  | IntraCfg.Cmd.Ccall (_, exp, _, _) ->
      (match CilHelper.remove_cast exp with
      | GoblintCil.Cil.Lval (GoblintCil.Cil.Var v, GoblintCil.Cil.NoOffset)
        when GoblintCil.Cil.isFunctionType v.vtype -> Some v.vname
      | _ -> None)
  | _ -> None

let callees icfg node cmd =
  let resolved = InterCfg.ProcSet.elements (InterCfg.get_callees node icfg) in
  List.sort_uniq String.compare
    (match direct_callee cmd with Some pid -> pid :: resolved | None -> resolved)

let graph_text s =
  (* Keep individual Graphviz label lines manageable without discarding text. *)
  let b = Buffer.create (String.length s) in
  let col = ref 0 in
  String.iter (fun c ->
    if c = '\n' || !col >= 90 then (Buffer.add_string b "<BR ALIGN=\"LEFT\"/>"; col := 0);
    if c <> '\n' then (Buffer.add_string b (html (String.make 1 c)); incr col)) s;
  if Buffer.length b = 0 then " " else Buffer.contents b

let link_cell known pid =
  if Hashtbl.mem known pid then
    sprintf "<TD HREF=\"%s\" TARGET=\"_self\" TOOLTIP=\"Open function %s\"><FONT COLOR=\"#075fba\"><U>%s</U></FONT></TD>"
      (function_file pid) (html pid) (html pid)
  else sprintf "<TD>%s (external / no CFG)</TD>" (html pid)

let command_label known cmd targets =
  match cmd with
  | IntraCfg.Cmd.Ccall (result, exp, args, _) ->
      let prefix = match result with None -> "call" | Some lv -> CilHelper.s_lv lv ^ " := call" in
      let target = match direct_callee cmd with
        | Some pid -> link_cell known pid
        | None -> "<TD>" ^ graph_text (CilHelper.s_exp exp) ^ "</TD>" in
      let resolved = match direct_callee cmd with Some _ -> [] | None -> targets in
      "<TR><TD><TABLE BORDER=\"0\" CELLBORDER=\"0\"><TR><TD>" ^ graph_text prefix ^
      "</TD>" ^ target ^ "</TR></TABLE></TD></TR><TR><TD ALIGN=\"LEFT\">" ^
      graph_text (CilHelper.s_exps args) ^ "</TD></TR>" ^
      (if resolved = [] then "" else
        "<TR><TD><TABLE BORDER=\"0\" CELLBORDER=\"0\"><TR><TD>Possible callees:</TD></TR>" ^
        String.concat "" (List.map (fun p -> "<TR>" ^ link_cell known p ^ "</TR>") resolved) ^
        "</TABLE></TD></TR>")
  | _ -> "<TR><TD ALIGN=\"LEFT\">" ^ graph_text (IntraCfg.Cmd.to_string cmd) ^ "</TD></TR>"

let inline_svg path =
  let svg = read path in
  let pos = Str.search_forward (Str.regexp_string "<svg") svg 0 in
  String.sub svg pos (String.length svg - pos)

let generate_function ~dot ~out ~analysis ~known ~input ~output icfg pid =
  let cfg = InterCfg.cfgof icfg pid in
  let nodes = List.sort InterCfg.Node.compare (InterCfg.nodes_of_pid icfg pid) in
  let stem = Filename.remove_extension (function_file pid) in
  let dot_path = Filename.concat out (stem ^ ".dot") in
  let svg_path = Filename.concat out (stem ^ ".svg") in
  write dot_path (fun ch ->
    fprintf ch "digraph cfg {\ngraph [bgcolor=\"transparent\",ranksep=0.5];\nnode [shape=box,style=\"rounded,filled\",fillcolor=\"white\",color=\"#aebfcd\",fontname=\"monospace\",fontsize=11];\nedge [color=\"#8195a6\",arrowsize=0.7];\n";
    (* Bound optimization work on large CFGs, retaining every vertex and edge.
       https://graphviz.org/docs/attrs/nslimit/ *)
    if List.length nodes > 1000 then
      fprintf ch "graph [nslimit=1,nslimit1=1,mclimit=0.2];\n";
    List.iter (fun node ->
      let cmd = InterCfg.cmdof icfg node in
      let targets = callees icfg node cmd in
      let color = if InterCfg.is_callnode node icfg then "#eaf4ff"
        else if InterCfg.is_inside_loop node icfg then "#f0f6e9" else "white" in
      fprintf ch "%S [id=%S,fillcolor=%S,label=<<TABLE BORDER=\"0\" CELLBORDER=\"0\" CELLPADDING=\"5\"><TR><TD ALIGN=\"LEFT\"><B>%s</B></TD></TR>%s</TABLE>>];\n"
        (node_id node) (node_id node) color (html (InterCfg.Node.to_string node))
        (command_label known cmd targets)) nodes;
    IntraCfg.fold_edges (fun src dst () ->
      fprintf ch "%S -> %S;\n" (node_id (InterCfg.Node.make pid src))
        (node_id (InterCfg.Node.make pid dst))) cfg ();
    fprintf ch "}\n");
  run [|dot; "-Tsvg"; dot_path; "-o"; svg_path|];
  let ref_json refs node = match Hashtbl.find_opt refs node with None -> `Null | Some key -> `String key in
  let metadata = `Assoc (List.map (fun node ->
    let cmd = InterCfg.cmdof icfg node in
    (node_id node, `Assoc ["name", `String (InterCfg.Node.to_string node);
      "command", `String (IntraCfg.Cmd.to_string cmd);
      "input", ref_json input node; "output", ref_json output node;
      "callees", `List (List.map (fun name -> `Assoc ["name", `String name;
        "href", if Hashtbl.mem known name then `String (function_file name) else `Null]) (callees icfg node cmd))])) nodes) in
  write (Filename.concat out (function_file pid)) (fun ch -> page ch pid (fun ch ->
    fprintf ch "<header><a href=\"index.html\">← Functions</a><h1>%s</h1><span class=\"badge\">%s</span><span>%d nodes</span></header>" (html pid) (html analysis) (List.length nodes);
    fprintf ch "<div class=\"toolbar\"><p>Click a node to inspect its state. Click a <a href=\"index.html\">blue function name</a> to open its CFG.</p><label for=\"node-picker\">Node</label><select id=\"node-picker\"><option value=\"\">Select a node…</option>";
    List.iter (fun node -> fprintf ch "<option value=\"%s\">%s</option>" (node_id node) (html (InterCfg.Node.to_string node))) nodes;
    fprintf ch "</select><button id=\"zoom-out\" aria-label=\"Zoom out\">−</button><button id=\"zoom-in\" aria-label=\"Zoom in\">+</button><button id=\"zoom-fit\">Fit width</button><a href=\"%s.dot\">DOT</a><a href=\"%s.svg\">SVG</a></div>" stem stem;
    fprintf ch "<main class=\"layout\"><section class=\"graph-view\" aria-label=\"Control flow graph\">%s</section>" (inline_svg svg_path);
    fprintf ch "<aside class=\"state-panel\" aria-label=\"Abstract state\"><h2 id=\"node-title\">Select a node</h2><pre id=\"node-command\" class=\"command\">Click a node or choose it from the list.</pre><nav id=\"callees\" aria-label=\"Called functions\"></nav><p class=\"muted\">Saved sparse states: input is before the command; output is after it. Missing entries are shown as not recorded, not as bottom.</p><label for=\"state-search\">Filter state lines</label><input id=\"state-search\" type=\"search\" placeholder=\"Variable, location, or constraint\"><div class=\"states\" aria-live=\"polite\"><h3>Input</h3><pre id=\"input-state\">No node selected.</pre><h3>Output</h3><pre id=\"output-state\">No node selected.</pre></div></aside></main><script id=\"node-data\" type=\"application/json\">%s</script>" (json metadata)))

let generate ~dir ~prefix ~analysis ~out ~dot =
  if not (List.mem analysis ["itv"; "oct"]) then invalid_arg "--analysis must be itv or oct";
  let base = Filename.concat dir (prefix ^ "." ^ analysis) in
  List.iter (fun suffix -> if not (Sys.file_exists (base ^ suffix)) then
    failwith ("Missing snapshot: " ^ base ^ suffix)) [".global"; ".input"; ".output"];
  (* Check Graphviz before loading potentially large snapshots. *)
  (try run [|dot; "-V"|] with Unix.Unix_error (Unix.ENOENT, _, _) ->
    failwith "Graphviz dot was not found. Install graphviz or pass --dot PATH.");
  if Sys.file_exists out then failwith ("Output already exists: " ^ out ^ ". Choose a new --output directory.");
  GoblintCil.Cil.initCIL ();
  eprintf "Loading %s.global\n%!" base;
  let global : Global.t = unmarshal (base ^ ".global") in
  let icfg = global.icfg in
  Unix.mkdir out 0o755;
  Unix.mkdir (Filename.concat out "states") 0o755;
  let load side =
    eprintf "Exporting %s states…\n%!" side;
    let refs = load_states ~out ~analysis (base ^ "." ^ side) in
    Gc.full_major (); refs in
  let input = load "input" in
  let output = load "output" in
  write (Filename.concat out "style.css") (fun ch -> output_string ch VisHtml.css);
  write (Filename.concat out "app.js") (fun ch -> output_string ch VisHtml.js);
  let pids = List.sort String.compare (InterCfg.pidsof icfg) in
  let known = Hashtbl.create (List.length pids) in
  List.iter (fun p -> Hashtbl.add known p ()) pids;
  List.iteri (fun i pid ->
    eprintf "[%d/%d] Rendering %s\n%!" (i + 1) (List.length pids) pid;
    generate_function ~dot ~out ~analysis ~known ~input ~output icfg pid) pids;
  write (Filename.concat out "index.html") (fun ch -> page ch "Functions" (fun ch ->
    fprintf ch "<header><h1>Sparrow · Function explorer</h1><span class=\"badge\">%s analysis</span></header><main class=\"index\"><h2>%s</h2><p>Browse function CFGs and inspect the saved abstract states at each node.</p><label for=\"function-search\">Find a function</label><input id=\"function-search\" type=\"search\" placeholder=\"Filter by function name\"><p id=\"function-count\" class=\"muted\">%d functions</p><table><thead><tr><th>Function</th><th>CFG nodes</th><th>Call nodes</th></tr></thead><tbody>"
      (html analysis) (html prefix) (List.length pids);
    List.iter (fun pid ->
      let nodes = InterCfg.nodes_of_pid icfg pid in
      fprintf ch "<tr data-function=\"%s\"><td><a href=\"%s\"><code>%s</code></a></td><td>%d</td><td>%d</td></tr>"
        (html pid) (function_file pid) (html pid) (List.length nodes)
        (List.length (List.filter (fun n -> InterCfg.is_callnode n icfg) nodes))) pids;
    fprintf ch "</tbody></table></main>"));
  printf "Open %s\n%!" (Filename.concat out "index.html")
