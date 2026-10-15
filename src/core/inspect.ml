type snapshot = {
  global : Global.t;
  input_table : ItvDom.Table.t;
  output_table : ItvDom.Table.t;
}

let state = ref None
let init_cil = lazy (GoblintCil.Cil.initCIL ())

let read path =
  try
    let ch = open_in_bin path in
    Fun.protect ~finally:(fun () -> close_in_noerr ch) (fun () ->
        Marshal.from_channel ch)
  with exn ->
    failwith (Printf.sprintf "Cannot load %s: %s" path (Printexc.to_string exn))

let load ?(prefix = "merged") dir =
  Lazy.force init_cil;
  let base = Filename.concat dir (prefix ^ ".itv") in
  let global : Global.t = read (base ^ ".global") in
  let input_table : ItvDom.Table.t = read (base ^ ".input") in
  let output_table : ItvDom.Table.t = read (base ^ ".output") in
  state := Some { global; input_table; output_table }

let current () =
  match !state with
  | Some snapshot -> snapshot
  | None -> failwith "No snapshot loaded. Use load ~prefix:\"merged\" DIR."

let functions () =
  InterCfg.pidsof (current ()).global.icfg |> List.sort String.compare

let nodes ?func () =
  let icfg = (current ()).global.icfg in
  (match func with
  | None -> InterCfg.nodesof icfg
  | Some pid ->
      if not (List.mem pid (InterCfg.pidsof icfg)) then
        invalid_arg ("Unknown function: " ^ pid);
      InterCfg.nodes_of_pid icfg pid)
  |> List.sort InterCfg.Node.compare

let node name =
  match List.find_opt (fun n -> InterCfg.Node.to_string n = name) (nodes ()) with
  | Some n -> n
  | None -> invalid_arg ("Unknown node: " ^ name)

let memory side table n =
  if not (ItvDom.Table.mem n table) then
    failwith
      (Printf.sprintf "No recorded %s state for node %s" side
         (InterCfg.Node.to_string n));
  ItvDom.Table.find n table

let input n = memory "input" (current ()).input_table n
let output n = memory "output" (current ()).output_table n
