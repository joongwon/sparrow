open GoblintCil
open BasicDom
open ItvDom

let check b message = if not b then failwith message
let interval n = Itv.of_int n

let check_string mem value size =
  let array = Val.array_of_val value in
  check (not (ArrayBlk.is_empty array)) "String has no pointer target";
  check (Itv.eq (ArrayBlk.sizeof array) (interval size)) "Wrong string size";
  check
    (Itv.eq (ArrayBlk.nullof array) (interval (size - 1)))
    "Wrong terminator position";
  let contents = Mem.lookup (ArrayBlk.pow_loc_of_array array) mem in
  check (not (Val.eq contents Val.bot)) "String contents are missing"

let run_fixture path optimize =
  Options.optil := optimize;
  let global = Frontc.parse path () |> Frontend.makeCFGinfo |> Global.init in
  let rec walk pid node ((mem, global) as state) =
    let cmd = InterCfg.cmdof global.Global.icfg node in
    (match cmd with
    | IntraCfg.Cmd.Ccall (_, Cil.Lval (Cil.Var f, Cil.NoOffset), [ arg ], _)
      when f.Cil.vname = "external_sink" || f.Cil.vname = "defined_sink" ->
        check (f.Cil.vstorage = Cil.Extern) "Fixture must exercise extern";
        check_string mem (ItvSem.eval pid arg mem)
          (if f.Cil.vname = "external_sink" then 9 else 17)
    | _ -> ());
    let state = ItvSem.run AbsSem.Strong ItvSem.Spec.empty node state in
    let mem, global = state in
    (match cmd with
    | IntraCfg.Cmd.Ccall (_, Cil.Lval (Cil.Var f, Cil.NoOffset), _, _)
      when f.Cil.vname = "defined_sink" ->
        let formal = List.hd (InterCfg.argsof global.icfg "defined_sink") in
        check_string mem
          (Mem.find (Loc.of_lvar "defined_sink" formal.vname formal.vtype) mem)
          17
    | _ -> ());
    let cfg = InterCfg.cfgof global.icfg pid in
    match IntraCfg.succ (InterCfg.Node.get_cfgnode node) cfg with
    | [] -> state
    | [ next ] -> walk pid (InterCfg.Node.make pid next) state
    | nexts ->
        failwith
          ("Fixture unexpectedly branches at "
          ^ InterCfg.Node.to_string node
          ^ " to "
          ^ String.concat ", " (List.map IntraCfg.Node.to_string nexts))
  in
  let state = walk InterCfg.global_proc InterCfg.start_node (Mem.bot, global) in
  let mem, global = walk "main" (InterCfg.entryof global.icfg "main") state in
  let find name =
    let vi =
      List.find_map
        (function
          | Cil.GVar (vi, _, _) when vi.Cil.vname = name -> Some vi | _ -> None)
        global.file.globals
      |> Option.get
    in
    Mem.find (Loc.of_gvar name vi.vtype) mem
  in
  check
    (Itv.eq (Val.itv_of_val (find "length")) (interval 3))
    "strlen lost the literal's length";
  check
    (Itv.eq (Val.itv_of_val (find "literal_size")) (interval 4))
    "sizeof literal became pointer size";
  check
    (not (Val.eq (find "character") Val.bot))
    "Literal dereference disappeared";
  let allocations =
    List.filter
      (fun node ->
        match InterCfg.cmdof global.icfg node with
        | IntraCfg.Cmd.Csalloc _ -> true
        | _ -> false)
      (InterCfg.nodes_of_pid global.icfg "table")
  in
  check (List.length allocations = 2) "String initializer allocations were lost";
  List.iter
    (fun node ->
      match InterCfg.cmdof global.icfg node with
      | IntraCfg.Cmd.Csalloc (lv, s, _) ->
          let mem, _ =
            ItvSem.run AbsSem.Strong ItvSem.Spec.empty node (mem, global)
          in
          check_string mem
            (ItvSem.eval "table" (Cil.Lval lv) mem)
            (String.length s + 1)
      | _ -> assert false)
    allocations

let () =
  Cil.initCIL ();
  run_fixture Sys.argv.(1) false;
  run_fixture Sys.argv.(1) true;
  let rejects e =
    try
      ignore (ItvSem.eval "main" e Mem.bot);
      false
    with Invalid_argument _ -> true
  in
  check
    (rejects (Cil.mkString "unlowered"))
    "Unlowered literal silently became numeric top";
  check
    (rejects (Cil.Const (Cil.CWStr ([ 65L ], Cil.Wchar_t))))
    "Unsupported wide literal silently became numeric top"
