let contains text fragment =
  try
    ignore (Str.search_forward (Str.regexp_string fragment) text 0);
    true
  with Not_found -> false

let check condition message = if not condition then failwith message

let rec remove path =
  if Sys.is_directory path then (
    Array.iter
      (fun name -> remove (Filename.concat path name))
      (Sys.readdir path);
    Unix.rmdir path)
  else Sys.remove path

let () =
  GoblintCil.Cil.initCIL ();
  let source =
    GoblintCil.Frontc.parse Sys.argv.(1) () |> Frontend.makeCFGinfo
  in
  let global = Global.init source in
  let signatures = VisReport.function_signatures global.file in
  let signature name =
    Str.global_replace (Str.regexp "[ \t\r\n]+") " "
      (Hashtbl.find signatures name)
  in
  check
    (contains (signature "callee") "int callee(int x")
    "Signature must include return type and named parameters";
  check
    (contains (signature "main") "main(void)")
    "Signature must preserve a void parameter list";
  check
    (contains (signature "choose") "callback"
    && contains (signature "choose") "..."
    && contains (signature "choose") "(*")
    "Signature must preserve function pointers and variadic parameters";
  let nodes = InterCfg.nodes_of_pid global.icfg "main" in
  let direct =
    List.find
      (fun node ->
        VisReport.direct_callee (InterCfg.cmdof global.icfg node)
        = Some "callee")
      nodes
  in
  let indirect =
    List.find
      (fun node ->
        InterCfg.is_callnode node global.icfg
        && VisReport.direct_callee (InterCfg.cmdof global.icfg node) = None)
      nodes
  in
  let icfg = InterCfg.add_call_edge indirect "callee" global.icfg in
  let icfg = InterCfg.add_call_edge direct "callee" icfg in
  let callers = VisReport.caller_nodes icfg in
  check
    (List.sort InterCfg.Node.compare (Hashtbl.find callers "callee")
    = List.sort InterCfg.Node.compare [ direct; indirect ])
    "Caller index must include direct and resolved indirect calls without \
     duplicates";
  let global = { global with icfg } in
  let describe analysis node = VisReport.node_command ~analysis icfg node in
  check
    (contains (describe "itv" (InterCfg.entryof icfg "main")) "function entry")
    "Missing entry role";
  check
    (contains (describe "itv" (InterCfg.exitof icfg "main")) "function exit")
    "Missing exit role";
  check
    (contains (describe "oct" InterCfg.start_node) "octagon init")
    "Missing octagon initialization";
  let returned = InterCfg.returnof direct icfg in
  check
    (contains (describe "itv" returned) "call return: callee"
    && contains (describe "itv" returned) "<- return, weak")
    "Missing implicit return-value assignment";
  check
    (not (contains (describe "oct" returned) "<- return, weak"))
    "Octagon return point incorrectly claims interval semantics";
  check
    (contains (describe "itv" (InterCfg.returnof indirect icfg)) "call return:")
    "Missing indirect-call return role";
  let external_call =
    List.find
      (fun node ->
        VisReport.direct_callee (InterCfg.cmdof icfg node) = Some "external_fn")
      nodes
  in
  check
    (contains
       (describe "itv" (InterCfg.returnof external_call icfg))
       "call continuation: external_fn")
    "External continuation incorrectly claims a return-value transfer";
  let root = Filename.temp_file "sparrow-vis-test" "" in
  Sys.remove root;
  Unix.mkdir root 0o755;
  Fun.protect
    ~finally:(fun () ->
      if Sys.getenv_opt "SPARROW_VIS_KEEP_TEST_REPORT" = Some "1" then
        Printf.printf "Test report: %s/report/index.html\n%!" root
      else remove root)
    (fun () ->
      let snapshot name value =
        VisReport.write (Filename.concat root name) (fun ch ->
            Marshal.to_channel ch value [])
      in
      snapshot "fixture.itv.global" global;
      let loc = BasicDom.Loc.of_gvar "fixture_value" GoblintCil.Cil.intType in
      let mem = ItvDom.Mem.add loc (ItvDom.Val.of_itv Itv.top) ItvDom.Mem.bot in
      snapshot "fixture.itv.input"
        (ItvDom.Table.add direct mem ItvDom.Table.bot);
      snapshot "fixture.itv.output" ItvDom.Table.bot;
      let out = Filename.concat root "report" in
      VisReport.generate ~dir:root ~prefix:"fixture" ~analysis:"itv" ~out
        ~dot:"dot";
      let page =
        VisReport.read (Filename.concat out (VisReport.function_file "main"))
      in
      let callee_page =
        VisReport.read (Filename.concat out (VisReport.function_file "callee"))
      in
      check
        (contains callee_page "Caller nodes (2)")
        "Function page must show the caller count";
      List.iter
        (fun node ->
          check
            (contains callee_page
               ("href=\""
               ^ VisReport.function_file "main"
               ^ "#" ^ VisReport.node_id node ^ "\""))
            "Caller link must target the exact calling node")
        [ direct; indirect ];
      let uncalled_page =
        VisReport.read (Filename.concat out (VisReport.function_file "choose"))
      in
      check
        (contains uncalled_page "No caller nodes recorded.")
        "Functions without callers must show an empty state";
      let svg =
        VisReport.read
          (Filename.concat out
             (Filename.remove_extension (VisReport.function_file "main")
             ^ ".svg"))
      in
      check
        (contains page "class=\"function-signature\""
        && contains page "main(void)")
        "Function page must show its signature";
      check
        (contains page "external / no CFG")
        "External callee should be marked";
      check
        (contains svg ("xlink:href=\"" ^ VisReport.function_file "callee"))
        "Missing callee link";
      check (contains svg "Possible callees:") "Missing indirect call targets";
      check
        (contains page "\"output\":null")
        "Missing state must not be rendered as bottom";
      check (contains page (VisReport.node_id direct)) "Missing node metadata";
      List.iter
        (fun label ->
          check (contains page label) ("Missing state-panel label: " ^ label);
          check (contains svg label) ("Missing graph label: " ^ label))
        [
          "function entry";
          "function exit";
          "call return: callee";
          "call continuation: external_fn";
        ];
      let states = Filename.concat out "states" in
      check
        (Array.length (Sys.readdir states) = 1)
        "Expected one recorded state";
      check
        (contains
           (VisReport.read (Filename.concat states (Sys.readdir states).(0)))
           "fixture_value")
        "Recorded binding must remain visible";
      check
        (VisReport.display_text "\000\025\255" = "\\x00\\x19\\xff")
        "Binary bytes must be escaped";
      let dangerous = "</script><script>alert('x')</script>&" in
      check
        (not (contains (VisReport.json (`String dangerous)) "<"))
        "Unsafe JSON embedding";
      check (VisReport.html "<&\"" = "&lt;&amp;&quot;") "Unsafe HTML escaping";
      let known = Hashtbl.create 1 in
      Hashtbl.add known "a/b" ();
      check
        (contains
           (VisReport.link_cell known "a/b")
           (VisReport.function_file "a/b"))
        "Unsafe function filename";
      (* Exercise the current portable octagon snapshot representation too. *)
      snapshot "fixture.oct.global" global;
      let pack = OctDom.Pack.singleton (OctDom.OctLoc.of_loc loc) in
      let oct_mem =
        OctDom.Mem.add pack (OctDom.Octagon.top pack) OctDom.Mem.bot
      in
      snapshot "fixture.oct.input"
        (OctAnalysis.serialize_table
           (OctAnalysis.Table.add direct oct_mem OctAnalysis.Table.bot));
      snapshot "fixture.oct.output"
        (OctAnalysis.serialize_table OctAnalysis.Table.bot);
      VisReport.generate ~dir:root ~prefix:"fixture" ~analysis:"oct"
        ~out:(Filename.concat root "oct-report")
        ~dot:"dot";
      (* Existing output is never silently overwritten. *)
      check
        (try
           VisReport.generate ~dir:root ~prefix:"fixture" ~analysis:"itv" ~out
             ~dot:"dot";
           false
         with Failure _ -> true)
        "Existing report was overwritten")
