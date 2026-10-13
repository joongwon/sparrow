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
      (Hashtbl.find signatures name) in
  check (contains (signature "callee") "int callee(int x")
    "Signature must include return type and named parameters";
  check (contains (signature "main") "main(void)")
    "Signature must preserve a void parameter list";
  check (contains (signature "choose") "callback" &&
         contains (signature "choose") "..." &&
         contains (signature "choose") "(*")
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
  let global = { global with icfg } in
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
      let svg =
        VisReport.read
          (Filename.concat out
             (Filename.remove_extension (VisReport.function_file "main")
             ^ ".svg"))
      in
      check (contains page "class=\"function-signature\"" &&
             contains page "main(void)") "Function page must show its signature";
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
