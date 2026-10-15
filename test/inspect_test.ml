let check condition message = if not condition then failwith message

let expect_error f =
  match f () with
  | exception (Failure _ | Invalid_argument _) -> ()
  | _ -> failwith "Expected an inspection error"

let () =
  expect_error Inspect.current;
  GoblintCil.Cil.initCIL ();
  let file = GoblintCil.Frontc.parse Sys.argv.(1) () |> Frontend.makeCFGinfo in
  let global = Global.init file in
  let n = InterCfg.entryof global.icfg "main" in
  let loc = BasicDom.Loc.of_gvar "test_value" GoblintCil.Cil.intType in
  let mem i =
    ItvDom.Mem.add loc (ItvDom.Val.of_itv (Itv.of_int i)) ItvDom.Mem.bot
  in
  let before = mem 1 and after = mem 2 in
  let root = Filename.temp_file "sparrow-inspect-" "" in
  Sys.remove root;
  Unix.mkdir root 0o700;
  Fun.protect
    ~finally:(fun () ->
      Array.iter (fun name -> Sys.remove (Filename.concat root name)) (Sys.readdir root);
      Unix.rmdir root)
    (fun () ->
      let write suffix value =
        let ch = open_out_bin (Filename.concat root ("fixture.itv." ^ suffix)) in
        Fun.protect ~finally:(fun () -> close_out ch) (fun () ->
            Marshal.to_channel ch value [])
      in
      write "global" global;
      write "input" (ItvDom.Table.add n before ItvDom.Table.bot);
      write "output" (ItvDom.Table.add n after ItvDom.Table.bot);
      Inspect.load ~prefix:"fixture" root;
      check (List.mem "main" (Inspect.functions ())) "Missing function";
      check (List.mem n (Inspect.nodes ~func:"main" ())) "Missing node";
      let found = Inspect.node (InterCfg.Node.to_string n) in
      check (InterCfg.Node.equal n found) "Node name did not round-trip";
      check (ItvDom.Mem.eq before (Inspect.input found)) "Wrong input state";
      check (ItvDom.Mem.eq after (Inspect.output found)) "Wrong output state";
      expect_error (fun () -> Inspect.node "not-a-node");
      expect_error (fun () -> Inspect.nodes ~func:"not-a-function" ());
      expect_error (fun () -> Inspect.input (InterCfg.exitof global.icfg "main"));
      let previous = Inspect.current () in
      Sys.remove (Filename.concat root "fixture.itv.output");
      expect_error (fun () -> Inspect.load ~prefix:"fixture" root);
      check (Inspect.current () == previous) "Failed load replaced the session")
