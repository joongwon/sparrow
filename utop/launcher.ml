let () =
  let dir = ref "" in
  let prefix = ref "merged" in
  let args = ref [] in
  Arg.parse
    [
      ("--marshal-dir", Arg.Set_string dir, "DIR Load saved interval states");
      ("--prefix", Arg.Set_string prefix, "NAME Snapshot basename (default: merged)");
      ("--", Arg.Rest (fun arg -> args := arg :: !args), "Pass remaining options to utop");
    ]
    (fun arg -> raise (Arg.Bad ("Unexpected argument: " ^ arg)))
    "sparrow-utop [--marshal-dir DIR] [--prefix merged] [-- UTOP_OPTIONS]";
  try
    Findlib.init ();
    let init = Filename.concat (Findlib.package_directory "sparrow") "utop_init.ml" in
    if not (Sys.file_exists init) then failwith ("Missing initialization file: " ^ init);
    Unix.putenv "SPARROW_UTOP_DIR" !dir;
    Unix.putenv "SPARROW_UTOP_PREFIX" !prefix;
    Unix.execvp "utop"
      (Array.of_list ([ "utop"; "-init"; init ] @ List.rev !args))
  with exn ->
    Printf.eprintf "sparrow-utop: %s\n%!" (Printexc.to_string exn);
    exit 1
