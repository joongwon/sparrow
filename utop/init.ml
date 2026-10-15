#require "sparrow.lib";;

#install_printer InterCfg.Node.pp;;
#install_printer BasicDom.Loc.pp;;
#install_printer Itv.pp;;
#install_printer ItvDom.Val.pp;;
#install_printer ItvDom.Mem.pp;;

open Inspect;;

let () =
  match Sys.getenv_opt "SPARROW_UTOP_DIR" with
  | Some dir when dir <> "" ->
      let prefix =
        Option.value ~default:"merged" (Sys.getenv_opt "SPARROW_UTOP_PREFIX")
      in
      (try
         load ~prefix dir;
         Printf.printf "Loaded %s interval states from %s.\n%!" prefix dir
       with exn ->
         Printf.eprintf "sparrow-utop: %s\n%!" (Printexc.to_string exn);
         exit 1)
  | _ -> ();;

let () =
  print_endline
    "Inspect: load ~prefix:\"merged\" DIR;; functions ();; nodes ~func:\"main\" ();;\n\
     node \"NAME\";; input n;; output n;; current ();;";;
