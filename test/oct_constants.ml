let () =
  let analyzer = Sys.argv.(1) in
  let output = Filename.temp_file "sparrow-oct-constants" ".log" in
  let fd = Unix.openfile output [ Unix.O_WRONLY; Unix.O_TRUNC ] 0o600 in
  let pid =
    Unix.create_process analyzer
      [| analyzer; "-oct"; Sys.argv.(2) |]
      Unix.stdin fd fd
  in
  Unix.close fd;
  let _, status = Unix.waitpid [] pid in
  let ic = open_in output in
  let log = really_input_string ic (in_channel_length ic) in
  close_in ic;
  Unix.unlink output;
  (* Sparrow currently catches analysis exceptions without a nonzero exit. *)
  let finished =
    try
      ignore (Str.search_forward (Str.regexp_string "Finished properly.") log 0);
      true
    with Not_found -> false
  in
  if status <> Unix.WEXITED 0 || not finished then (
    prerr_string log;
    failwith "Octagon analysis failed on large integer constants")
