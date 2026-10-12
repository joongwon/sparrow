open OctDom
open Apron

let table () =
  let loc name =
    OctLoc.of_loc (BasicDom.Loc.of_gvar name GoblintCil.Cil.intType)
  in
  let x, y = (loc "x", loc "y") in
  let pack = Pack.add x (Pack.singleton y) in
  let top = Octagon.top pack in
  let var l = Texpr1.Var (OctLoc.to_var l) in
  let c = Texpr1.Cst (Coeff.s_of_mpqf (Mpqf.of_string "9223372036854775807")) in
  let relation =
    Octagon.set y
      (Texpr1.Binop (Texpr1.Add, var x, c, Texpr1.Int, Texpr1.Near))
      top
  in
  let bounded =
    Octagon.prune x
      (Texpr1.Binop
         ( Texpr1.Sub,
           var x,
           Texpr1.Cst (Coeff.s_of_int 7),
           Texpr1.Int,
           Texpr1.Near ))
      Tcons1.EQ relation
  in
  List.fold_left
    (fun table (name, value) ->
      OctAnalysis.Table.add
        (BasicDom.Node.make name IntraCfg.Node.entry)
        (Mem.add pack value Mem.bot)
        table)
    OctAnalysis.Table.bot
    [
      ("bottom", Octagon.bot);
      ("top", top);
      ("relation", relation);
      ("bounded", bounded);
      ("narrowed", Octagon.narrow top bounded);
    ]

let () =
  GoblintCil.Cil.initCIL ();
  if Array.length Sys.argv = 3 && Sys.argv.(1) = "read" then (
    let ic = open_in_bin Sys.argv.(2) in
    let saved = Marshal.from_channel ic in
    close_in ic;
    let restored = OctAnalysis.deserialize_table saved in
    if not (OctAnalysis.Table.eq (table ()) restored) then
      failwith "Octagon table changed during serialization")
  else
    let filename = Filename.temp_file "sparrow-oct-marshal" ".bin" in
    Fun.protect
      ~finally:(fun () -> Sys.remove filename)
      (fun () ->
        let oc = open_out_bin filename in
        Marshal.to_channel oc (OctAnalysis.serialize_table (table ())) [];
        close_out oc;
        let executable = Sys.executable_name in
        let pid =
          Unix.create_process executable
            [| executable; "read"; filename |]
            Unix.stdin Unix.stdout Unix.stderr
        in
        match snd (Unix.waitpid [] pid) with
        | Unix.WEXITED 0 -> ()
        | _ -> failwith "Octagon table could not be read in a fresh process")
