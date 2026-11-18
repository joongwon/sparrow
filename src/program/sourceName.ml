(* Source names of globals the CIL merge renamed.

   Sparrow recognizes a library function by its name: the buffer-overrun
   queries of strcpy/memcpy/... (AlarmExp), the string-argument allocations of
   a call (IntraCfg.transform_string_allocs), malloc/alloca allocations, the
   upstream exit/abort no-return set, and the library models of an undefined
   callee (ItvModelSemantics and the other domains).  The merge of several
   translation units renames every global that does not take part in the
   merge of externally visible names (a static, or a GNU [extern inline] body
   such as glibc's fortify wrapper [strcpy]) when an earlier unit already uses
   the name: the second unit's [strcpy] becomes [strcpy___1].  A test of the
   merged name then depends on the input order: only the first unit's calls
   were recognized.  Every such test uses [of_varinfo], the name the
   translation unit itself wrote.

   Which procedure a call denotes (its body or the absence of one,
   [Global.is_undef]) is still the merged name: that is the identity of the
   merged program, not a recognition by name.

   The table is the merge's own record (Mergecil.renamed_globals).  It is
   installed after a merge of several units and cleared by every parse of a
   single unit (Frontend.parseOneFile), so a unit analysed alone, which no
   merge renamed, uses its names as they are. *)

let table : (string, string) Hashtbl.t = Hashtbl.create 64

let clear () = Hashtbl.reset table

let install_from_merge () =
  Hashtbl.reset table;
  List.iter
    (fun (merged, (_, source)) ->
      if merged <> source then Hashtbl.replace table merged source)
    (Sparrow_cil.Mergecil.renamed_globals ())

let of_varinfo (v : Sparrow_cil.varinfo) =
  if v.Sparrow_cil.vglob then
    match Hashtbl.find_opt table v.Sparrow_cil.vname with
    | Some source -> source
    | None -> v.Sparrow_cil.vname
  else v.Sparrow_cil.vname

