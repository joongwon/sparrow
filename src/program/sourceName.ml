(* Source names of globals the CIL merge renamed.

   Sparrow recognizes a library function by its name: the buffer-overrun
   queries of strcpy/memcpy/... (AlarmExp), the string-argument allocations of
   a call (IntraCfg.transform_string_allocs), malloc/alloca allocations, the
   upstream exit/abort no-return set, and the library models of an undefined
   callee (ItvSem and the other domains).  The merge of several
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

   goblint-cil does not export the merge's record of the names it changed,
   so the source name is the merged name without the suffix [___N] the merge
   appends. *)

let clear () = ()
let install_from_merge () = ()

let source_name name =
  match String.rindex_opt name '_' with
  | Some i
    when i >= 2
         && i < String.length name - 1
         && String.sub name (i - 2) 3 = "___"
         && String.for_all
              (function '0' .. '9' -> true | _ -> false)
              (String.sub name (i + 1) (String.length name - i - 1)) ->
      String.sub name 0 (i - 2)
  | _ -> name

let of_varinfo (v : Sparrow_cil.varinfo) =
  if v.Sparrow_cil.vglob then source_name v.Sparrow_cil.vname
  else v.Sparrow_cil.vname
