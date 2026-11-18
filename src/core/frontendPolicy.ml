(* The CIL frontend policy of every parse: [Frontend.parseOneFile] and any
   client that parses translation units itself.  It is its own module, with
   no dependency on [Frontend], so such a client need not link the
   frontend.

   It keeps goblint-cil's defaults. *)
let configure_cil () = ()
