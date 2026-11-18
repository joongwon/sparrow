(* The CIL frontend policy of every parse: [Frontend.parseOneFile] and any
   client that parses translation units itself.  It is its own module, with
   no dependency on [Frontend], so such a client need not link the
   frontend.

   The CIL frontend follows GCC's constant folding of signed shifts where it
   decides a value (enumerator values, __builtin_constant_p in every context).
   CIL's own default stays upstream's, which suits
   clients detecting undefined shifts. *)
let configure_cil () =
  GoblintCil.Cabs2cil.gccConstantFallback := true
