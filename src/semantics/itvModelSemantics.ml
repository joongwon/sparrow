(* The interval library models as a functor: syntax and the API dictionary
   are inputs; policy, memory and identities are explicit inputs of the
   computation.  ItvSem is the direct instance. *)
open Sparrow_cil
open BasicDom
open ItvDom
open ItvSemantics

module Make (S : STAGE) = struct
  include ItvSemantics.Make (S)
  open S

  let text s = literal (Text s)
  let fail message = p1 Fail_memory (text message)
  let alloc_loc site = p1 Locs_singleton (p1 Loc_of_allocsite site)
  let named_site name = p1 Named_external_site (text name)

  let array_make site offset size stride null =
    app
      (app (app (app (app (primitive Array_make) site) offset) size) stride)
      null

  let default_spec () = p1 Default_spec unit

  let model_alloc_one mode spec cg pid lvo f mem =
    match lvo with
    | None -> mem
    | Some lv ->
        let* size = p1 Alloc_one_size (literal (Type f.vtype)) in
        let* site = named_site (SourceName.of_varinfo f) in
        let* array =
          p1 Val_of_array
            (array_make site (interval Itv.zero) (interval Itv.one) size
               (interval Itv.nat))
        in
        let* locations = alloc_loc site in
        let* mem = update mode spec cg (eval_lv spec pid lv mem) array mem in
        update mode spec cg locations (value Val.itv_top) mem

  let model_realloc mode spec cg node lvo expressions mem =
    match (lvo, expressions) with
    | None, _ -> mem
    | Some lv, _ :: size :: _ ->
        array_assign mode spec cg node lv size false mem
    | Some _, _ -> fail "Error: arguments of realloc are not given"

  let model_calloc mode spec cg node lvo expressions mem =
    match (lvo, expressions) with
    | None, _ -> mem
    | Some lv, n :: size :: _ ->
        array_assign mode spec cg node lv
          (BinOp (Mult, n, size, uintType))
          false mem
    | Some _, _ -> fail "Error: arguments of realloc are not given"

  let model_scanf mode spec cg pid expressions mem =
    match expressions with
    | [] -> mem
    | _ :: rest ->
        List.fold_left
          (fun mem -> function
            | AddrOf lv ->
                let* mem = mem in
                update mode spec cg (eval_lv spec pid lv mem)
                  (value Val.itv_top) mem
            | _ -> mem)
          mem rest

  let model_strdup mode spec cg node pid lvo expressions mem =
    match (lvo, expressions) with
    | Some lv, str :: _ ->
        let* site = p1 Node_allocsite node in
        let* source = p1 Val_array (eval spec pid str mem) in
        let* size = p1 Array_size source in
        let* null = p1 Array_null source in
        let* sources = p1 Array_locs source in
        let* array =
          array_make site (interval Itv.zero)
            (p2 Itv_minus size (interval Itv.zero))
            (interval Itv.one) null
        in
        let* locations = alloc_loc site in
        let* v =
          p2 Val_join (p1 Val_of_array array) (p1 Val_of_locs locations)
        in
        let* mem = update mode spec cg (eval_lv spec pid lv mem) v mem in
        update mode spec cg locations (lookup sources mem) mem
    | _ -> mem

  let model_input mode spec cg pid lvo mem =
    match lvo with
    | None -> mem
    | Some lv ->
        let* site = p1 External_site unit in
        let* v = p1 External_value site in
        let* locations = alloc_loc site in
        let* mem = update mode spec cg (eval_lv spec pid lv mem) v mem in
        update mode spec cg locations (value Val.itv_top) mem

  let model_assign mode spec cg pid lvo expressions mem =
    match (lvo, expressions) with
    | Some lv, e :: _ -> assign mode spec cg pid lv e mem
    | _ -> mem

  let model_strlen mode spec cg pid lvo expressions mem =
    match (lvo, expressions) with
    | Some lv, str :: _ ->
        let* v = eval spec pid str mem in
        let* null = p1 Array_null (p1 Val_array v) in
        let* v = of_itv (p2 Itv_meet (interval Itv.nat) null) in
        update mode spec cg (eval_lv spec pid lv mem) v mem
    | _ -> mem

  let rec model_fgets mode spec cg pid lvo expressions mem =
    match expressions with
    | Lval buf :: size :: _ | StartOf buf :: size :: _ ->
        let* size = itv (eval spec pid size mem) in
        let* locations = eval_lv spec pid buf mem in
        let* array = p1 Val_array (lookup locations mem) in
        let* elements = p1 Array_locs array in
        let* v =
          p1 Val_of_array
            (p2 Array_set_null array (p2 Itv_join (interval Itv.zero) size))
        in
        let* mem = update mode spec cg locations v mem in
        update mode spec cg elements (value Val.itv_top) mem
    | CastE (_, _, buf) :: size :: rest ->
        model_fgets mode spec cg pid lvo (buf :: size :: rest) mem
    | _ -> mem

  let rec model_sprintf mode spec cg pid lvo expressions mem =
    match expressions with
    | [ Lval buf; str ] | [ StartOf buf; str ] -> (
        let* source = p1 Val_array (eval spec pid str mem) in
        let* sources = p1 Array_locs source in
        let* null = p1 Array_null source in
        let* locations = eval_lv spec pid buf mem in
        let* array = p1 Val_array (lookup locations mem) in
        let* elements = p1 Array_locs array in
        let* v = p1 Val_of_array (p2 Array_set_null array null) in
        (* The reads and return destination use the input
           memory, while the writes compose over the updated accumulator. *)
        let original = mem in
        let* mem = update mode spec cg locations v mem in
        let* mem = update mode spec cg elements (lookup sources original) mem in
        match lvo with
        | None -> mem
        | Some lv ->
            update mode spec cg (eval_lv spec pid lv original) (of_itv null) mem
        )
    | [ CastE (_, _, buf); str ] | [ buf; CastE (_, _, str) ] ->
        model_sprintf mode spec cg pid lvo [ buf; str ] mem
    | _ -> (
        match lvo with
        | None -> mem
        | Some lv ->
            update mode spec cg (eval_lv spec pid lv mem)
              (of_itv (interval Itv.nat))
              mem)

  let sparrow_arg mode spec cg pid expressions mem =
    match expressions with
    | Lval argc :: Lval argv :: _ ->
        let* argv_site = named_site "argv" in
        let* argv_value = p1 Val_of_array (p1 Array_input argv_site) in
        let* arg_site = named_site "arg" in
        let* arg_value = p1 Val_of_array (p1 Array_input arg_site) in
        let original = mem in
        let* mem =
          update mode spec cg
            (eval_lv spec pid argc original)
            (of_itv (interval Itv.pos))
            mem
        in
        let* mem =
          update mode spec cg (eval_lv spec pid argv original) argv_value mem
        in
        let* mem = update mode spec cg (alloc_loc argv_site) arg_value mem in
        update mode spec cg (alloc_loc arg_site) (of_itv (interval Itv.top)) mem
    | _ -> mem

  let sparrow_opt mode spec cg pid expressions mem =
    match expressions with
    | Lval optind :: Lval optarg :: _ ->
        let* site = named_site "arg" in
        let* v = p1 Val_of_array (p1 Array_input site) in
        let original = mem in
        let* mem =
          update mode spec cg
            (eval_lv spec pid optind original)
            (of_itv (interval Itv.nat))
            mem
        in
        let* mem =
          update mode spec cg (eval_lv spec pid optarg original) v mem
        in
        update mode spec cg (alloc_loc site) (of_itv (interval Itv.top)) mem
    | _ -> mem

  (* An explicit compatibility policy for clients; it is not the sparrow_arg
     model.  The direct instance keeps the default. *)
  let generic_external_effect store locations mem =
    let* site = p1 External_site unit in
    let* external_value = p1 External_value site in
    let null = value (Val.of_pow_loc (PowLoc.singleton Loc.null)) in
    let* v =
      p2 Val_join (value Val.itv_top) (p2 Val_join external_value null)
    in
    let* mem = store locations v mem in
    store (alloc_loc site) (value Val.itv_top) mem

  let model_unknown mode spec cg pid lvo f mem =
    match lvo with
    | None -> mem
    | Some lv ->
        if_
          (p1 Arithmetic_lvalue (literal (Lvalue_type_query lv)))
          (fun () ->
            update mode spec cg (eval_lv spec pid lv mem)
              (p1 Unknown_scalar (literal (Lvalue_type_query lv)))
              mem)
          (fun () ->
            let* site = named_site (SourceName.of_varinfo f) in
            let* v = p2 Unknown_array site (literal (Lvalue_type_query lv)) in
            let* locations = alloc_loc site in
            let* mem = update mode spec cg (eval_lv spec pid lv mem) v mem in
            update mode spec cg locations (value Val.itv_top) mem)

  let model_memcpy mode spec cg pid lvo expressions mem =
    match (lvo, expressions) with
    | Some lv, dst :: src :: _ ->
        let* source = eval spec pid src mem in
        let* destination = eval spec pid dst mem in
        let* sources = p1 Array_locs (p1 Val_array source) in
        let* destinations = p1 Array_locs (p1 Val_array destination) in
        let original = mem in
        let* mem =
          update mode spec cg destinations (lookup sources original) mem
        in
        update mode spec cg (eval_lv spec pid lv original) destination mem
    | _ -> mem

  let model_getpwent mode spec cg node pid lvo f mem =
    match (lvo, f.vtype) with
    | Some lv, TFun ((TPtr ((TComp (comp, _) as elem), _) as ptr), _, _, _) ->
        let* locations = eval_lv spec pid lv mem in
        let* v =
          app
            (app
               (app (primitive Val_cast_types) (literal (Type ptr)))
               (p1 Lvalue_type (literal (Lvalue_type_query lv))))
            (array_alloc spec node (SizeOf elem) false mem)
        in
        let* field =
          p2 Named_field (literal (Composite comp)) (text "pw_name")
        in
        let* fields = p2 Array_field (p1 Val_array v) field in
        let* site = named_site "getpwent.pw_name" in
        let* external_value = p1 Val_of_array (p1 Array_input site) in
        let* elements = alloc_loc site in
        let* mem = update mode spec cg locations v mem in
        let* mem = update mode spec cg fields external_value mem in
        update mode spec cg elements (value Val.itv_top) mem
    | _ -> mem

  let rec model_string_copy plus mode spec cg pid expressions mem =
    match expressions with
    | CastE (_, _, e) :: rest ->
        model_string_copy plus mode spec cg pid (e :: rest) mem
    | [ dst; CastE (_, _, e) ] ->
        model_string_copy plus mode spec cg pid [ dst; e ] mem
    | [ Lval dst; Lval src ]
    | [ StartOf dst; StartOf src ]
    | [ Lval dst; StartOf src ]
    | [ StartOf dst; Lval src ] ->
        let* source = p1 Val_array (lookup (eval_lv spec pid src mem) mem) in
        let* destination =
          p1 Val_array (lookup (eval_lv spec pid dst mem) mem)
        in
        let* null = p1 Array_null source in
        let* v =
          p1 Val_of_array
            (p2
               (if plus then Array_plus_null else Array_set_null)
               destination null)
        in
        update mode spec cg (eval_lv spec pid dst mem) v mem
    | _ -> mem

  let rec model_strncpy mode spec cg pid expressions mem =
    match expressions with
    | CastE (_, _, e) :: rest -> model_strncpy mode spec cg pid (e :: rest) mem
    | Lval dst :: _ :: size :: _ | StartOf dst :: _ :: size :: _ ->
        let* array = p1 Val_array (lookup (eval_lv spec pid dst mem) mem) in
        let* size = itv (eval spec pid size mem) in
        let* null =
          p2 Itv_join (interval Itv.zero) (p2 Itv_minus size (interval Itv.one))
        in
        let* v = p1 Val_of_array (p2 Array_set_null array null) in
        update mode spec cg (eval_lv spec pid dst mem) v mem
    | _ -> mem

  let rec model_strchr mode spec cg pid lvo expressions mem =
    match (lvo, expressions) with
    | Some _, CastE (_, _, e) :: rest ->
        model_strchr mode spec cg pid lvo (e :: rest) mem
    | Some lv, Lval str :: _ | Some lv, StartOf str :: _ ->
        let* array = p1 Val_array (lookup (eval_lv spec pid str mem) mem) in
        let* null = p1 Array_null array in
        let* v = p1 Val_of_array (p2 Array_plus array null) in
        update mode spec cg (eval_lv spec pid lv mem) v mem
    | _ -> mem

  let sparrow_array_init mode spec cg node pid expressions mem =
    match expressions with
    | arr :: (Const (CInt _) :: _ as rest) ->
        let* locations = p1 Array_locs (p1 Val_array (eval spec pid arr mem)) in
        let rec loop acc = function
          | [] -> update mode spec cg locations acc mem
          | e :: rest ->
              let* v = eval spec pid e mem in
              let* acc = p2 Val_join v acc in
              loop acc rest
        in
        loop (value Val.bot) rest
    | arr :: (Const (CStr _) :: _ as rest) ->
        let* locations = p1 Array_locs (p1 Val_array (eval spec pid arr mem)) in
        let rec loop acc = function
          | [] -> update mode spec cg locations acc mem
          | Const (CStr (s, _)) :: rest ->
              let* v = string_alloc node s in
              let* acc = p2 Val_join v acc in
              loop acc rest
          | _ :: rest -> loop acc rest
        in
        loop (value Val.bot) rest
    | [] | [ _ ] -> fail "nth"
    | _ -> mem

  let eval_src kind pid mem e =
    match kind with
    | ApiSem.Value -> eval (default_spec ()) pid e mem
    | ApiSem.Array ->
        let* locations = p1 Val_all_locs (eval (default_spec ()) pid e mem) in
        lookup locations mem

  (* Continuations sequence the reads even if a model later discards
     a collected value. The list shape is syntax, never an abstract value. *)
  let collect_values select pid mem expressions types k =
    let rec collect acc expressions types =
      match (expressions, types) with
      | [], _ | _, [] -> k (List.rev acc)
      | e :: expressions, kind :: types -> (
          match select kind with
          | None -> collect acc expressions types
          | Some (ApiSem.Fixed, kind) ->
              let* v = eval_src kind pid mem e in
              collect (v :: acc) expressions types
          | Some (ApiSem.Variable, kind) ->
              if types <> [] then
                fail
                  "itvSem.ml : API encoding error (Varg not at the last \
                   position)"
              else
                let rec remaining acc = function
                  | [] -> k (List.rev acc)
                  | e :: rest ->
                      let* v = eval_src kind pid mem e in
                      remaining (v :: acc) rest
                in
                remaining acc (e :: expressions))
    in
    collect [] expressions types

  let join_values vs = List.fold_left (p2 Val_join) (value Val.bot) vs

  let va_source types =
    List.exists
      (function ApiSem.Src (ApiSem.Variable, _, _) -> true | _ -> false)
      types

  let assert_model line condition k =
    let* _ = p2 Assert_condition (literal (Int line)) (bool condition) in
    k ()

  let process_dst mode spec cg pid sources mem e =
    let* source = join_values sources in
    let* locations = p1 Val_all_locs (eval (default_spec ()) pid e mem) in
    update mode spec cg locations source mem

  let process_buf mode spec cg node pid mem e =
    let* locations = p1 Val_all_locs (eval (default_spec ()) pid e mem) in
    let* site = p1 Node_allocsite node in
    let* v = p1 External_value site in
    update mode spec cg locations v mem

  let process_struct_ptr mode spec cg node pid mem e =
    let* locations = p1 Val_all_locs (eval (default_spec ()) pid e mem) in
    let* site = p1 Node_allocsite node in
    let* v = p1 External_value site in
    let* external_locations = p1 Val_all_locs v in
    let* mem = update mode spec cg locations v mem in
    update mode spec cg external_locations v mem

  let rec process_args mode spec cg node pid expressions types sources mem =
    let va = va_source types in
    let rec each process mem = function
      | [] -> mem
      | e :: rest ->
          let* mem = process mem e in
          each process mem rest
    in
    match (expressions, types) with
    | [], _ | _, [] -> mem
    | _, [ ApiSem.Dst (ApiSem.Variable, _) ] ->
        assert_model 681
          (va || List.length sources > 0)
          (fun () ->
            each (process_dst mode spec cg pid sources) mem expressions)
    | _, ApiSem.Dst (ApiSem.Variable, _) :: _ ->
        fail "API encoding error (Varg not at the last position)"
    | e :: rest, ApiSem.Dst (ApiSem.Fixed, _) :: types ->
        assert_model 686
          (va || List.length sources > 0)
          (fun () ->
            let* mem = process_dst mode spec cg pid sources mem e in
            process_args mode spec cg node pid rest types sources mem)
    | _, [ ApiSem.Buf (ApiSem.Variable, _) ] ->
        each (process_buf mode spec cg node pid) mem expressions
    | _, ApiSem.Buf (ApiSem.Variable, _) :: _ ->
        fail "API encoding error (Varg not at the last position)"
    | e :: rest, ApiSem.Buf (ApiSem.Fixed, _) :: types ->
        let* mem = process_buf mode spec cg node pid mem e in
        process_args mode spec cg node pid rest types sources mem
    | e :: rest, ApiSem.StructPtr :: types ->
        let* mem = process_struct_ptr mode spec cg node pid mem e in
        process_args mode spec cg node pid rest types sources mem
    | _ :: rest, (ApiSem.Src _ | ApiSem.Size | ApiSem.Skip) :: types ->
        process_args mode spec cg node pid rest types sources mem

  let gen_block mode spec cg node initial mem k =
    let* site = p1 Node_allocsite node in
    let* array =
      array_make site
        (interval (Itv.of_int 0))
        (interval Itv.top)
        (interval (Itv.of_int 1))
        (interval Itv.nat)
    in
    let* v = p1 Val_of_array array in
    let* locations = alloc_loc site in
    let* mem = update mode spec cg locations initial mem in
    k mem v

  let produce_ret mode spec cg node kind va sources destinations buffers sizes
      mem k =
    let one line values =
      assert_model line
        (List.length values = 1)
        (fun () -> match values with v :: _ -> k mem v | [] -> fail "hd")
    in
    match kind with
    | ApiSem.Const | ApiSem.TaintInput -> k mem (value Val.itv_top)
    | ApiSem.SrcArg -> one 722 sources
    | ApiSem.SizeArg -> one 725 sizes
    | ApiSem.DstArg -> one 731 destinations
    | ApiSem.BufArg -> one 734 buffers
    | ApiSem.TopWithSrcTaint ->
        assert_model 728
          (va || List.length sources > 0)
          (fun () -> k mem (value Val.itv_top))
    | ApiSem.AllocConst | ApiSem.AllocBuf ->
        gen_block mode spec cg node (value Val.itv_top) mem k
    | ApiSem.AllocDst ->
        assert_model 739
          (va || List.length sources > 0)
          (fun () ->
            let* source = join_values sources in
            gen_block mode spec cg node source mem k)
    | ApiSem.AllocStruct ->
        let* site = p1 Node_allocsite node in
        let* v = p1 External_value site in
        gen_block mode spec cg node v mem k

  let handle_api mode spec cg node pid lvo expressions mem api =
    let types = api.ApiSem.arg_typs in
    collect_values
      (function ApiSem.Src (v, k, _) -> Some (v, k) | _ -> None)
      pid mem expressions types
      (fun sources ->
        collect_values
          (function ApiSem.Dst (v, _) -> Some (v, ApiSem.Value) | _ -> None)
          pid mem expressions types
          (fun destinations ->
            collect_values
              (function
                | ApiSem.Buf (v, _) -> Some (v, ApiSem.Value) | _ -> None)
              pid mem expressions types
              (fun buffers ->
                collect_values
                  (function
                    | ApiSem.Size -> Some (ApiSem.Fixed, ApiSem.Value)
                    | _ -> None)
                  pid mem expressions types
                  (fun sizes ->
                    let* mem =
                      process_args mode spec cg node pid expressions types
                        sources mem
                    in
                    match lvo with
                    | None -> mem
                    | Some lv ->
                        produce_ret mode spec cg node api.ApiSem.ret_typ
                          (va_source types) sources destinations buffers sizes
                          mem (fun mem v ->
                            update mode spec cg (eval_lv spec pid lv mem) v mem)))))

  let mem_alloc_libs =
    [
      "__ctype_b_loc";
      "initscr";
      "newwin";
      "localtime";
      "getpwnam";
      "__errno_location";
      "opendir";
      "readdir";
      "fopen";
      "fdopen";
      "localtime";
    ]

  let scaffolded_functions mode spec cg node pid lvo f expressions mem =
    if_ (p1 Scaffold unit)
      (fun () ->
        match SourceName.of_varinfo f with
        | "fgets" -> model_fgets mode spec cg pid lvo expressions mem
        | "sprintf" -> model_sprintf mode spec cg pid lvo expressions mem
        | "scanf" -> model_scanf mode spec cg pid expressions mem
        | "getenv" -> model_input mode spec cg pid lvo mem
        | "strdup" -> model_strdup mode spec cg node pid lvo expressions mem
        | "gettext" -> model_assign mode spec cg pid lvo expressions mem
        | "memcpy" -> model_memcpy mode spec cg pid lvo expressions mem
        | "getpwent" -> model_getpwent mode spec cg node pid lvo f mem
        | "strcpy" -> model_string_copy false mode spec cg pid expressions mem
        | "strcat" -> model_string_copy true mode spec cg pid expressions mem
        | "strncpy" -> model_strncpy mode spec cg pid expressions mem
        | "strchr" | "strrchr" ->
            model_strchr mode spec cg pid lvo expressions mem
        | s when List.mem s mem_alloc_libs ->
            model_alloc_one mode spec cg pid lvo f mem
        | s when ApiSem.ApiMap.mem s ApiSem.api_map ->
            handle_api mode spec cg node pid lvo expressions mem
              (ApiSem.ApiMap.find s ApiSem.api_map)
        | _ -> model_unknown mode spec cg pid lvo f mem)
      (fun () -> model_unknown mode spec cg pid lvo f mem)

  let undefined_call ?generic_argv mode spec cg node pid lvo f expressions mem
      location =
    let name = SourceName.of_varinfo f in
    let key = CilHelper.s_location location ^ ":" ^ name in
    if_
      (p2 Unsound_library spec (text key))
      (fun () -> mem)
      (fun () ->
        let* _ = discard (eval_list spec pid expressions mem) in
        match name with
        | "sparrow_arg" -> (
            match generic_argv with
            | None -> sparrow_arg mode spec cg pid expressions mem
            | Some locations ->
                generic_external_effect (update mode spec cg) locations mem)
        | "sparrow_opt" -> sparrow_opt mode spec cg pid expressions mem
        | "sparrow_print" ->
            if_ (p1 Verbose unit)
              (fun () ->
                let* vs = eval_list spec pid expressions mem in
                let* description =
                  p2 Text_concat
                    (p1 Describe_expressions
                       (literal (Description expressions)))
                    (text (" @ " ^ CilHelper.s_location location))
                in
                let* _ = p2 Print_values description vs in
                mem)
              (fun () -> mem)
        | "sparrow_dump" ->
            if_ (p1 Verbose unit)
              (fun () ->
                let* _ =
                  p2 Print_memory (text (CilHelper.s_location location)) mem
                in
                mem)
              (fun () -> mem)
        | "sparrow_assume" -> (
            match expressions with
            | e :: _ -> prune mode spec cg pid e mem
            | [] -> fail "hd")
        | "sparrow_array_init" ->
            sparrow_array_init mode spec cg node pid expressions mem
        | "strlen" -> model_strlen mode spec cg pid lvo expressions mem
        | "realloc" -> model_realloc mode spec cg node lvo expressions mem
        | "calloc" -> model_calloc mode spec cg node lvo expressions mem
        | _ -> scaffolded_functions mode spec cg node pid lvo f expressions mem)
end

module Direct = struct
  include Make (ItvSemantics.Direct_stage)

  let undefined_call mode spec graph node =
    undefined_call mode spec graph (ItvSemantics.node_metadata node)
end
