(** Interval semantics of undefined library functions. *)

open Sparrow_cil
open BasicDom
open ItvDom
open ItvSemantics

let ext_site name = Allocsite.allocsite_of_ext (Some name)
let alloc_loc site = PowLoc.singleton (Loc.of_allocsite site)

(* One element of the returned pointer's type, in a block of its own. *)
let model_alloc_one mode spec cg pid lvo f mem =
  match lvo with
  | None -> mem
  | Some lv ->
      let site = ext_site (SourceName.of_varinfo f) in
      let array =
        Val.of_array (ArrayBlk.make (Loc.of_allocsite site) Itv.zero Itv.one)
      in
      let locations = alloc_loc site in
      let mem = update mode spec cg (eval_lv spec pid lv mem) array mem in
      update mode spec cg locations Val.itv_top mem

let model_realloc mode spec cg node lvo expressions mem =
  match (lvo, expressions) with
  | None, _ -> mem
  | Some lv, _ :: size :: _ -> array_assign mode spec cg node lv size mem
  | Some _, _ -> failwith "Error: arguments of realloc are not given"

let model_calloc mode spec cg node lvo expressions mem =
  match (lvo, expressions) with
  | None, _ -> mem
  | Some lv, n :: size :: _ ->
      array_assign mode spec cg node lv (BinOp (Mult, n, size, uintType)) mem
  | Some _, _ -> failwith "Error: arguments of realloc are not given"

let model_scanf mode spec cg pid expressions mem =
  match expressions with
  | [] -> mem
  | _ :: rest ->
      List.fold_left
        (fun mem -> function
          | AddrOf lv ->
              update mode spec cg (eval_lv spec pid lv mem) Val.itv_top mem
          | _ -> mem)
        mem rest

let model_strdup mode spec cg node pid lvo expressions mem =
  match (lvo, expressions) with
  | Some lv, str :: _ ->
      let site = Loc.of_allocsite (Allocsite.allocsite_of_node node) in
      let source = eval spec pid str mem in
      let size = ArrayBlk.sizeof (Val.array_of_val source) in
      let null = null_of mem source in
      let sources = ArrayBlk.pow_loc_of_array (Val.array_of_val source) in
      let array = ArrayBlk.make site Itv.zero (Itv.minus size Itv.zero) in
      let locations = PowLoc.singleton site in
      let v = Val.join (Val.of_array array) (Val.of_pow_loc locations) in
      let mem = update mode spec cg (eval_lv spec pid lv mem) v mem in
      let mem = update mode spec cg locations (Mem.lookup sources mem) mem in
      update_info mode spec cg ~offset:Itv.zero locations
        (CellInfo.of_null null) mem
  | _ -> mem

let model_input mode spec cg pid lvo mem =
  match lvo with
  | None -> mem
  | Some lv ->
      let site = Allocsite.allocsite_of_ext None in
      let v = Val.external_value site in
      let locations = alloc_loc site in
      let mem = update mode spec cg (eval_lv spec pid lv mem) v mem in
      update mode spec cg locations Val.itv_top mem

let model_assign mode spec cg pid lvo expressions mem =
  match (lvo, expressions) with
  | Some lv, e :: _ -> assign mode spec cg pid lv e mem
  | _ -> mem

let model_strlen mode spec cg pid lvo expressions mem =
  match (lvo, expressions) with
  | Some lv, str :: _ ->
      let null = null_of mem (eval spec pid str mem) in
      let v = Val.of_itv (Itv.meet Itv.nat null) in
      update mode spec cg (eval_lv spec pid lv mem) v mem
  | _ -> mem

let model_fgets mode spec cg pid lvo expressions mem =
  match expressions with
  | buf :: size :: _ ->
      let size = Val.itv_of_val (eval spec pid size mem) in
      let buffer = eval spec pid buf mem in
      let elements = ArrayBlk.pow_loc_of_array (Val.array_of_val buffer) in
      let mem = update mode spec cg elements Val.itv_top mem in
      set_null mode spec cg buffer (Itv.join Itv.zero size) mem
  | _ -> mem

let model_sprintf mode spec cg pid lvo expressions mem =
  match expressions with
  | [ buf; str ] -> (
      let source = eval spec pid str mem in
      let sources = ArrayBlk.pow_loc_of_array (Val.array_of_val source) in
      let null = null_of mem source in
      let buffer = eval spec pid buf mem in
      let elements = ArrayBlk.pow_loc_of_array (Val.array_of_val buffer) in
      (* Reads and the return destination use the input memory; the writes
         compose over the updated one. *)
      let original = mem in
      let mem =
        update mode spec cg elements (Mem.lookup sources original) mem
      in
      let mem = set_null mode spec cg buffer null mem in
      match lvo with
      | None -> mem
      | Some lv ->
          update mode spec cg
            (eval_lv spec pid lv original)
            (Val.of_itv null) mem)
  | _ -> (
      match lvo with
      | None -> mem
      | Some lv ->
          update mode spec cg (eval_lv spec pid lv mem) (Val.of_itv Itv.nat) mem
      )

let sparrow_arg mode spec cg pid expressions mem =
  match expressions with
  | Lval argc :: Lval argv :: _ ->
      let argv_site = ext_site "argv" in
      let argv_value = Val.of_array (ArrayBlk.input argv_site) in
      let arg_site = ext_site "arg" in
      let arg_value = Val.of_array (ArrayBlk.input arg_site) in
      let original = mem in
      let mem =
        update mode spec cg
          (eval_lv spec pid argc original)
          (Val.of_itv Itv.pos) mem
      in
      let mem =
        update mode spec cg (eval_lv spec pid argv original) argv_value mem
      in
      let mem = update mode spec cg (alloc_loc argv_site) arg_value mem in
      update mode spec cg (alloc_loc arg_site) (Val.of_itv Itv.top) mem
  | _ -> mem

let sparrow_opt mode spec cg pid expressions mem =
  match expressions with
  | Lval optind :: Lval optarg :: _ ->
      let site = ext_site "arg" in
      let v = Val.of_array (ArrayBlk.input site) in
      let original = mem in
      let mem =
        update mode spec cg
          (eval_lv spec pid optind original)
          (Val.of_itv Itv.nat) mem
      in
      let mem = update mode spec cg (eval_lv spec pid optarg original) v mem in
      update mode spec cg (alloc_loc site) (Val.of_itv Itv.top) mem
  | _ -> mem

let model_unknown mode spec cg pid lvo f mem =
  match lvo with
  | None -> mem
  | Some lv ->
      if isArithmeticType (unrollTypeDeep (typeOfLval lv)) then
        let v =
          Val.of_itv
            (if CilHelper.is_unsigned (unrollTypeDeep (typeOfLval lv)) then
               Itv.nat
             else Itv.top)
        in
        update mode spec cg (eval_lv spec pid lv mem) v mem
      else
        let site = ext_site (SourceName.of_varinfo f) in
        let v = Val.of_array (ArrayBlk.extern site) in
        let locations = alloc_loc site in
        let mem = update mode spec cg (eval_lv spec pid lv mem) v mem in
        update mode spec cg locations Val.itv_top mem

let model_memcpy mode spec cg pid lvo expressions mem =
  match (lvo, expressions) with
  | Some lv, dst :: src :: _ ->
      let source = eval spec pid src mem in
      let destination = eval spec pid dst mem in
      let sources = ArrayBlk.pow_loc_of_array (Val.array_of_val source) in
      let destinations =
        ArrayBlk.pow_loc_of_array (Val.array_of_val destination)
      in
      let original = mem in
      let mem =
        update mode spec cg destinations (Mem.lookup sources original) mem
      in
      update mode spec cg (eval_lv spec pid lv original) destination mem
  | _ -> mem

(* A fresh [struct passwd] whose [pw_name] points to an input string. *)
let model_getpwent mode spec cg node pid lvo f mem =
  match (lvo, f.vtype) with
  | Some lv, TFun (TPtr (TComp (comp, _), _), _, _, _) ->
      let locations = eval_lv spec pid lv mem in
      let v =
        Val.cast voidPtrType (typeOfLval lv)
          (array_alloc spec node (SizeOf (TComp (comp, []))) mem)
      in
      let field = List.find (fun f -> f.fname = "pw_name") comp.cfields in
      let fields = PowLoc.append_field (cells_of_val v) field in
      let site = ext_site "getpwent.pw_name" in
      let external_value = Val.of_array (ArrayBlk.input site) in
      let elements = alloc_loc site in
      let mem = update mode spec cg locations v mem in
      let mem = update mode spec cg fields external_value mem in
      update mode spec cg elements Val.itv_top mem
  | _ -> mem

(* strcpy if not [plus], strcat if [plus]: the destination's null position *)
let model_string_copy plus mode spec cg pid expressions mem =
  match expressions with
  | [ dst; src ] ->
      let source = eval spec pid src mem in
      let destination = eval spec pid dst mem in
      let null = null_of mem source in
      let null =
        if plus then Itv.plus (null_of mem destination) null else null
      in
      set_null mode spec cg destination null mem
  | _ -> mem

let model_strncpy mode spec cg pid expressions mem =
  match expressions with
  | dst :: _ :: size :: _ ->
      let destination = eval spec pid dst mem in
      let size = Val.itv_of_val (eval spec pid size mem) in
      let null = Itv.join Itv.zero (Itv.minus size Itv.one) in
      set_null mode spec cg destination null mem
  | _ -> mem

let model_strchr mode spec cg pid lvo expressions mem =
  match (lvo, expressions) with
  | Some lv, str :: _ ->
      let pointer = eval spec pid str mem in
      let null = null_of mem pointer in
      let v =
        Val.of_array (ArrayBlk.plus_offset (Val.array_of_val pointer) null)
      in
      update mode spec cg (eval_lv spec pid lv mem) v mem
  | _ -> mem

let sparrow_array_init mode spec cg node pid expressions mem =
  match expressions with
  | arr :: (Const (CInt _) :: _ as rest) ->
      let locations =
        ArrayBlk.pow_loc_of_array (Val.array_of_val (eval spec pid arr mem))
      in
      let v =
        List.fold_left
          (fun acc e -> Val.join (eval spec pid e mem) acc)
          Val.bot rest
      in
      update mode spec cg locations v mem
  | arr :: (Const (CStr _) :: _ as rest) ->
      let locations =
        ArrayBlk.pow_loc_of_array (Val.array_of_val (eval spec pid arr mem))
      in
      let v =
        List.fold_left
          (fun acc -> function
            | Const (CStr (s, _)) -> Val.join (string_alloc node s) acc
            | _ -> acc)
          Val.bot rest
      in
      update mode spec cg locations v mem
  | [] | [ _ ] -> failwith "nth"
  | _ -> mem

(* ************************************* *
 * Library functions described by ApiSem *
 * ************************************* *)

let eval_src kind pid mem e =
  match kind with
  | ApiSem.Value -> eval Spec.empty pid e mem
  | ApiSem.Array ->
      Mem.lookup (Val.all_loc_of_val (eval Spec.empty pid e mem)) mem

(* The values of the arguments whose type [select] picks, left to right. *)
let collect_values select pid mem expressions types =
  let rec collect acc expressions types =
    match (expressions, types) with
    | [], _ | _, [] -> List.rev acc
    | e :: expressions, kind :: types -> (
        match select kind with
        | None -> collect acc expressions types
        | Some (ApiSem.Fixed, kind) ->
            let v = eval_src kind pid mem e in
            collect (v :: acc) expressions types
        | Some (ApiSem.Variable, kind) ->
            if types <> [] then
              failwith
                "itvSem.ml : API encoding error (Varg not at the last position)"
            else
              List.rev_append acc
                (List.map (eval_src kind pid mem) (e :: expressions)))
  in
  collect [] expressions types

let join_values vs = List.fold_left Val.join Val.bot vs

let va_source types =
  List.exists
    (function ApiSem.Src (ApiSem.Variable, _, _) -> true | _ -> false)
    types

let process_dst mode spec cg pid sources mem e =
  let source = join_values sources in
  let locations = Val.all_loc_of_val (eval Spec.empty pid e mem) in
  update mode spec cg locations source mem

let process_buf mode spec cg node pid mem e =
  let locations = Val.all_loc_of_val (eval Spec.empty pid e mem) in
  let v = Val.external_value (Allocsite.allocsite_of_node node) in
  update mode spec cg locations v mem

let process_struct_ptr mode spec cg node pid mem e =
  let locations = Val.all_loc_of_val (eval Spec.empty pid e mem) in
  let v = Val.external_value (Allocsite.allocsite_of_node node) in
  let external_locations = Val.all_loc_of_val v in
  let mem = update mode spec cg locations v mem in
  update mode spec cg external_locations v mem

let rec process_args mode spec cg node pid expressions types sources mem =
  let has_source = va_source types || sources <> [] in
  match (expressions, types) with
  | [], _ | _, [] -> mem
  | _, [ ApiSem.Dst (ApiSem.Variable, _) ] ->
      assert has_source;
      List.fold_left (process_dst mode spec cg pid sources) mem expressions
  | _, ApiSem.Dst (ApiSem.Variable, _) :: _ ->
      failwith "API encoding error (Varg not at the last position)"
  | e :: rest, ApiSem.Dst (ApiSem.Fixed, _) :: types ->
      assert has_source;
      let mem = process_dst mode spec cg pid sources mem e in
      process_args mode spec cg node pid rest types sources mem
  | _, [ ApiSem.Buf (ApiSem.Variable, _) ] ->
      List.fold_left (process_buf mode spec cg node pid) mem expressions
  | _, ApiSem.Buf (ApiSem.Variable, _) :: _ ->
      failwith "API encoding error (Varg not at the last position)"
  | e :: rest, ApiSem.Buf (ApiSem.Fixed, _) :: types ->
      let mem = process_buf mode spec cg node pid mem e in
      process_args mode spec cg node pid rest types sources mem
  | e :: rest, ApiSem.StructPtr :: types ->
      let mem = process_struct_ptr mode spec cg node pid mem e in
      process_args mode spec cg node pid rest types sources mem
  | _ :: rest, (ApiSem.Src _ | ApiSem.Size | ApiSem.Skip) :: types ->
      process_args mode spec cg node pid rest types sources mem

(* A fresh block whose contents are [initial]; returns the memory and a
   pointer to the block. *)
let gen_block mode spec cg node initial mem =
  let site = Allocsite.allocsite_of_node node in
  let v =
    Val.of_array (ArrayBlk.make (Loc.of_allocsite site) (Itv.of_int 0) Itv.top)
  in
  let mem = update mode spec cg (alloc_loc site) initial mem in
  (mem, v)

let produce_ret mode spec cg node kind va sources destinations buffers sizes mem
    =
  let one values =
    assert (List.length values = 1);
    (mem, List.hd values)
  in
  match kind with
  | ApiSem.Const | ApiSem.TaintInput -> (mem, Val.itv_top)
  | ApiSem.SrcArg -> one sources
  | ApiSem.SizeArg -> one sizes
  | ApiSem.DstArg -> one destinations
  | ApiSem.BufArg -> one buffers
  | ApiSem.TopWithSrcTaint ->
      assert (va || sources <> []);
      (mem, Val.itv_top)
  | ApiSem.AllocConst | ApiSem.AllocBuf ->
      gen_block mode spec cg node Val.itv_top mem
  | ApiSem.AllocDst ->
      assert (va || sources <> []);
      gen_block mode spec cg node (join_values sources) mem
  | ApiSem.AllocStruct ->
      let v = Val.external_value (Allocsite.allocsite_of_node node) in
      gen_block mode spec cg node v mem

let handle_api mode spec cg node pid lvo expressions mem api =
  let types = api.ApiSem.arg_typs in
  let collect select = collect_values select pid mem expressions types in
  let sources =
    collect (function ApiSem.Src (v, k, _) -> Some (v, k) | _ -> None)
  in
  let destinations =
    collect (function ApiSem.Dst (v, _) -> Some (v, ApiSem.Value) | _ -> None)
  in
  let buffers =
    collect (function ApiSem.Buf (v, _) -> Some (v, ApiSem.Value) | _ -> None)
  in
  let sizes =
    collect (function
      | ApiSem.Size -> Some (ApiSem.Fixed, ApiSem.Value)
      | _ -> None)
  in
  let mem = process_args mode spec cg node pid expressions types sources mem in
  match lvo with
  | None -> mem
  | Some lv ->
      let mem, v =
        produce_ret mode spec cg node api.ApiSem.ret_typ (va_source types)
          sources destinations buffers sizes mem
      in
      update mode spec cg (eval_lv spec pid lv mem) v mem

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
  if not !Options.scaffold then model_unknown mode spec cg pid lvo f mem
  else
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
    | "strchr" | "strrchr" -> model_strchr mode spec cg pid lvo expressions mem
    | s when List.mem s mem_alloc_libs ->
        model_alloc_one mode spec cg pid lvo f mem
    | s when ApiSem.ApiMap.mem s ApiSem.api_map ->
        handle_api mode spec cg node pid lvo expressions mem
          (ApiSem.ApiMap.find s ApiSem.api_map)
    | _ -> model_unknown mode spec cg pid lvo f mem

let undefined_call mode spec cg node pid lvo f expressions mem location =
  let name = SourceName.of_varinfo f in
  let key = CilHelper.s_location location ^ ":" ^ name in
  if BatSet.mem key spec.Spec.unsound_lib then mem
  else (
    (* The arguments are evaluated even when unused, for their failures. *)
    ignore (eval_list spec pid expressions mem);
    match name with
    | "sparrow_arg" -> sparrow_arg mode spec cg pid expressions mem
    | "sparrow_opt" -> sparrow_opt mode spec cg pid expressions mem
    | "sparrow_print" ->
        (if !Options.verbose >= 1 then
           let vs = eval_list spec pid expressions mem in
           let description =
             Vocab.string_of_list CilHelper.s_exp expressions
             ^ " @ "
             ^ CilHelper.s_location location
           in
           prerr_endline
             ("sparrow_print (" ^ description ^ ") : "
             ^ Vocab.string_of_list Val.to_string vs));
        mem
    | "sparrow_dump" ->
        if !Options.verbose >= 1 then
          prerr_endline
            ("sparrow_dump ("
            ^ CilHelper.s_location location
            ^ ") : \n" ^ Mem.to_string mem);
        mem
    | "sparrow_assume" -> (
        match expressions with
        | e :: _ -> prune mode spec cg pid e mem
        | [] -> failwith "hd")
    | "sparrow_array_init" ->
        sparrow_array_init mode spec cg node pid expressions mem
    | "strlen" -> model_strlen mode spec cg pid lvo expressions mem
    | "realloc" -> model_realloc mode spec cg node lvo expressions mem
    | "calloc" -> model_calloc mode spec cg node lvo expressions mem
    | _ -> scaffolded_functions mode spec cg node pid lvo f expressions mem)
