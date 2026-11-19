(***********************************************************************)
(*                                                                     *)
(* Copyright (c) 2007-present.                                         *)
(* Programming Research Laboratory (ROPAS), Seoul National University. *)
(* All rights reserved.                                                *)
(*                                                                     *)
(* This software is distributed under the term of the BSD license.     *)
(* See the LICENSE file for details.                                   *)
(*                                                                     *)
(***********************************************************************)
(** Semantics of interval analysis.

    Evaluation order is observable (lookups may fail and some evaluations are
    kept only for their exceptions), so keep the order of the existing code when
    editing. *)

open Sparrow_cil
open BasicDom
open ItvDom
module Dom = ItvDom.Mem
module Spec = Spec.Make (Dom)

(* ********************** *
 * Abstract memory access *
 * ********************** *)

(* A cell of array type holds all the elements of the array. *)
let is_array_cell loc =
  match Loc.typ loc with Some t -> isArrayType (unrollType t) | None -> false

(* One location that stands for one variable instance. *)
let single_location mode spec callgraph locs =
  spec.Spec.unsound_update
  ||
  match mode with
  | AbsSem.Weak -> false
  | AbsSem.Strong ->
      PowLoc.cardinal locs = 1
      &&
      let loc = PowLoc.choose locs in
      Loc.is_gvar loc
      || Loc.is_lvar loc
         && ((not (CallGraph.is_rec callgraph (Loc.get_proc loc)))
            || FrameLocal.mem loc)

(* A value update is strong only for a single location holding one value; an
   array's cell holds all its elements. *)
let can_strong_update mode spec callgraph locs =
  single_location mode spec callgraph locs
  && not (PowLoc.exists is_array_cell locs)

(* Info describes the array object a cell holds. It is set strongly when the
   cell holds exactly one array object (a single location of a one-dimensional
   array type) and the pointer is at its start; otherwise it is joined. *)
let can_strong_update_info mode spec callgraph locs offset =
  single_location mode spec callgraph locs
  && Itv.eq offset Itv.zero
  && PowLoc.for_all
       (fun loc ->
         match Option.map unrollTypeDeep (Loc.typ loc) with
         | Some (TArray (element, _, _)) -> not (isArrayType element)
         | _ -> false)
       locs

let update_info mode spec callgraph ~offset locs info mem =
  if can_strong_update_info mode spec callgraph locs offset then
    Mem.strong_update_info locs info mem
  else Mem.weak_update_info locs info mem

let update mode spec callgraph locs v mem =
  if can_strong_update mode spec callgraph locs then
    Mem.strong_update locs v mem
  else Mem.weak_update locs v mem

(* ********************************** *
 * Semantic functions for expressions *
 * ********************************** *)

let var_of_varinfo vi pid =
  if vi.vglob then Loc.of_gvar vi.vname vi.vtype
  else Loc.of_lvar pid vi.vname vi.vtype

let eval_const = function
  | CInt (n, _, _) ->
      Val.of_itv (try Itv.of_int (Cilint.to_int n) with _ -> Itv.top)
  | CChr c -> Val.of_itv (Itv.of_int (int_of_char c))
  | CReal (f, _, _) ->
      Val.of_itv (Itv.of_ints (int_of_float (floor f)) (int_of_float (ceil f)))
  | CStr _ | CWStr _ | CEnum _ -> Val.of_itv Itv.top

(* [typ] is a thunk so that a failure computing the type (e.g. [typeOf]) is
   caught as well. *)
let size_of typ =
  Val.of_itv (try Itv.of_int (CilHelper.byteSizeOf typ) with _ -> Itv.pos)

let eval_uop spec op v =
  if Val.eq v Val.bot then Val.bot
  else
    let i = Val.itv_of_val v in
    Val.of_itv
      (match op with
      | Neg -> Itv.minus Itv.zero i
      | LNot -> Itv.l_not i
      | BNot ->
          if spec.Spec.unsound_bitwise then Itv.bot else Itv.unknown_unary i)

let eval_bop spec op a b =
  let ints op = Val.of_itv (op (Val.itv_of_val a) (Val.itv_of_val b)) in
  let pointer op =
    Val.join
      (Val.of_pow_loc (Val.pow_loc_of_val a))
      (Val.of_array (op (Val.array_of_val a) (Val.itv_of_val b)))
  in
  match op with
  | PlusA -> ints Itv.plus
  | MinusA -> ints Itv.minus
  | Mult -> ints Itv.times
  | Div -> ints Itv.divide
  | PlusPI | IndexPI -> pointer ArrayBlk.plus_offset
  | MinusPI -> pointer ArrayBlk.minus_offset
  | MinusPP ->
      Val.of_itv
        (Itv.minus
           (ArrayBlk.offsetof (Val.array_of_val a))
           (ArrayBlk.offsetof (Val.array_of_val b)))
  | Lt -> ints Itv.lt_itv
  | Gt -> ints Itv.gt_itv
  | Le -> ints Itv.le_itv
  | Ge -> ints Itv.ge_itv
  | Eq -> ints Itv.eq_itv
  | Ne -> ints Itv.ne_itv
  | LAnd -> ints Itv.l_and
  | LOr -> ints Itv.l_or
  | Shiftlt -> if spec.Spec.unsound_bitwise then a else ints Itv.l_shift
  | Shiftrt | Mod | BAnd | BXor | BOr ->
      if spec.Spec.unsound_bitwise then a else ints Itv.unknown_binary

(* The cells a pointer value points to: its locations and its arrays. *)
let cells_of_val v =
  PowLoc.join (Val.pow_loc_of_val v)
    (ArrayBlk.pow_loc_of_array (Val.array_of_val v))

(* The number of elements of an array type; top when unknown. *)
let array_length typ =
  match unrollTypeDeep typ with
  | TArray (_, len, _) -> ( try Itv.of_int (lenOfArray len) with _ -> Itv.top)
  | _ -> Itv.top

(* A pointer to the first element of each array object in [cells]. *)
let array_start cells typ =
  let size = array_length typ in
  Val.of_array
    (PowLoc.fold
       (fun cell -> ArrayBlk.join (ArrayBlk.make cell (Itv.of_int 0) size))
       cells ArrayBlk.bot)

let is_composite typ = match unrollType typ with TComp _ -> true | _ -> false

(* An object of composite type has no value of its own: reading it reads its
   fields (an array's elements are its one cell). *)
let rec read_object typ cells mem =
  match unrollType typ with
  | TComp (comp, _) ->
      List.iter
        (fun f -> read_object f.ftype (PowLoc.append_field cells f) mem)
        comp.cfields
  | TArray (t, _, _) when is_composite t -> read_object t cells mem
  | _ -> ignore (Mem.lookup cells mem)

(* Fields and elements live in place: a field is a cell named from its
   parent, and all elements of an array are the array's cell. *)
let rec resolve_offset spec pid cells os mem =
  match os with
  | NoOffset -> cells
  | Field (f, rest) ->
      resolve_offset spec pid (PowLoc.append_field cells f) rest mem
  | Index (e, rest) ->
      (* The index value is unused, but its evaluation may fail. *)
      ignore (eval spec pid e mem);
      resolve_offset spec pid cells rest mem

and eval_lv spec pid (host, offset) mem =
  let cells =
    match host with
    | Var vi -> PowLoc.singleton (var_of_varinfo vi pid)
    | Mem e -> cells_of_val (eval spec pid e mem)
  in
  PowLoc.remove Loc.null (resolve_offset spec pid cells offset mem)

and eval spec pid e mem =
  match e with
  | Const c -> eval_const c
  | Lval lv ->
      let cells = eval_lv spec pid lv mem in
      if is_composite (typeOfLval lv) then (
        read_object (typeOfLval lv) cells mem;
        Val.bot)
      else Mem.lookup cells mem
  | StartOf lv -> array_start (eval_lv spec pid lv mem) (typeOfLval lv)
  | SizeOf t -> size_of t
  | SizeOfE e -> size_of (typeOf e)
  | SizeOfStr s -> Val.of_itv (Itv.of_int (String.length s + 1))
  | AlignOf t -> Val.of_itv (Itv.of_int (alignOf_int t))
  | AlignOfE _ | Real _ | Imag _ -> Val.of_itv Itv.top
  | UnOp (op, e, _) -> eval_uop spec op (eval spec pid e mem)
  | BinOp (op, a, b, _) ->
      (* The right operand is evaluated first. *)
      let b = eval spec pid b mem in
      let a = eval spec pid a mem in
      eval_bop spec op a b
  | Question (c, a, b, _) ->
      let i = Val.itv_of_val (eval spec pid c mem) in
      if Itv.is_bot i then Val.bot
      else if Itv.eq Itv.zero i then eval spec pid b mem
      else if Itv.le Itv.zero i then
        let b = eval spec pid b mem in
        let a = eval spec pid a mem in
        Val.join a b
      else eval spec pid a mem
  | CastE (_, t, e) -> (
      let v = eval spec pid e mem in
      try Val.cast (typeOf e) t v with _ -> v)
  | AddrOf lv -> Val.of_pow_loc (eval_lv spec pid lv mem)
  | AddrOfLabel _ ->
      invalid_arg
        "itvSem.ml:eval AddrOfLabel mem. Analysis does not support label \
         values."

let eval_list spec pid exps mem = List.map (fun e -> eval spec pid e mem) exps

(* ******* *
 * Pruning *
 * ******* *)

let rec prune_simple mode spec callgraph pid cond mem =
  match cond with
  | BinOp (((Lt | Gt | Le | Ge | Eq | Ne) as op), Lval x, e, _) ->
      let locs = eval_lv spec pid x mem in
      if PowLoc.cardinal locs = 1 then
        let v = Mem.lookup locs mem in
        let rhs = Val.itv_of_val (eval spec pid e mem) in
        let i = Itv.prune op (Val.itv_of_val v) rhs in
        let p =
          let ptrs = Val.pow_loc_of_val v in
          match op with
          | Eq when isZero e -> PowLoc.singleton Loc.null
          | Ne when isZero e -> PowLoc.remove Loc.null ptrs
          | _ -> ptrs
        in
        let v' = Val.make (i, p, Val.array_of_val v, Val.pow_proc_of_val v) in
        update mode spec callgraph locs v' mem
      else mem
  | BinOp (((LAnd | LOr) as op), e1, e2, _) ->
      let m1 = prune_simple mode spec callgraph pid e1 mem in
      let m2 = prune_simple mode spec callgraph pid e2 mem in
      if op = LAnd then Mem.meet m1 m2 else Mem.join m1 m2
  | UnOp (LNot, Lval x, _) -> prune_lvalue mode spec callgraph pid x mem true
  | Lval x -> prune_lvalue mode spec callgraph pid x mem false
  | _ -> mem

and prune_lvalue mode spec callgraph pid x mem is_zero =
  let locs = eval_lv spec pid x mem in
  if PowLoc.cardinal locs = 1 then
    let v = Mem.lookup locs mem in
    let i = Val.itv_of_val v in
    let i =
      if is_zero then Itv.meet i Itv.zero
      else Itv.join (Itv.meet i Itv.pos) (Itv.meet i Itv.neg)
    in
    update mode spec callgraph locs (Val.modify_itv i v) mem
  else mem

let prune mode spec callgraph pid cond mem =
  match CilHelper.make_cond_simple cond with
  | None -> mem
  | Some cond -> prune_simple mode spec callgraph pid cond mem

(* ********** *
 * Allocation *
 * ********** *)

(* A block of [e] elements of the destination's pointee type, or null. *)
let array_alloc spec node e mem =
  let size = Val.itv_of_val (eval spec (Node.get_pid node) e mem) in
  (* A fresh zero per allocation: sharing Itv.zero here changes physical
     identities even though domain equality holds. *)
  let array =
    ArrayBlk.make
      (Loc.of_allocsite (Allocsite.allocsite_of_node node))
      (Itv.of_int 0) size
  in
  Val.join (Val.of_pow_loc (PowLoc.singleton Loc.null)) (Val.of_array array)

let string_alloc node s =
  Val.of_array
    (ArrayBlk.make
       (Loc.of_allocsite (Allocsite.allocsite_of_string node))
       (Itv.of_int 0)
       (Itv.of_int (String.length s + 1)))

let array_assign mode spec callgraph node lv e mem =
  let v = array_alloc spec node e mem in
  let locs = eval_lv spec (Node.get_pid node) lv mem in
  update mode spec callgraph locs v mem

(* ************* *
 * Null position *
 * ************* *)

(* The null position seen from a pointer: each array's null position minus
   the pointer's offset; unknown (bot) is [0, +oo]. *)
let null_of mem v =
  ArrayBlk.foldi
    (fun cell info acc ->
      let null = (Mem.lookup_info (PowLoc.singleton cell) mem).null_pos in
      let relative =
        if Itv.is_bot null then Itv.nat
        else Itv.minus null info.ArrayBlk.ArrInfo.offset
      in
      Itv.join acc relative)
    (Val.array_of_val v) Itv.bot

(* Set the null position seen from a pointer to [null]. *)
let set_null mode spec callgraph v null mem =
  ArrayBlk.foldi
    (fun cell info mem ->
      let offset = info.ArrayBlk.ArrInfo.offset in
      update_info mode spec callgraph ~offset (PowLoc.singleton cell)
        (CellInfo.of_null (Itv.plus null offset))
        mem)
    (Val.array_of_val v) mem

(* ****************** *
 * Composite objects *
 * ****************** *)

(* Copy an object of type [typ] from the cells [src] to [dst], field by
   field; an array's cell is copied whole, with its info. *)
let rec copy mode spec callgraph typ dst src mem =
  match unrollType typ with
  | TComp (comp, _) ->
      List.fold_left
        (fun mem f ->
          copy mode spec callgraph f.ftype
            (PowLoc.append_field dst f)
            (PowLoc.append_field src f)
            mem)
        mem comp.cfields
  | TArray (t, _, _) when is_composite t ->
      copy mode spec callgraph t dst src mem
  | _ ->
      let mem = update mode spec callgraph dst (Mem.lookup src mem) mem in
      let info = Mem.lookup_info src mem in
      if CellInfo.eq info CellInfo.bot then mem
      else update_info mode spec callgraph ~offset:Itv.zero dst info mem

(* The object an expression of composite type denotes, if it is an lvalue. *)
let composite_source e =
  match e with Lval rv when is_composite (typeOf e) -> Some rv | _ -> None

let assign mode spec callgraph pid lv e mem =
  match composite_source e with
  | Some rv ->
      let src = eval_lv spec pid rv mem in
      let dst = eval_lv spec pid lv mem in
      copy mode spec callgraph (typeOf e) dst src mem
  | None ->
      let v = eval spec pid e mem in
      let locs = eval_lv spec pid lv mem in
      update mode spec callgraph locs v mem

(* An argument: a value, or the cells of an object passed by value. *)
type argument = Value of Val.t | Object of typ * PowLoc.t

let eval_argument spec pid e mem =
  match composite_source e with
  | Some rv -> Object (typeOf e, eval_lv spec pid rv mem)
  | None -> Value (eval spec pid e mem)

(* Bind the arguments to every group of formals of matching arity; weakly if
   there are several. *)
let bind_args mode spec callgraph groups args mem =
  let groups =
    BatSet.filter (fun locs -> List.length locs = List.length args) groups
  in
  let mode = if BatSet.cardinal groups > 1 then AbsSem.Weak else mode in
  BatSet.fold
    (fun locations mem ->
      Vocab.list_fold2
        (fun loc arg mem ->
          let formal = PowLoc.singleton loc in
          match arg with
          | Value v -> update mode spec callgraph formal v mem
          | Object (typ, src) -> copy mode spec callgraph typ formal src mem)
        locations args mem)
    groups mem

let call_return_locs targets lv =
  PowProc.fold
    (fun target locs -> PowLoc.add (Loc.return_var target (typeOfLval lv)) locs)
    targets PowLoc.empty

(* ************************************* *
 * Semantics of undefined library calls *
 * ************************************* *)

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

(* ******************************* *
 * Semantic functions for commands *
 * ******************************* *)

(* Default update option is weak update. *)
let run :
    AbsSem.update_mode ->
    Spec.t ->
    Node.t ->
    Mem.t * Global.t ->
    Mem.t * Global.t =
 fun mode spec node (mem, global) ->
  let pid = Node.get_pid node in
  let icfg = global.Global.icfg and cg = global.Global.callgraph in
  match InterCfg.cmdof icfg node with
  | IntraCfg.Cmd.Cset (lv, e, _) -> (assign mode spec cg pid lv e mem, global)
  | IntraCfg.Cmd.Calloc (lv, e, _) ->
      (array_assign mode spec cg node lv e mem, global)
  | IntraCfg.Cmd.Csalloc (lv, s, _) ->
      let str_loc =
        PowLoc.singleton (Loc.of_allocsite (Allocsite.allocsite_of_string node))
      in
      let v = string_alloc node s in
      let locs = eval_lv spec pid lv mem in
      let mem = update mode spec cg locs v mem in
      let mem = update mode spec cg str_loc (Val.of_itv Itv.nat) mem in
      let mem =
        update_info mode spec cg ~offset:Itv.zero str_loc
          (CellInfo.of_null (Itv.of_int (String.length s)))
          mem
      in
      (mem, global)
  | IntraCfg.Cmd.Cfalloc (lv, fd, _) ->
      let v = Val.of_pow_proc (PowProc.singleton fd.svar.vname) in
      let locs = eval_lv spec pid lv mem in
      (update mode spec cg locs v mem, global)
  | IntraCfg.Cmd.Cassume (e, _) ->
      ignore (eval spec pid e mem);
      (prune mode spec cg pid e mem, global)
  | IntraCfg.Cmd.Ccall (lvo, Lval (Var f, NoOffset), arguments, loc)
    when Global.is_undef f.vname global ->
      (* undefined library functions *)
      (undefined_call mode spec cg node pid lvo f arguments mem loc, global)
  | IntraCfg.Cmd.Ccall (lvo, f, arguments, _) ->
      (* user functions; the destination is evaluated in the memory before
         formals are bound. *)
      let targets = Val.pow_proc_of_val (eval spec pid f mem) in
      if PowProc.eq targets PowProc.bot then (mem, global)
      else
        let formals target =
          List.map
            (fun x -> Loc.of_lvar target x.vname x.vtype)
            (InterCfg.argsof icfg target)
        in
        let groups =
          PowProc.fold
            (fun target groups -> BatSet.add (formals target) groups)
            targets BatSet.empty
        in
        let args = List.map (fun e -> eval_argument spec pid e mem) arguments in
        let dump =
          match lvo with
          | None -> global.Global.dump
          | Some lv ->
              let returns = call_return_locs targets lv in
              ignore (Mem.lookup returns mem);
              PowProc.fold
                (fun target dump ->
                  Dump.weak_add target (eval_lv spec pid lv mem) dump)
                targets global.Global.dump
        in
        (bind_args mode spec cg groups args mem, { global with Global.dump })
  | IntraCfg.Cmd.Creturn (None, _) -> (mem, global)
  | IntraCfg.Cmd.Creturn (Some e, _) ->
      let locs = PowLoc.singleton (Loc.return_var pid (typeOf e)) in
      let mem =
        match composite_source e with
        | Some rv ->
            let src = eval_lv spec pid rv mem in
            copy AbsSem.Weak spec cg (typeOf e) locs src mem
        | None ->
            let v = eval spec pid e mem in
            update AbsSem.Weak spec cg locs v mem
      in
      (mem, global)
  | IntraCfg.Cmd.Cskip when InterCfg.is_returnnode node icfg -> (
      match InterCfg.cmdof icfg (InterCfg.callof node icfg) with
      | IntraCfg.Cmd.Ccall (Some lv, f, _, _) ->
          let targets = Val.pow_proc_of_val (eval spec pid f mem) in
          let returns = call_return_locs targets lv in
          let typ = typeOfLval lv in
          let mem =
            if is_composite typ then
              copy AbsSem.Weak spec cg typ (eval_lv spec pid lv mem) returns mem
            else
              update AbsSem.Weak spec cg (eval_lv spec pid lv mem)
                (Mem.lookup returns mem) mem
          in
          (mem, global)
      | _ -> (mem, global))
  | IntraCfg.Cmd.Cskip -> (mem, global)
  | IntraCfg.Cmd.Casm _ -> (mem, global) (* Not supported *)
  | _ -> invalid_arg "itvSem.ml: run_cmd"

let initial _ = Mem.bot

(* ********************************* *
 * Evaluation for the other analyses *
 * ********************************* *)

(* Some API models deliberately evaluate operands with the default
   Spec.empty. *)
let eval_lv ?(spec = Spec.empty) pid lv mem = eval_lv spec pid lv mem
let eval ?(spec = Spec.empty) pid e mem = eval spec pid e mem

let eval_array_alloc ?(spec = Spec.empty) node e mem =
  array_alloc spec node e mem

let eval_string_alloc node s _mem = string_alloc node s
