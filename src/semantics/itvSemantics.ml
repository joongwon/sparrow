(** The interval transfer functions for expressions and commands.

    Evaluation order is observable (lookups may fail and some evaluations are
    kept only for their exceptions), so keep the order of the existing code when
    editing. *)

open Sparrow_cil
open BasicDom
open ItvDom
module Spec = Spec.Make (Mem)

(* ********************** *
 * Abstract memory access *
 * ********************** *)

let can_strong_update mode spec callgraph locs =
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
  Val.of_itv
    (try Itv.of_int (CilHelper.byteSizeOf (typ ())) with _ -> Itv.pos)

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

let rec resolve_offset spec pid v os mem =
  match os with
  | NoOffset ->
      PowLoc.join (Val.pow_loc_of_val v)
        (ArrayBlk.pow_loc_of_array (Val.array_of_val v))
  | Field (f, rest) ->
      let loaded = Mem.lookup (Val.pow_loc_of_val v) mem in
      let locs =
        PowLoc.join
          (StructBlk.append_field (Val.struct_of_val v) f)
          (PowLoc.join
             (ArrayBlk.append_field (Val.array_of_val v) f)
             (StructBlk.append_field (Val.struct_of_val loaded) f))
      in
      resolve_offset spec pid (Val.of_pow_loc locs) rest mem
  | Index (e, rest) ->
      let loaded = Mem.lookup (Val.pow_loc_of_val v) mem in
      (* The index value is unused, but its evaluation may fail. *)
      ignore (eval spec pid e mem);
      resolve_offset spec pid
        (Val.of_pow_loc (ArrayBlk.pow_loc_of_array (Val.array_of_val loaded)))
        rest mem

and eval_lv spec pid (host, offset) mem =
  let v =
    match host with
    | Var vi -> Val.of_pow_loc (PowLoc.singleton (var_of_varinfo vi pid))
    | Mem e -> eval spec pid e mem
  in
  PowLoc.remove Loc.null (resolve_offset spec pid v offset mem)

and eval spec pid e mem =
  match e with
  | Const c -> eval_const c
  | Lval lv | StartOf lv -> Mem.lookup (eval_lv spec pid lv mem) mem
  | SizeOf t -> size_of (fun () -> t)
  | SizeOfE e -> size_of (fun () -> typeOf e)
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
        let v' =
          Val.make
            ( i,
              p,
              Val.array_of_val v,
              Val.struct_of_val v,
              Val.pow_proc_of_val v )
        in
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

(* ******************************* *
 * Semantic functions for commands *
 * ******************************* *)

let assign mode spec callgraph pid lv e mem =
  let v = eval spec pid e mem in
  let locs = eval_lv spec pid lv mem in
  update mode spec callgraph locs v mem

let array_alloc spec node e is_static mem =
  let size = Val.itv_of_val (eval spec (Node.get_pid node) e mem) in
  (* A fresh zero per allocation: sharing Itv.zero here changes physical
     identities even though domain equality holds. *)
  let array =
    ArrayBlk.make
      (Allocsite.allocsite_of_node node)
      (Itv.of_int 0) size ArrayBlk.Stride.one Itv.nat
  in
  Val.join
    (Val.of_pow_loc
       (if is_static then PowLoc.bot else PowLoc.singleton Loc.null))
    (Val.of_array array)

let struct_alloc locs comp = Val.of_struct (StructBlk.make locs comp)

let string_alloc node s =
  Val.of_array
    (ArrayBlk.make
       (Allocsite.allocsite_of_string node)
       (Itv.of_int 0)
       (Itv.of_int (String.length s + 1))
       ArrayBlk.Stride.one
       (Itv.of_int (String.length s)))

let array_assign mode spec callgraph node lv e is_static mem =
  let v = array_alloc spec node e is_static mem in
  let locs = eval_lv spec (Node.get_pid node) lv mem in
  update mode spec callgraph locs v mem

let struct_assign mode spec callgraph pid lv comp mem =
  let locs = eval_lv spec pid lv mem in
  update mode spec callgraph locs (struct_alloc locs comp) mem

let string_assign mode spec callgraph node lv s mem =
  let str_loc =
    PowLoc.singleton (Loc.of_allocsite (Allocsite.allocsite_of_string node))
  in
  let v = string_alloc node s in
  let locs = eval_lv spec (Node.get_pid node) lv mem in
  let mem = update mode spec callgraph locs v mem in
  update mode spec callgraph str_loc (Val.of_itv Itv.nat) mem

let function_assign mode spec callgraph pid lv target mem =
  let v = Val.of_pow_proc (PowProc.singleton target) in
  let locs = eval_lv spec pid lv mem in
  update mode spec callgraph locs v mem

let return_store spec callgraph pid expression mem =
  match expression with
  | None -> mem
  | Some e ->
      let v = eval spec pid e mem in
      let locs = PowLoc.singleton (Loc.return_var pid (typeOf e)) in
      update AbsSem.Weak spec callgraph locs v mem

let assume mode spec callgraph pid e mem =
  ignore (eval spec pid e mem);
  prune mode spec callgraph pid e mem

(* [formals] gives the formal locations of a procedure. *)
let formal_groups formals targets =
  PowProc.fold
    (fun target groups -> BatSet.add (formals target) groups)
    targets BatSet.empty

(* Bind the arguments to every group of formals of matching arity; weakly if
   there are several. *)
let bind_args mode spec callgraph groups vs mem =
  let groups =
    BatSet.filter (fun locs -> List.length locs = List.length vs) groups
  in
  let mode = if BatSet.cardinal groups > 1 then AbsSem.Weak else mode in
  BatSet.fold
    (fun locations mem ->
      Vocab.list_fold2
        (fun loc v mem ->
          update mode spec callgraph (PowLoc.singleton loc) v mem)
        locations vs mem)
    groups mem

let call_return_locs targets lv =
  PowProc.fold
    (fun target locs -> PowLoc.add (Loc.return_var target (typeOfLval lv)) locs)
    targets PowLoc.empty

(* The destination is evaluated in the memory before formals are bound. *)
let user_call mode spec callgraph formals pid lvo f arguments mem dump =
  let targets = Val.pow_proc_of_val (eval spec pid f mem) in
  if PowProc.eq targets PowProc.bot then (mem, dump)
  else
    let groups = formal_groups formals targets in
    let vs = eval_list spec pid arguments mem in
    let dump =
      match lvo with
      | None -> dump
      | Some lv ->
          let returns = call_return_locs targets lv in
          ignore (Mem.lookup returns mem);
          PowProc.fold
            (fun target dump ->
              Dump.weak_add target (eval_lv spec pid lv mem) dump)
            targets dump
    in
    (bind_args mode spec callgraph groups vs mem, dump)

let call_return spec callgraph pid lv f mem =
  let targets = Val.pow_proc_of_val (eval spec pid f mem) in
  let returns = call_return_locs targets lv in
  update AbsSem.Weak spec callgraph (eval_lv spec pid lv mem)
    (Mem.lookup returns mem) mem
