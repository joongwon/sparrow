(** The interval transfer as a functor; ItvSem is its direct instance. Syntax is
    an input. Memory, update policy and environment are inputs of the resulting
    computation. The algebra must preserve exceptions and the effects of [let_]
    even when its bound value is unused (notably indices). No whole-command
    evaluator is an operation of this interface. *)

open Sparrow_cil
open BasicDom
open ItvDom
module Spec = Spec.Make (Mem)

type node_binding = {
  node_procedure : Proc.t;
  node_allocation : unit -> Allocsite.t;
  node_string_allocation : unit -> Allocsite.t;
}

let unrelocated_node_metadata node =
  {
    node_procedure = Node.get_pid node;
    node_allocation = (fun () -> Allocsite.allocsite_of_node node);
    node_string_allocation = (fun () -> Allocsite.allocsite_of_string node);
  }

(* A scoped representation adapter: a client that runs this transfer on
   commands under its own names supplies the allocation sites of the node.
   The analysis itself never installs one.  Procedure identity and
   allocation identity are separate metadata slots in Make. *)
let node_metadata_adapter : (Node.t -> node_binding) option ref = ref None

let node_metadata node =
  match !node_metadata_adapter with
  | None -> unrelocated_node_metadata node
  | Some bind -> bind node

let with_node_metadata_adapter bind action =
  let previous = !node_metadata_adapter in
  node_metadata_adapter := Some bind;
  Fun.protect ~finally:(fun () -> node_metadata_adapter := previous) action

type formal_groups = Loc.t list BatSet.t
type variable = { name : string; declared_type : typ; global : bool }

let variable_metadata vi =
  { name = vi.vname; declared_type = vi.vtype; global = vi.vglob }

type _ literal =
  | Value : Val.t -> Val.t literal
  | Interval : Itv.t -> Itv.t literal
  | Bool : bool -> bool literal
  | Int : int -> int literal
  | Text : string -> string literal
  | Description : exp list -> (unit -> string) literal
  | Proc : Proc.t -> Proc.t literal
  | Node : Node.t -> node_binding literal
  | Variable : varinfo -> (Proc.t -> PowLoc.t) literal
  | Field_info : fieldinfo -> fieldinfo literal
  | Type : typ -> (unit -> typ) literal
  | Expression_type : exp -> (unit -> typ) literal
  | Is_zero : exp -> (unit -> bool) literal
  | Constant : constant -> (unit -> Val.t) literal
  | Operator : binop -> binop literal
  | Composite : compinfo -> compinfo literal
  | Lvalue_type_query : lval -> (unit -> typ) literal

(* These are domain/environment operations, not a second expression language.
   Each instance uses precisely the function denoted by [meaning]. *)
type _ primitive =
  | Val_of_itv : (Itv.t -> Val.t) primitive
  | Val_itv : (Val.t -> Itv.t) primitive
  | Val_locs : (Val.t -> PowLoc.t) primitive
  | Val_array : (Val.t -> ArrayBlk.t) primitive
  | Val_struct : (Val.t -> StructBlk.t) primitive
  | Val_of_locs : (PowLoc.t -> Val.t) primitive
  | Val_of_array : (ArrayBlk.t -> Val.t) primitive
  | Val_join : (Val.t -> Val.t -> Val.t) primitive
  | Val_is_bot : (Val.t -> bool) primitive
  | Val_modify_itv : (Itv.t -> Val.t -> Val.t) primitive
  | Itv_is_bot : (Itv.t -> bool) primitive
  | Itv_eq : (Itv.t -> Itv.t -> bool) primitive
  | Itv_le : (Itv.t -> Itv.t -> bool) primitive
  | Itv_join : (Itv.t -> Itv.t -> Itv.t) primitive
  | Itv_meet : (Itv.t -> Itv.t -> Itv.t) primitive
  | Itv_plus : (Itv.t -> Itv.t -> Itv.t) primitive
  | Itv_minus : (Itv.t -> Itv.t -> Itv.t) primitive
  | Itv_times : (Itv.t -> Itv.t -> Itv.t) primitive
  | Itv_divide : (Itv.t -> Itv.t -> Itv.t) primitive
  | Itv_lt : (Itv.t -> Itv.t -> Itv.t) primitive
  | Itv_gt : (Itv.t -> Itv.t -> Itv.t) primitive
  | Itv_le_itv : (Itv.t -> Itv.t -> Itv.t) primitive
  | Itv_ge : (Itv.t -> Itv.t -> Itv.t) primitive
  | Itv_eq_itv : (Itv.t -> Itv.t -> Itv.t) primitive
  | Itv_ne : (Itv.t -> Itv.t -> Itv.t) primitive
  | Itv_and : (Itv.t -> Itv.t -> Itv.t) primitive
  | Itv_or : (Itv.t -> Itv.t -> Itv.t) primitive
  | Itv_shift : (Itv.t -> Itv.t -> Itv.t) primitive
  | Itv_unknown_binary : (Itv.t -> Itv.t -> Itv.t) primitive
  | Itv_not : (Itv.t -> Itv.t) primitive
  | Itv_unknown_unary : (Itv.t -> Itv.t) primitive
  | Itv_prune : (binop -> Itv.t -> Itv.t -> Itv.t) primitive
  | Array_plus : (ArrayBlk.t -> Itv.t -> ArrayBlk.t) primitive
  | Array_minus : (ArrayBlk.t -> Itv.t -> ArrayBlk.t) primitive
  | Array_offset : (ArrayBlk.t -> Itv.t) primitive
  | Array_locs : (ArrayBlk.t -> PowLoc.t) primitive
  | Array_field : (ArrayBlk.t -> fieldinfo -> PowLoc.t) primitive
  | Struct_field : (StructBlk.t -> fieldinfo -> PowLoc.t) primitive
  | Locs_join : (PowLoc.t -> PowLoc.t -> PowLoc.t) primitive
  | Locs_singleton : (Loc.t -> PowLoc.t) primitive
  | Locs_remove_null : (PowLoc.t -> PowLoc.t) primitive
  | Locs_is_singleton : (PowLoc.t -> bool) primitive
  | Locs_choose : (PowLoc.t -> Loc.t) primitive
  | Locs_prune : (binop -> PowLoc.t -> (unit -> bool) -> PowLoc.t) primitive
  | Loc_is_global : (Loc.t -> bool) primitive
  | Loc_is_local : (Loc.t -> bool) primitive
  | Loc_proc : (Loc.t -> Proc.t) primitive
  | Variable_locs : ((Proc.t -> PowLoc.t) -> Proc.t -> PowLoc.t) primitive
  | Is_recursive : (Proc.t -> CallGraph.t -> bool) primitive
  | Loc_frame_local : (Loc.t -> bool) primitive
  | Unsound_update : (Spec.t -> bool) primitive
  | Unsound_bitwise : (Spec.t -> bool) primitive
  | Lookup : (PowLoc.t -> Mem.t -> Val.t) primitive
  | Strong_update : (PowLoc.t -> Val.t -> Mem.t -> Mem.t) primitive
  | Weak_update : (PowLoc.t -> Val.t -> Mem.t -> Mem.t) primitive
  | Observe_strong_update : (PowLoc.t -> unit) primitive
  | Observe_weak_update : (PowLoc.t -> unit) primitive
  | Mem_join : (Mem.t -> Mem.t -> Mem.t) primitive
  | Mem_meet : (Mem.t -> Mem.t -> Mem.t) primitive
  | Eval_const : ((unit -> Val.t) -> Val.t) primitive
  | Size_of : ((unit -> typ) -> Val.t) primitive
  | Size_of_exp : ((unit -> typ) -> Val.t) primitive
  | Align_of : ((unit -> typ) -> Val.t) primitive
  | Cast : ((unit -> typ) -> (unit -> typ) -> Val.t -> Val.t) primitive
  | Pruned_value : (Val.t -> Itv.t -> PowLoc.t -> Val.t) primitive
  | Reject_label : (unit -> Val.t) primitive
  | Node_proc : (node_binding -> Proc.t) primitive
  | Node_allocsite : (node_binding -> Allocsite.t) primitive
  | String_allocsite : (node_binding -> Allocsite.t) primitive
  | Array_make :
      (Allocsite.t -> Itv.t -> Itv.t -> Itv.t -> Itv.t -> ArrayBlk.t) primitive
  | Struct_make : (PowLoc.t -> compinfo -> StructBlk.t) primitive
  | Val_of_struct : (StructBlk.t -> Val.t) primitive
  | Function_value : (Proc.t -> Val.t) primitive
  | Loc_of_allocsite : (Allocsite.t -> Loc.t) primitive
  | Return_locs : (Proc.t -> (unit -> typ) -> PowLoc.t) primitive
  | Scalar_lvalue : ((unit -> typ) -> bool) primitive
  | External_site : (unit -> Allocsite.t) primitive
  | External_value : (Allocsite.t -> Val.t) primitive
  | Val_procs : (Val.t -> PowProc.t) primitive
  | Procs_is_bot : (PowProc.t -> bool) primitive
  | Formal_groups :
      ((Proc.t -> Loc.t list) -> PowProc.t -> formal_groups) primitive
  | Compatible_formals :
      (formal_groups -> Val.t list -> formal_groups) primitive
  | Several_formals : (formal_groups -> bool) primitive
  | Call_return_locs : (PowProc.t -> (unit -> typ) -> PowLoc.t) primitive
  | Dump_weak_add : (Proc.t -> PowLoc.t -> Dump.t -> Dump.t) primitive
  | Val_all_locs : (Val.t -> PowLoc.t) primitive
  | Array_size : (ArrayBlk.t -> Itv.t) primitive
  | Array_null : (ArrayBlk.t -> Itv.t) primitive
  | Array_set_null : (ArrayBlk.t -> Itv.t -> ArrayBlk.t) primitive
  | Array_plus_null : (ArrayBlk.t -> Itv.t -> ArrayBlk.t) primitive
  | Array_input : (Allocsite.t -> ArrayBlk.t) primitive
  | Named_external_site : (string -> Allocsite.t) primitive
  | Alloc_one_size : ((unit -> typ) -> Itv.t) primitive
  | Arithmetic_lvalue : ((unit -> typ) -> bool) primitive
  | Unknown_scalar : ((unit -> typ) -> Val.t) primitive
  | Unknown_array : (Allocsite.t -> (unit -> typ) -> Val.t) primitive
  | Default_spec : (unit -> Spec.t) primitive
  | Val_cast_types : ((unit -> typ) -> typ -> Val.t -> Val.t) primitive
  | Lvalue_type : ((unit -> typ) -> typ) primitive
  | Named_field : (compinfo -> string -> fieldinfo) primitive
  | Fail_memory : (string -> Mem.t) primitive
  | Assert_condition : (int -> bool -> unit) primitive
  | Scaffold : (unit -> bool) primitive
  | Verbose : (unit -> bool) primitive
  | Unsound_library : (Spec.t -> string -> bool) primitive
  | Print_values : (string -> Val.t list -> unit) primitive
  | Print_memory : (string -> Mem.t -> unit) primitive
  | Describe_expressions : ((unit -> string) -> string) primitive
  | Text_concat : (string -> string -> string) primitive

(* Environment adapters and finite domain fragments from ItvSem.
   Keep catches here: moving [typeOf] outside [Cast]'s try changes behaviour. *)
let val_is_bot v = Val.eq v Val.bot
let locs_remove_null = PowLoc.remove Loc.null
let locs_is_singleton x = PowLoc.cardinal x = 1

let metadata_location vi pid =
  if vi.global then Loc.of_gvar vi.name vi.declared_type
  else Loc.of_lvar pid vi.name vi.declared_type

let variable_loc vi pid = metadata_location (variable_metadata vi) pid

(* A scoped variable adapter: a client binds a variable to the locations it
   denotes in its own program.  The analysis itself never installs one. *)
let variable_adapter : (varinfo -> Proc.t -> PowLoc.t option) option ref =
  ref None

let variable_locs vi pid =
  match !variable_adapter with
  | None -> PowLoc.singleton (variable_loc vi pid)
  | Some bind -> (
      match bind vi pid with
      | Some locations -> locations
      | None -> PowLoc.singleton (variable_loc vi pid))

let with_variable_adapter bind action =
  let previous = !variable_adapter in
  variable_adapter := Some bind;
  Fun.protect ~finally:(fun () -> variable_adapter := previous) action

let force_query query = query ()

let prune_locations op locations zero =
  match op with
  | Eq when zero () -> PowLoc.singleton Loc.null
  | Ne when zero () -> PowLoc.remove Loc.null locations
  | _ -> locations

let unsound_update spec = spec.Spec.unsound_update
let unsound_bitwise spec = spec.Spec.unsound_bitwise

let eval_const = function
  | CInt (n, _, _) ->
      Val.of_itv (try Itv.of_int (Cilint.to_int n) with _ -> Itv.top)
  | CChr c -> Val.of_itv (Itv.of_int (int_of_char c))
  | CReal (f, _, _) ->
      Val.of_itv (Itv.of_ints (int_of_float (floor f)) (int_of_float (ceil f)))
  | CStr _ | CWStr _ | CEnum _ -> Val.of_itv Itv.top

let size_of_with_layout resolve_comp query =
  Val.of_itv
    (try Itv.of_int (CilHelper.byteSizeOf_with_layout resolve_comp (query ()))
     with _ -> Itv.pos)

let size_of = size_of_with_layout Fun.id
let size_of_exp = size_of

let align_of_with_layout resolve_comp query =
  Val.of_itv (Itv.of_int (alignOf_int (query ())))

let align_of = align_of_with_layout Fun.id

let cast_with_layout resolve_comp query target v =
  try Val.cast_with_layout resolve_comp (query ()) (target ()) v with _ -> v

let cast = cast_with_layout Fun.id

let pruned_value v i p =
  Val.make (i, p, Val.array_of_val v, Val.struct_of_val v, Val.pow_proc_of_val v)

let reject_label () =
  invalid_arg
    "itvSem.ml:eval AddrOfLabel mem. Analysis does not support label values."

let function_value pid = Val.of_pow_proc (PowProc.singleton pid)
let return_locs pid query = PowLoc.singleton (Loc.return_var pid (query ()))

let scalar_lvalue query =
  match query () with TInt _ | TFloat _ -> true | _ -> false

let external_site () = Allocsite.allocsite_of_ext None

let formal_groups formals targets =
  PowProc.fold
    (fun target groups -> BatSet.add (formals target) groups)
    targets BatSet.empty

let compatible_formals groups values =
  BatSet.filter
    (fun locations -> List.length locations = List.length values)
    groups

let several_formals groups = BatSet.cardinal groups > 1

let call_return_locs targets query =
  PowProc.fold
    (fun target locations ->
      PowLoc.add (Loc.return_var target (query ())) locations)
    targets PowLoc.empty

let named_external_site name = Allocsite.allocsite_of_ext (Some name)

let alloc_one_size_with_layout resolve_comp declared_type =
  try
    let typ =
      match declared_type () with
      | TFun (TPtr (t, _), _, _, _) -> t
      | _ -> assert false
    in
    Itv.of_int (CilHelper.byteSizeOf_with_layout resolve_comp typ)
  with _ -> Itv.top

let alloc_one_size = alloc_one_size_with_layout Fun.id
let arithmetic_lvalue query = isArithmeticType (unrollTypeDeep (query ()))

let unknown_scalar query =
  Val.of_itv
    (if CilHelper.is_unsigned (unrollTypeDeep (query ())) then Itv.nat
     else Itv.top)

let unknown_array_with_layout resolve_comp site query =
  ArrayBlk.extern site
  |> ArrayBlk.cast_array_with_layout resolve_comp (query ())
  |> Val.of_array

let unknown_array = unknown_array_with_layout Fun.id

let named_field_with_layout resolve_comp comp name =
  List.find (fun field -> field.fname = name) (resolve_comp comp).cfields

let named_field = named_field_with_layout Fun.id

(* A scoped layout adapter: a client resolves a declared composite to the
   definition whose layout applies, when a layout is consumed.  The analysis
   itself never installs one; without it every layout is the type's own. *)
let layout_adapter : (compinfo -> compinfo) option ref = ref None

let resolve_layout comp =
  match !layout_adapter with None -> comp | Some resolve -> resolve comp

let with_layout_adapter resolve action =
  let previous = !layout_adapter in
  layout_adapter := Some resolve;
  Fun.protect ~finally:(fun () -> layout_adapter := previous) action

(* Source sites are part of the assertion diagnostic: they name this
   file's location. *)
let assert_condition line condition =
  if not condition then
    raise (Assert_failure ("sparrow/src/semantics/itvSem.ml", line, 12))

let unsound_library spec key = BatSet.mem key spec.Spec.unsound_lib

let print_values description values =
  prerr_endline
    ("sparrow_print (" ^ description ^ ") : "
    ^ Vocab.string_of_list Val.to_string values)

let print_memory location memory =
  prerr_endline ("sparrow_dump (" ^ location ^ ") : \n" ^ Mem.to_string memory)

let meaning : type a. a primitive -> a = function
  | Val_of_itv -> Val.of_itv
  | Val_itv -> Val.itv_of_val
  | Val_locs -> Val.pow_loc_of_val
  | Val_array -> Val.array_of_val
  | Val_struct -> Val.struct_of_val
  | Val_of_locs -> Val.of_pow_loc
  | Val_of_array -> Val.of_array
  | Val_join -> Val.join
  | Val_is_bot -> val_is_bot
  | Val_modify_itv -> Val.modify_itv
  | Itv_is_bot -> Itv.is_bot
  | Itv_eq -> Itv.eq
  | Itv_le -> Itv.le
  | Itv_join -> Itv.join
  | Itv_meet -> Itv.meet
  | Itv_plus -> Itv.plus
  | Itv_minus -> Itv.minus
  | Itv_times -> Itv.times
  | Itv_divide -> Itv.divide
  | Itv_lt -> Itv.lt_itv
  | Itv_gt -> Itv.gt_itv
  | Itv_le_itv -> Itv.le_itv
  | Itv_ge -> Itv.ge_itv
  | Itv_eq_itv -> Itv.eq_itv
  | Itv_ne -> Itv.ne_itv
  | Itv_and -> Itv.l_and
  | Itv_or -> Itv.l_or
  | Itv_shift -> Itv.l_shift
  | Itv_unknown_binary -> Itv.unknown_binary
  | Itv_not -> Itv.l_not
  | Itv_unknown_unary -> Itv.unknown_unary
  | Itv_prune -> Itv.prune
  | Array_plus -> ArrayBlk.plus_offset
  | Array_minus -> ArrayBlk.minus_offset
  | Array_offset -> ArrayBlk.offsetof
  | Array_locs -> ArrayBlk.pow_loc_of_array
  | Array_field -> ArrayBlk.append_field
  | Struct_field -> StructBlk.append_field
  | Locs_join -> PowLoc.join
  | Locs_singleton -> PowLoc.singleton
  | Locs_remove_null -> locs_remove_null
  | Locs_is_singleton -> locs_is_singleton
  | Locs_choose -> PowLoc.choose
  | Locs_prune -> prune_locations
  | Loc_is_global -> Loc.is_gvar
  | Loc_is_local -> Loc.is_lvar
  | Loc_proc -> Loc.get_proc
  | Variable_locs -> fun locations pid -> locations pid
  | Is_recursive -> fun pid callgraph -> CallGraph.is_rec callgraph pid
  | Loc_frame_local -> FrameLocal.mem
  | Unsound_update -> unsound_update
  | Unsound_bitwise -> unsound_bitwise
  | Lookup -> Mem.lookup
  | Strong_update -> Mem.strong_update
  | Weak_update -> Mem.weak_update
  | Mem_join -> Mem.join
  | Mem_meet -> Mem.meet
  | Observe_strong_update -> Mem.observe_update ~weak:false
  | Observe_weak_update -> Mem.observe_update ~weak:true
  | Eval_const -> force_query
  | Size_of -> size_of_with_layout resolve_layout
  | Size_of_exp -> size_of_with_layout resolve_layout
  | Align_of -> align_of_with_layout resolve_layout
  | Cast -> cast_with_layout resolve_layout
  | Pruned_value -> pruned_value
  | Reject_label -> reject_label
  | Node_proc -> fun node -> node.node_procedure
  | Node_allocsite -> fun node -> node.node_allocation ()
  | String_allocsite -> fun node -> node.node_string_allocation ()
  | Array_make -> ArrayBlk.make
  | Struct_make -> StructBlk.make
  | Val_of_struct -> Val.of_struct
  | Function_value -> function_value
  | Loc_of_allocsite -> Loc.of_allocsite
  | Return_locs -> return_locs
  | Scalar_lvalue -> scalar_lvalue
  | External_site -> external_site
  | External_value -> Val.external_value
  | Val_procs -> Val.pow_proc_of_val
  | Procs_is_bot -> fun targets -> PowProc.eq targets PowProc.bot
  | Formal_groups -> formal_groups
  | Compatible_formals -> compatible_formals
  | Several_formals -> several_formals
  | Call_return_locs -> call_return_locs
  | Dump_weak_add -> Dump.weak_add
  | Val_all_locs -> Val.all_loc_of_val
  | Array_size -> ArrayBlk.sizeof
  | Array_null -> ArrayBlk.nullof
  | Array_set_null -> ArrayBlk.set_null_pos
  | Array_plus_null -> ArrayBlk.plus_null_pos
  | Array_input -> ArrayBlk.input
  | Named_external_site -> named_external_site
  | Alloc_one_size -> alloc_one_size_with_layout resolve_layout
  | Arithmetic_lvalue -> arithmetic_lvalue
  | Unknown_scalar -> unknown_scalar
  | Unknown_array -> unknown_array_with_layout resolve_layout
  | Default_spec -> fun () -> Spec.empty
  | Val_cast_types ->
      fun source target value ->
        Val.cast_with_layout resolve_layout (source ()) target value
  | Lvalue_type -> force_query
  | Named_field -> named_field_with_layout resolve_layout
  | Fail_memory -> failwith
  | Assert_condition -> assert_condition
  | Scaffold -> fun () -> !Options.scaffold
  | Verbose -> fun () -> !Options.verbose >= 1
  | Unsound_library -> unsound_library
  | Print_values -> print_values
  | Print_memory -> print_memory
  | Describe_expressions -> force_query
  | Text_concat -> ( ^ )

let literal_value : type a. a literal -> a = function
  | Value x -> x
  | Interval x -> x
  | Bool x -> x
  | Int x -> x
  | Proc x -> x
  | Node x -> node_metadata x
  | Variable x -> fun pid -> variable_locs x pid
  | Field_info x -> x
  | Type x -> fun () -> x
  | Expression_type x -> fun () -> typeOf x
  | Is_zero x -> fun () -> isZero x
  | Constant x -> fun () -> eval_const x
  | Operator x -> x
  | Composite x -> x
  | Lvalue_type_query x -> fun () -> typeOfLval x
  | Text x -> x
  | Description x -> fun () -> Vocab.string_of_list CilHelper.s_exp x

module type STAGE = sig
  type 'a repr

  val literal : 'a literal -> 'a repr
  val primitive : 'a primitive -> 'a repr
  val app : ('a -> 'b) repr -> 'a repr -> 'b repr
  val let_ : 'a repr -> ('a repr -> 'b repr) -> 'b repr
  val if_ : bool repr -> (unit -> 'a repr) -> (unit -> 'a repr) -> 'a repr

  val value_boundary : Val.t repr -> Val.t repr
  (** Identity in the direct interpreter. Another instance may generalize branch
      knowledge here, before the common continuation stores a value. *)

  val discard : 'a repr -> unit repr
  (** Evaluate the effects and failures also when the value is unused. *)

  val unit : unit repr
  val pair : 'a repr -> 'b repr -> ('a * 'b) repr
  val values : Val.t repr list -> Val.t list repr

  val fold_procs :
    (Proc.t repr -> 'a repr -> 'a repr) -> PowProc.t repr -> 'a repr -> 'a repr

  val fold_formals :
    (Loc.t list repr -> Mem.t repr -> Mem.t repr) ->
    formal_groups repr ->
    Mem.t repr ->
    Mem.t repr

  val fold_bindings :
    (Loc.t repr -> Val.t repr -> Mem.t repr -> Mem.t repr) ->
    Loc.t list repr ->
    Val.t list repr ->
    Mem.t repr ->
    Mem.t repr
end

module Make (S : STAGE) = struct
  open S

  let p1 p x = app (primitive p) x
  let p2 p x y = app (app (primitive p) x) y
  let p3 p x y z = app (app (app (primitive p) x) y) z
  let ( let* ) = let_
  let interval x = literal (Interval x)
  let value x = literal (Value x)
  let bool x = literal (Bool x)
  let itv v = p1 Val_itv v
  let of_itv v = p1 Val_of_itv v
  let lookup locs mem = p2 Lookup locs mem

  let can_strong_update mode spec callgraph locs =
    if_ (p1 Unsound_update spec)
      (fun () -> bool true)
      (fun () ->
        match mode with
        | AbsSem.Weak -> bool false
        | AbsSem.Strong ->
            if_
              (p1 Locs_is_singleton locs)
              (fun () ->
                let* loc = p1 Locs_choose locs in
                if_ (p1 Loc_is_global loc)
                  (fun () -> bool true)
                  (fun () ->
                    if_ (p1 Loc_is_local loc)
                      (fun () ->
                        if_
                          (p2 Is_recursive (p1 Loc_proc loc) callgraph)
                          (fun () -> p1 Loc_frame_local loc)
                          (fun () -> bool true))
                      (fun () -> bool false)))
              (fun () -> bool false))

  let update mode spec callgraph locs v mem =
    if_
      (can_strong_update mode spec callgraph locs)
      (fun () -> p3 Strong_update locs v mem)
      (fun () -> p3 Weak_update locs v mem)

  let eval_uop spec op v =
    if_ (p1 Val_is_bot v)
      (fun () -> value Val.bot)
      (fun () ->
        let* i = itv v in
        of_itv
          (match op with
          | Neg -> p2 Itv_minus (interval Itv.zero) i
          | LNot -> p1 Itv_not i
          | BNot ->
              if_ (p1 Unsound_bitwise spec)
                (fun () -> interval Itv.bot)
                (fun () -> p1 Itv_unknown_unary i)))

  let eval_bop spec op a b =
    let ints op = of_itv (p2 op (itv a) (itv b)) in
    let pointer op =
      p2 Val_join
        (p1 Val_of_locs (p1 Val_locs a))
        (p1 Val_of_array (p2 op (p1 Val_array a) (itv b)))
    in
    match op with
    | PlusA -> ints Itv_plus
    | MinusA -> ints Itv_minus
    | Mult -> ints Itv_times
    | Div -> ints Itv_divide
    | PlusPI | IndexPI -> pointer Array_plus
    | MinusPI -> pointer Array_minus
    | MinusPP ->
        of_itv
          (p2 Itv_minus
             (p1 Array_offset (p1 Val_array a))
             (p1 Array_offset (p1 Val_array b)))
    | Lt -> ints Itv_lt
    | Gt -> ints Itv_gt
    | Le -> ints Itv_le_itv
    | Ge -> ints Itv_ge
    | Eq -> ints Itv_eq_itv
    | Ne -> ints Itv_ne
    | LAnd -> ints Itv_and
    | LOr -> ints Itv_or
    | Shiftlt ->
        if_ (p1 Unsound_bitwise spec) (fun () -> a) (fun () -> ints Itv_shift)
    | Shiftrt | Mod | BAnd | BXor | BOr ->
        if_ (p1 Unsound_bitwise spec)
          (fun () -> a)
          (fun () -> ints Itv_unknown_binary)

  let rec resolve_offset spec pid v os mem =
    match os with
    | NoOffset -> p2 Locs_join (p1 Val_locs v) (p1 Array_locs (p1 Val_array v))
    | Field (f, rest) ->
        let field = literal (Field_info f) in
        let* loaded = lookup (p1 Val_locs v) mem in
        let* locs =
          p2 Locs_join
            (p2 Struct_field (p1 Val_struct v) field)
            (p2 Locs_join
               (p2 Array_field (p1 Val_array v) field)
               (p2 Struct_field (p1 Val_struct loaded) field))
        in
        resolve_offset spec pid (p1 Val_of_locs locs) rest mem
    | Index (e, rest) ->
        let* loaded = lookup (p1 Val_locs v) mem in
        let* _ = discard (eval spec pid e mem) in
        resolve_offset spec pid
          (p1 Val_of_locs (p1 Array_locs (p1 Val_array loaded)))
          rest mem

  and eval_lv spec pid (host, offset) mem =
    let* v =
      match host with
      | Var vi -> p1 Val_of_locs (p2 Variable_locs (literal (Variable vi)) pid)
      | Mem e -> eval spec pid e mem
    in
    p1 Locs_remove_null (resolve_offset spec pid v offset mem)

  and eval spec pid e mem =
    match e with
    | Const c -> p1 Eval_const (literal (Constant c))
    | Lval lv | StartOf lv -> lookup (eval_lv spec pid lv mem) mem
    | SizeOf t -> p1 Size_of (literal (Type t))
    | SizeOfE e -> p1 Size_of_exp (literal (Expression_type e))
    | SizeOfStr s -> of_itv (interval (Itv.of_int (String.length s + 1)))
    | AlignOf t -> p1 Align_of (literal (Type t))
    | AlignOfE _ | Real _ | Imag _ -> of_itv (interval Itv.top)
    | UnOp (op, e, _) ->
        let* v = eval spec pid e mem in
        eval_uop spec op v
    | BinOp (op, a, b, _) ->
        (* Keep ItvSem's evaluation order. *)
        let* b = eval spec pid b mem in
        let* a = eval spec pid a mem in
        eval_bop spec op a b
    | Question (c, a, b, _) ->
        let* i = itv (eval spec pid c mem) in
        if_ (p1 Itv_is_bot i)
          (fun () -> value Val.bot)
          (fun () ->
            if_
              (p2 Itv_eq (interval Itv.zero) i)
              (fun () -> eval spec pid b mem)
              (fun () ->
                if_
                  (p2 Itv_le (interval Itv.zero) i)
                  (fun () ->
                    let* b = eval spec pid b mem in
                    let* a = eval spec pid a mem in
                    p2 Val_join a b)
                  (fun () -> eval spec pid a mem)))
    | CastE (_, t, e) ->
        let* v = eval spec pid e mem in
        p3 Cast (literal (Expression_type e)) (literal (Type t)) v
    | AddrOf lv -> p1 Val_of_locs (eval_lv spec pid lv mem)
    | AddrOfLabel _ -> p1 Reject_label unit

  let rec prune_simple mode spec callgraph pid cond mem =
    match cond with
    | BinOp (((Lt | Gt | Le | Ge | Eq | Ne) as op), Lval x, e, _) ->
        let* locs = eval_lv spec pid x mem in
        if_
          (p1 Locs_is_singleton locs)
          (fun () ->
            let* v = lookup locs mem in
            let* rhs = itv (eval spec pid e mem) in
            let* i = p3 Itv_prune (literal (Operator op)) (itv v) rhs in
            let* p =
              p3 Locs_prune (literal (Operator op)) (p1 Val_locs v)
                (literal (Is_zero e))
            in
            update mode spec callgraph locs (p3 Pruned_value v i p) mem)
          (fun () -> mem)
    | BinOp (((LAnd | LOr) as op), e1, e2, _) ->
        let* m1 = prune_simple mode spec callgraph pid e1 mem in
        let* m2 = prune_simple mode spec callgraph pid e2 mem in
        p2 (if op = LAnd then Mem_meet else Mem_join) m1 m2
    | UnOp (LNot, Lval x, _) -> prune_lvalue mode spec callgraph pid x mem true
    | Lval x -> prune_lvalue mode spec callgraph pid x mem false
    | _ -> mem

  and prune_lvalue mode spec callgraph pid x mem is_zero =
    let* locs = eval_lv spec pid x mem in
    if_
      (p1 Locs_is_singleton locs)
      (fun () ->
        let* v = lookup locs mem in
        let* i = itv v in
        let* i =
          if is_zero then p2 Itv_meet i (interval Itv.zero)
          else
            p2 Itv_join
              (p2 Itv_meet i (interval Itv.pos))
              (p2 Itv_meet i (interval Itv.neg))
        in
        update mode spec callgraph locs (p2 Val_modify_itv i v) mem)
      (fun () -> mem)

  let prune mode spec callgraph pid cond mem =
    match CilHelper.make_cond_simple cond with
    | None -> mem
    | Some cond -> prune_simple mode spec callgraph pid cond mem

  let assign_result evaluate store spec pid lv e mem =
    let* v = evaluate (eval spec pid e mem) in
    let* locs = eval_lv spec pid lv mem in
    store locs v

  let assign mode spec callgraph pid lv e mem =
    assign_result value_boundary
      (fun locs v -> update mode spec callgraph locs v mem)
      spec pid lv e mem

  (* Only the access information is consumed here. Share RHS/destination order
     and update-policy decisions with assignment; no intermediate store is
     elided. The caller must not consume the resulting memory or after-store
     changed-location observations. *)
  let assign_access mode spec callgraph pid lv e mem =
    assign_result discard
      (fun locs _ ->
        if_
          (can_strong_update mode spec callgraph locs)
          (fun () -> p1 Observe_strong_update locs)
          (fun () -> p1 Observe_weak_update locs))
      spec pid lv e mem

  let array_alloc spec node e is_static mem =
    let* size = itv (eval spec (p1 Node_proc node) e mem) in
    (* Keep ItvSem's fresh zero per allocation. Sharing Itv.zero here changes
       physical identities even though domain equality holds. *)
    let array =
      app
        (app
           (app
              (app
                 (app (primitive Array_make) (p1 Node_allocsite node))
                 (interval (Itv.of_int 0)))
              size)
           (interval (Itv.of_int 1)))
        (interval Itv.nat)
    in
    p2 Val_join
      (value
         (Val.of_pow_loc
            (if is_static then PowLoc.bot else PowLoc.singleton Loc.null)))
      (p1 Val_of_array array)

  let struct_alloc locs comp =
    p1 Val_of_struct (p2 Struct_make locs (literal (Composite comp)))

  let string_alloc node s =
    p1 Val_of_array
      (app
         (app
            (app
               (app
                  (app (primitive Array_make) (p1 String_allocsite node))
                  (interval (Itv.of_int 0)))
               (interval (Itv.of_int (String.length s + 1))))
            (interval (Itv.of_int 1)))
         (interval (Itv.of_int (String.length s))))

  let array_assign mode spec callgraph node lv e is_static mem =
    let* v = array_alloc spec node e is_static mem in
    let* locs = eval_lv spec (p1 Node_proc node) lv mem in
    update mode spec callgraph locs v mem

  let struct_assign mode spec callgraph pid lv comp mem =
    let* locs = eval_lv spec pid lv mem in
    update mode spec callgraph locs (struct_alloc locs comp) mem

  let string_assign mode spec callgraph node lv s mem =
    let* str_loc =
      p1 Locs_singleton (p1 Loc_of_allocsite (p1 String_allocsite node))
    in
    let* v = string_alloc node s in
    let* locs = eval_lv spec (p1 Node_proc node) lv mem in
    let* mem = update mode spec callgraph locs v mem in
    update mode spec callgraph str_loc (of_itv (interval Itv.nat)) mem

  let function_assign mode spec callgraph pid lv target mem =
    let* v = p1 Function_value target in
    let* locs = eval_lv spec pid lv mem in
    update mode spec callgraph locs v mem

  let return_store spec callgraph pid expression mem =
    match expression with
    | None -> mem
    | Some e ->
        let* v = value_boundary (eval spec pid e mem) in
        let* locs = p2 Return_locs pid (literal (Expression_type e)) in
        update AbsSem.Weak spec callgraph locs v mem

  let assume mode spec callgraph pid e mem =
    let* _ = discard (eval spec pid e mem) in
    prune mode spec callgraph pid e mem

  let external_store mode spec callgraph pid lv mem =
    if_
      (p1 Scalar_lvalue (literal (Lvalue_type_query lv)))
      (fun () ->
        update mode spec callgraph (eval_lv spec pid lv mem)
          (of_itv (interval Itv.top))
          mem)
      (fun () ->
        let* site = p1 External_site unit in
        let* v = p1 External_value site in
        let* ext = p1 Locs_singleton (p1 Loc_of_allocsite site) in
        let* mem = update mode spec callgraph (eval_lv spec pid lv mem) v mem in
        update mode spec callgraph ext v mem)

  let bind_lvar mode spec callgraph location v mem =
    update mode spec callgraph (p1 Locs_singleton location) v mem

  let bind_arg_ids mode spec callgraph vs locations mem =
    fold_bindings (bind_lvar mode spec callgraph) locations vs mem

  let bind_arg_lvars_set mode spec callgraph groups vs mem =
    let* groups = p2 Compatible_formals groups vs in
    let bind mode =
      fold_formals
        (fun locations mem -> bind_arg_ids mode spec callgraph vs locations mem)
        groups mem
    in
    if_
      (p1 Several_formals groups)
      (fun () -> bind AbsSem.Weak)
      (fun () -> bind mode)

  let eval_list spec pid expressions mem =
    let rec loop acc = function
      | [] -> values (List.rev acc)
      | expression :: rest ->
          let* v = eval spec pid expression mem in
          loop (v :: acc) rest
    in
    loop [] expressions

  (* The provider contains formal locations only. Lookup failures and the
     formal/argument/destination evaluation order remain observable.
     In particular the destination sees the memory before formal writes. *)
  let user_call_with_arguments mode spec callgraph formals pid lvo f
      prepare_arguments mem dump =
    let* targets = p1 Val_procs (eval spec pid f mem) in
    if_ (p1 Procs_is_bot targets)
      (fun () -> pair mem dump)
      (fun () ->
        let* groups = p2 Formal_groups formals targets in
        prepare_arguments mem (fun mem vs ->
            let* dump =
              match lvo with
              | None -> dump
              | Some lv ->
                  let* returns =
                    p2 Call_return_locs targets (literal (Lvalue_type_query lv))
                  in
                  let* _ = discard (lookup returns mem) in
                  fold_procs
                    (fun target dump ->
                      let* destination = eval_lv spec pid lv mem in
                      p3 Dump_weak_add target destination dump)
                    targets dump
            in
            let* mem = bind_arg_lvars_set mode spec callgraph groups vs mem in
            pair mem dump))

  let user_call mode spec callgraph formals pid lvo f arguments mem dump =
    user_call_with_arguments mode spec callgraph formals pid lvo f
      (fun mem continue ->
        let* vs = eval_list spec pid arguments mem in
        continue mem vs)
      mem dump

  let call_return spec callgraph pid lv f mem =
    let* targets = p1 Val_procs (eval spec pid f mem) in
    let* returns =
      p2 Call_return_locs targets (literal (Lvalue_type_query lv))
    in
    update AbsSem.Weak spec callgraph (eval_lv spec pid lv mem)
      (lookup returns mem) mem
end

module Direct_stage = struct
  type 'a repr = 'a

  let literal = literal_value
  let primitive = meaning
  let app f x = f x
  let let_ x f = f x
  let if_ b yes no = if b then yes () else no ()
  let value_boundary value = value
  let discard value = ignore value
  let unit = ()
  let pair a b = (a, b)
  let values xs = xs
  let fold_procs = PowProc.fold
  let fold_formals = BatSet.fold
  let fold_bindings = Vocab.list_fold2
end

module Direct = struct
  include Make (Direct_stage)

  (* Keep the public direct API on CFG nodes. The common bodies use
     independent procedure, ordinary allocation and string allocation slots. *)
  let array_alloc spec node = array_alloc spec (node_metadata node)
  let string_alloc node = string_alloc (node_metadata node)

  let array_assign mode spec graph node =
    array_assign mode spec graph (node_metadata node)

  let string_assign mode spec graph node =
    string_assign mode spec graph (node_metadata node)
end
