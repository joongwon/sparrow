(** CFG for a Function. *)
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

open GoblintCil
open Vocab
open Cil
open CilHelper
open Printf

module Node = struct
  type t = ENTRY | EXIT | Node of int [@@deriving compare]

  let equal n1 n2 =
    match (n1, n2) with
    | ENTRY, ENTRY -> true
    | EXIT, EXIT -> true
    | Node i1, Node i2 -> i1 = i2
    | _, _ -> false

  let hash = Hashtbl.hash
  let entry = ENTRY
  let exit = EXIT
  let nid = ref 0

  let fromCilStmt : Cil.stmt -> t =
   fun s ->
    if !nid < s.sid then nid := s.sid;
    Node s.sid

  let make () =
    nid := !nid + 1;
    Node !nid

  let id n = match n with ENTRY | EXIT -> -1 | Node id -> id

  let to_string : t -> string =
   fun n ->
    match n with ENTRY -> "ENTRY" | EXIT -> "EXIT" | Node i -> string_of_int i

  let pp fmt n = Format.fprintf fmt "%s" (to_string n)
end

module NodeSet = BatSet.Make (Node)

module Cmd = struct
  type t =
    | Cinstr of instr list
    | Cif of exp * block * block * location
    | CLoop of location
    (* final graph has the following cmds only *)
    | Cset of lval * exp * location
    | Cexternal of lval * location
    | Calloc of lval * alloc * static * location
    | Csalloc of lval * string * location
    | Cfalloc of lval * fundec * location
    | Cassume of exp * location
    | Ccall of lval option * exp * exp list * location
    | Creturn of exp option * location
    | Casm of
        attributes
        * string list
        * (string option * string * lval) list
        * (string option * string * exp) list
        * string list
        * location
    | Cskip

  and alloc = Array of exp | Struct of compinfo
  and static = bool

  let fromCilStmt : Cil.stmtkind -> t =
   fun s ->
    match s with
    | Instr instrs -> Cinstr instrs
    | If (exp, b1, b2, loc, _) -> Cif (exp, b1, b2, loc)
    | Loop (_, loc, _, _, _) -> CLoop loc
    | Return (expo, loc, _) -> Creturn (expo, loc)
    | _ -> Cskip

  let rec to_string : t -> string =
   fun c ->
    match c with
    | Cinstr instrs -> s_instrs instrs
    | Cset (lv, e, _) -> "set(" ^ s_lv lv ^ "," ^ s_exp e ^ ")"
    | Cexternal (lv, _) -> "extern(" ^ s_lv lv ^ ")"
    | Calloc (lv, Array e, _, _) -> "alloc(" ^ s_lv lv ^ ",[" ^ s_exp e ^ "])"
    | Calloc (lv, Struct compinfo, _, _) ->
        "alloc(" ^ s_lv lv ^ ",{" ^ compinfo.cname ^ "})"
    | Csalloc (lv, s, _) -> "salloc(" ^ s_lv lv ^ ", \"" ^ s ^ "\")"
    | Cfalloc (lv, f, _) -> "falloc(" ^ s_lv lv ^ ", " ^ f.svar.vname ^ ")"
    | Ccall (Some lv, fexp, params, _) ->
        s_lv lv ^ ":= call(" ^ s_exp fexp ^ ", " ^ s_exps params ^ ")"
    | Ccall (None, fexp, params, _) ->
        "call(" ^ s_exp fexp ^ s_exps params ^ ")"
    | Creturn (Some e, _) -> "return " ^ s_exp e
    | Creturn (None, _) -> "return"
    | Cif (e, b1, b2, loc) -> "if"
    | Cassume (e, loc) -> "assume(" ^ s_exp e ^ ")"
    | CLoop _ -> "loop"
    | Casm _ -> "asm"
    | Cskip -> "skip"

  let location_of : t -> Cil.location =
   fun c ->
    match c with
    | Cset (_, _, l)
    | Cexternal (_, l)
    | Calloc (_, _, _, l)
    | Csalloc (_, _, l)
    | Cfalloc (_, _, l)
    | Ccall (_, _, _, l) ->
        l
    | Creturn (_, l) -> l
    | Cassume (_, l) -> l
    | _ -> Cil.locUnknown
end

type node = Node.t
type cmd = Cmd.t

module G = Graph.Persistent.Digraph.ConcreteBidirectional (Node)
module Merge = Graph.Merge.P (G)
module Topo = Graph.Topological.Make (G)
module Scc = Graph.Components.Make (G)

module GDom = struct
  module V = Node

  type t = G.t

  let empty () = G.empty
  let fromG g = g
  let pred = G.pred
  let succ = G.succ
  let fold_vertex = G.fold_vertex
  let iter_vertex = G.iter_vertex
  let iter_succ = G.iter_succ
  let nb_vertex = G.nb_vertex
  let add_edge g a b = G.add_edge g a b
  let create : ?size:int -> unit -> t = fun ?size:int () -> G.empty
end

module Dom = Graph.Dominator.Make_graph (GDom)

type t = {
  fd : Cil.fundec;
  graph : G.t;
  cmd_map : (node, cmd) BatMap.t;
  dom_fronts : dom_fronts;
  dom_tree : dom_tree;
  scc_list : node list list;
}

and dom_fronts = (Node.t, NodeSet.t) BatMap.t
and dom_tree = G.t

let empty : Cil.fundec -> t =
 fun fd ->
  {
    fd;
    graph = G.empty;
    cmd_map = BatMap.empty;
    dom_fronts = BatMap.empty;
    dom_tree = G.empty;
    scc_list = [];
  }

let get_pid : t -> string = fun g -> g.fd.svar.vname
let get_formals : t -> Cil.varinfo list = fun g -> g.fd.sformals

let get_formals_lval : t -> Cil.lval list =
 fun g -> List.map Cil.var g.fd.sformals

let get_scc_list : t -> node list list = fun g -> g.scc_list

let children_of_dom_tree node g =
  NodeSet.remove node (NodeSet.of_list (G.succ g.dom_tree node))

let parent_of_dom_tree node g =
  match G.pred g.dom_tree node with
  | [] -> None
  | [ p ] -> Some p
  | _ -> raise (Failure "IntraCfg.parent_of_dom_tree: fatal")

let dom_fronts node g = BatMap.find node g.dom_fronts

let nodesof : t -> node list =
 fun g -> G.fold_vertex (fun x l -> x :: l) g.graph []

(** [add_edge n1 n2 g] adds an edge [n1 -> n2] to the graph [g]. *)
let add_edge : node -> node -> t -> t =
 fun n1 n2 g -> { g with graph = G.add_edge g.graph n1 n2 }

let add_node : node -> t -> t =
 fun n g -> { g with graph = G.add_vertex g.graph n }

let find_cmd : node -> t -> cmd =
 fun n g ->
  try
    if n = Node.ENTRY || n = Node.EXIT then Cmd.Cskip
    else BatMap.find n g.cmd_map
  with _ -> raise (Failure ("Can't find cmd of " ^ Node.to_string n))

(** [add_cmd n c g] is [g with n ↦ c] *)
let add_cmd : node -> cmd -> t -> t =
 fun n c g -> { g with cmd_map = BatMap.add n c g.cmd_map }

let add_node_with_cmd : node -> cmd -> t -> t =
 fun n c g -> g |> add_node n |> add_cmd n c

(** [remove_edge n1 n2 g] removes an edge [n1 -> n2] from the graph [g]. *)
let remove_edge : node -> node -> t -> t =
 fun n1 n2 g -> { g with graph = G.remove_edge g.graph n1 n2 }

let remove_node : node -> t -> t =
 fun n g ->
  {
    g with
    graph = G.remove_vertex g.graph n;
    cmd_map = BatMap.remove n g.cmd_map;
    dom_fronts = BatMap.remove n g.dom_fronts;
    dom_tree = G.remove_vertex g.dom_tree n;
  }

(* should be used only after all Cil nodes are made *)
let add_new_node : node -> cmd -> node -> t -> t =
 fun n cmd s g ->
  let new_node = Node.make () in
  (add_cmd new_node cmd >>> remove_edge n s >>> add_edge n new_node
 >>> add_edge new_node s)
    g

(* TODO: optimize G.pred *)
let pred : node -> t -> node list = fun n g -> G.pred g.graph n
let succ : node -> t -> node list = fun n g -> G.succ g.graph n
let fold_node f g a = G.fold_vertex f g.graph a
let fold_edges f g a = G.fold_edges f g.graph a

let is_entry : node -> bool =
 fun node -> match node with Node.ENTRY -> true | _ -> false

let is_exit : node -> bool =
 fun node -> match node with Node.EXIT -> true | _ -> false

let is_callnode : node -> t -> bool =
 fun n g -> match find_cmd n g with Cmd.Ccall _ -> true | _ -> false

let is_returnnode : node -> t -> bool =
 fun n g -> List.length (pred n g) = 1 && is_callnode (List.hd (pred n g)) g

let entryof _ = Node.ENTRY
let exitof _ = Node.EXIT

let returnof : node -> t -> node =
 fun n g ->
  if is_callnode n g then (
    assert (List.length (succ n g) = 1);
    List.hd (succ n g))
  else failwith "IntraCfg.returnof: given node is not a call-node"

let is_inside_loop : node -> t -> bool =
 fun n g ->
  List.exists (fun scc -> List.length scc > 1 && List.mem n scc) g.scc_list

let callof : node -> t -> node =
 fun r g ->
  try List.find (fun c -> is_callnode c g && returnof c g = r) (nodesof g)
  with _ -> failwith "IntraCfg.callof: given node may not be a return-node"

let generate_assumes : t -> t =
 fun g ->
  try
    fold_node
      (fun n g ->
        match find_cmd n g with
        | Cmd.Cif (e, tb, fb, loc) ->
            let succs = succ n g in
            (* successors of if-node *)
            let _ = assert (List.length succs = 1 || List.length succs = 2) in
            if List.length succs = 2 then (* normal case *)
              let s1, s2 = (List.nth succs 0, List.nth succs 1) in
              let tbn, fbn =
                (* true-branch node, false-branch node *)
                match (tb.bstmts, fb.bstmts) with
                | [], [] -> (s1, s2)
                | t :: l, _ -> if t.sid = Node.id s1 then (s1, s2) else (s2, s1)
                | _, t :: l -> if t.sid = Node.id s2 then (s1, s2) else (s2, s1)
              in
              let tassert = Cmd.Cassume (e, loc) in
              let fassert = Cmd.Cassume (UnOp (LNot, e, Cil.typeOf e), loc) in
              (add_new_node n fassert fbn >>> add_new_node n tassert tbn) g
            else
              (* XXX : when if-statement has only one successor.
                        seems to happen inside dead code *)
              let tbn = List.nth succs 0 in
              let tassert = Cmd.Cassume (e, loc) in
              add_new_node n tassert tbn g
        | _ -> g)
      g g
  with _ -> assert false

(* If and Loop are unnecessary in cfg *)
let remove_if_loop : t -> t =
 fun g ->
  fold_node
    (fun n g ->
      match find_cmd n g with
      | Cmd.Cif _ | Cmd.CLoop _ -> add_cmd n Cmd.Cskip g
      | _ -> g)
    g g

(* remove all nodes s.t. n1 -> empty_node -> n2 *)
let remove_empty_nodes : t -> t =
 fun g ->
  fold_node
    (fun n g ->
      if
        find_cmd n g = Cmd.Cskip
        && List.length (succ n g) = 1
        && List.length (pred n g) = 1
      then
        let p = List.nth (pred n g) 0 in
        let s = List.nth (succ n g) 0 in
        g |> remove_node n |> add_edge p s
      else g)
    g g

(* split instructions into set/call/asm *)
let flatten_instructions : t -> t =
 fun g ->
  fold_node
    (fun n g ->
      match find_cmd n g with
      | Cmd.Cinstr instrs when instrs <> [] ->
          let cmds =
            List.map
              (fun i ->
                match i with
                | Set (lv, e, loc, _) -> Cmd.Cset (lv, e, loc)
                | Call (lvo, f, args, loc, _) -> Cmd.Ccall (lvo, f, args, loc)
                | Asm (a, b, c, d, e, f) -> Cmd.Casm (a, b, c, d, e, f)
                | VarDecl _ ->
                    failwith "CIL VarDecl instructions are not supported")
              instrs
          in
          let pairs = List.map (fun c -> (Node.make (), c)) cmds in
          let first, _ = List.nth pairs 0 in
          let last, _ = List.nth pairs (List.length pairs - 1) in
          let preds, succs = (pred n g, succ n g) in
          g
          |> (fun g ->
          (* add nodes in instrs *)
          List.fold_left (fun g (n, c) -> add_node_with_cmd n c g) g pairs)
          |> (fun g ->
          (* connect edges between instrs *)
          fst
            (List.fold_left
               (fun (g, p) (n, c) -> (add_edge p n g, n))
               (g, n) pairs))
          |> list_fold (fun p -> add_edge p first) preds
          |> list_fold (fun s -> add_edge last s) succs
          |> remove_node n
      | Cmd.Cinstr [] -> add_cmd n Cmd.Cskip g
      | _ -> g)
    g g

(** [generate_alloc_array lv typ exp loc entry g] generates a malloc for an
    array of [typ] with length [exp] at lval [lv], starting from the entry node
    [entry]. It does not handle nested arrays or structs. *)
let generate_alloc_array :
    Cil.lval -> Cil.typ -> Cil.exp -> Cil.location -> node -> t -> node * t =
 fun lv typ exp loc entry g ->
  (* lv = malloc(sizeof(typ) * exp) *)
  let alloc_node = Node.make () in
  ( alloc_node,
    g
    |> add_cmd alloc_node
         (Calloc (lv, Array (BinOp (Mult, SizeOf typ, exp, intType)), true, loc))
    |> add_edge entry alloc_node )

(** [generate_alloc_struct lv comp loc entry g] generates a malloc for a struct
    of [comp] at lval [lv], starting from the entry node [entry]. It does not
    handle nested arrays or structs. *)
let generate_alloc_struct :
    Cil.lval -> Cil.compinfo -> Cil.location -> node -> t -> node * t =
 fun lv comp loc entry g ->
  (* lv = malloc(sizeof(comp)) *)
  let alloc_node = Node.make () in
  ( alloc_node,
    g
    |> add_cmd alloc_node (Calloc (lv, Struct comp, true, loc))
    |> add_edge entry alloc_node )

(** [generate_array_loop fd lv exp loc entry f g] generates a loop for
    traversing an array with size [exp] and element type [typ].

    The loop body is generated by [term, g = f node_body_entry lv_element g],
    where [node_body_entry] is the entry node of the loop body, [lv_element] is
    the lval of the current element to be initialized (i.e. [lv[i]]), and [term]
    is the exit node of the loop body. *)
let generate_array_loop fd lv exp loc entry f g =
  (* nodes *)
  let init_node = Node.make () in
  let skip_node = Node.make () in
  let assume_node = Node.make () in
  let nassume_node = Node.make () in
  let incr_node = Node.make () in
  (* reused variables and expressions *)
  let idx = (Var (makeTempVar fd (TInt (IInt, []))), NoOffset) in
  let cond = BinOp (Lt, Lval idx, exp, intType) in
  (***
                          [entry]
                          ↓
                          [init_node: idx = 0]
                          ↓
                          [skip_node: skip]
                          ↓               ↓
      [assume_node: assume(idx < exp)]    return = [nassume_node: assume(!(idx < exp))]
      ↓
      …(loop body)…
      [term]
      ↓
      [incr_node: idx++] → back to [skip_node]
     *)
  (* loop body *)
  let term, g =
    f assume_node (addOffsetLval (Index (Lval idx, NoOffset)) lv) g
  in
  g
  |> add_cmd init_node
       (Cset (idx, Const (CInt (Cilint.zero_cilint, IInt, None)), loc))
  |> add_cmd skip_node Cskip
  (* while (i < exp) *)
  |> add_edge init_node skip_node
  |> add_edge entry init_node
  |> add_cmd assume_node (Cassume (cond, loc))
  |> add_edge skip_node assume_node
  |> add_cmd nassume_node (Cassume (UnOp (LNot, cond, intType), loc))
  |> add_edge skip_node nassume_node
  (* i++ *)
  |> add_cmd incr_node
       (Cset
          ( idx,
            BinOp
              ( PlusA,
                Lval idx,
                Const (CInt (Cilint.one_cilint, IInt, None)),
                intType ),
            loc ))
  |> add_edge term incr_node
  |> add_edge incr_node skip_node
  |> fun g -> (nassume_node, g)

(** [generate_build_array fd lv typ exp loc entry_node ~initialize g] inserts
    allocs for an array of [typ] with length [exp] at lval [lv], starting from
    the entry node [entry_node]. If [initialize] is true, it also initializes
    the elements of the array to zero. *)
let rec generate_build_array :
    Cil.fundec ->
    Cil.lval ->
    Cil.typ ->
    Cil.exp ->
    Cil.location ->
    node ->
    initialize:bool ->
    t ->
    node * t =
 fun fd lv typ exp loc entry ~initialize g ->
  let typ = unrollTypeDeep typ in
  match typ with
  | TArray (t, Some size, _) ->
      g
      |> generate_array_loop fd lv exp loc entry @@ fun assume_node element g ->
         (* tmp = malloc(size); element = tmp *)
         let tmp = (Var (makeTempVar fd (TPtr (TVoid [], []))), NoOffset) in
         let term, g = g |> generate_alloc_array tmp t size loc assume_node in
         let cast_node = Node.make () in
         g
         |> add_cmd cast_node
              (Cmd.Cset
                 ( element,
                   mkCast ~kind:Explicit ~e:(Lval tmp) ~newt:(TPtr (t, [])),
                   loc ))
         |> add_edge term cast_node
         |> generate_build_array fd element t size loc cast_node ~initialize
  | TComp (comp, _) ->
      g
      |> generate_array_loop fd lv exp loc entry @@ fun assume_node element g ->
         (* tmp = malloc(size); element = tmp *)
         let term, g =
           g |> generate_alloc_struct element comp loc assume_node
         in
         g |> generate_build_fields comp.cfields element fd term ~initialize
  | _ when initialize ->
      (* simple type with zero initialization *)
      g
      |> generate_array_loop fd lv exp loc entry @@ fun assume_node element g ->
         (* element = 0 *)
         let init_node = Node.make () in
         ( init_node,
           g
           |> add_cmd init_node (Cset (element, zero, loc))
           |> add_edge assume_node init_node )
  | _ ->
      (* simple type without initialization *)
      (entry, g)

(** [generate_allocs_field fields lv fd entry ~initialize g] generates allocs
    for the [fields] of [lv], starting from the entry node [entry]. *)
and generate_build_fields :
    Cil.fieldinfo list ->
    Cil.lval ->
    Cil.fundec ->
    node ->
    initialize:bool ->
    t ->
    node * t =
 fun fl lv fd entry ~initialize g ->
  List.fold_left
    (fun (entry, g) fieldinfo ->
      let lv_field = addOffsetLval (Field (fieldinfo, NoOffset)) lv in
      match unrollTypeDeep fieldinfo.ftype with
      | TArray (typ, Some exp, _) ->
          (* tmp = alloc_array(exp); lv_field = (typ* )tmp; build_array(lv_field, typ, exp) *)
          let tmp = (Var (makeTempVar fd voidPtrType), NoOffset) in
          let term, g =
            generate_alloc_array tmp typ exp fieldinfo.floc entry g
          in
          let cast_node = Node.make () in
          g
          |> add_cmd cast_node
               (Cset
                  ( lv_field,
                    mkCast ~kind:Explicit ~e:(Lval tmp) ~newt:(TPtr (typ, [])),
                    fieldinfo.floc ))
          |> add_edge term cast_node
          |> generate_build_array fd lv_field typ exp fieldinfo.floc cast_node
               ~initialize
      | TComp (comp, _) ->
          (* lv_field = alloc_struct(comp); build_fields(lv_field, comp) *)
          let term, g =
            g |> generate_alloc_struct lv_field comp fieldinfo.floc entry
          in
          g |> generate_build_fields comp.cfields lv_field fd term ~initialize
      | _ when initialize ->
          let init_node = Node.make () in
          ( init_node,
            g
            |> add_cmd init_node (Cset (lv_field, zero, fieldinfo.floc))
            |> add_edge entry init_node )
      | _ -> (entry, g))
    (entry, g) fl

(** [generate_alloc_vars fd vl entry g] generates allocs for the variables [vl]
    of function [fd], starting from the entry node [entry]. *)
let generate_build_vars :
    Cil.fundec -> Cil.varinfo list -> node -> t -> node * t =
 fun fd vl entry g ->
  List.fold_left
    (fun (entry, g) varinfo ->
      match unrollTypeDeep varinfo.vtype with
      | TArray (typ, Some exp, _) ->
          let lv = (Var varinfo, NoOffset) in
          let tmp = (Var (makeTempVar fd voidPtrType), NoOffset) in
          let term, g =
            g |> generate_alloc_array tmp typ exp varinfo.vdecl entry
          in
          let cast_node = Node.make () in
          g
          |> add_cmd cast_node
               (Cmd.Cset
                  ( lv,
                    mkCast ~kind:Explicit ~e:(Lval tmp)
                      ~newt:(TPtr (unrollTypeDeep typ, [])),
                    varinfo.vdecl ))
          |> add_edge term cast_node
          |> generate_build_array fd lv typ exp varinfo.vdecl cast_node
               ~initialize:false
      | TComp (comp, _) ->
          let lv = (Var varinfo, NoOffset) in
          let term, g =
            g |> generate_alloc_struct lv comp varinfo.vdecl entry
          in
          g |> generate_build_fields comp.cfields lv fd term ~initialize:false
      | _ -> (entry, g))
    (entry, g) vl

let replace_node_graph : node -> node -> node -> t -> t =
 fun old entry exit g ->
  let preds = pred old g in
  let succs = succ old g in
  let g = remove_node old g in
  let g = List.fold_left (fun g p -> add_edge p entry g) g preds in
  let g = List.fold_left (fun g s -> add_edge exit s g) g succs in
  g

(* string allocation  *)
let transform_string_allocs : Cil.fundec -> t -> t =
 fun fd g ->
  let allocations = ref [] in
  let visitor =
    object
      inherit Cil.nopCilVisitor

      method! vexpr e =
        match e with
        | Const (CStr (s, _)) ->
            let tempinfo =
              Cil.makeTempVar fd (Cil.TPtr (Cil.TInt (IChar, []), []))
            in
            let temp = (Cil.Var tempinfo, Cil.NoOffset) in
            allocations := (temp, s) :: !allocations;
            Cil.ChangeTo (Lval temp)
        (* These operands are not evaluated. In particular, sizeof a literal
         must keep its array size rather than become sizeof a pointer. *)
        | SizeOfStr _ | SizeOfE _ | AlignOfE _ -> Cil.SkipChildren
        | _ -> Cil.DoChildren
    end
  in
  let exp e = Cil.visitCilExpr visitor e in
  let lval lv = Cil.visitCilLval visitor lv in
  let generate_sallocs :
      (Cil.lval * string) list -> Cil.location -> node -> t -> node * t =
   fun l loc node g ->
    List.fold_left
      (fun (node, g) (lv, s) ->
        let new_node = Node.make () in
        let g = add_edge node new_node g in
        let cmd = Cmd.Csalloc (lv, s, loc) in
        let g = add_cmd new_node cmd g in
        (new_node, g))
      (node, g) l
  in
  fold_node
    (fun n g ->
      allocations := [];
      let cmd =
        match find_cmd n g with
        | Cmd.Cset (lv, e, loc) -> Cmd.Cset (lval lv, exp e, loc)
        | Cmd.Cassume (e, loc) -> Cmd.Cassume (exp e, loc)
        | Cmd.Ccall (lv, f, args, loc) ->
            (* Extern is a storage class, not evidence of a missing body.
               External models also need valid pointer arguments. *)
            Cmd.Ccall (Option.map lval lv, exp f, List.map exp args, loc)
        | Cmd.Creturn (Some e, loc) -> Cmd.Creturn (Some (exp e), loc)
        | cmd -> cmd
      in
      match List.rev !allocations with
      | [] -> g
      | strings ->
          let entry, last = (Node.make (), Node.make ()) in
          let g = add_cmd entry Cmd.Cskip g in
          let node, g =
            generate_sallocs strings (Cmd.location_of cmd) entry g
          in
          let g = add_cmd last cmd g |> add_edge node last in
          replace_node_graph n entry last g)
    g g

(** replace [n] in [fd] with Calloc if it is a malloc call *)
let transform_one_malloc =
 fun fd n g ->
  let unwrap_sizeof exp =
    match exp with SizeOfE e -> SizeOf (Cil.typeOf e) | _ -> exp
  in
  match find_cmd n g with
  | Cmd.Ccall (Some lv, Lval (Var varinfo, _), args, loc)
    when varinfo.vname = "malloc" || varinfo.vname = "__builtin_alloca" ->
      (* remove the malloc node *)
      let preds = pred n g in
      let succs = succ n g in
      let g = List.fold_left (fun g s -> remove_edge n s g) g succs in
      let g = List.fold_left (fun g p -> remove_edge p n g) g preds in
      let g = remove_node n g in

      (* add a new node for the calloc command *)
      let new_node_start = Node.make () in
      let g = List.fold_left (fun g p -> add_edge p new_node_start g) g preds in
      let lv =
        match lv with
        | Var v, NoOffset -> (Var { v with vtype = voidPtrType }, NoOffset)
        | _ -> lv
      in
      let exp = List.hd args in
      let new_node_end, g =
        let exp = unwrap_sizeof exp in
        (* new_node_start: lv = alloc(size) *)
        let g = add_cmd new_node_start (Calloc (lv, Array exp, false, loc)) g in
        match exp with
        | BinOp (Mult, SizeOf typ, e, _) | BinOp (Mult, e, SizeOf typ, _) ->
          begin
            let typ = Cil.unrollTypeDeep typ in
            match (lv, typ) with
            | (Var _, NoOffset), TComp (_, _) ->
                (* dynamic struct array alloc *)
                generate_build_array fd lv typ e loc new_node_start
                  ~initialize:false g
            | _ ->
                (* simple type array alloc *)
                (new_node_start, g)
          end
        | SizeOf typ | CastE (_, _, SizeOf typ) -> begin
            let typ = Cil.unrollTypeDeep typ in
            match (lv, typ) with
            | (Var _, NoOffset), TComp (comp, _) ->
                (* dynamic struct alloc *)
                let cast_node = Node.make () in
                g
                |>
                (* cast_node: lv = (typ* )lv *)
                add_cmd cast_node
                  (Cset
                     ( lv,
                       Cil.mkCast ~kind:Explicit ~e:(Lval lv)
                         ~newt:(TPtr (typ, [])),
                       loc ))
                |> add_edge new_node_start cast_node
                |> generate_build_fields comp.cfields (Mem (Lval lv), NoOffset)
                     fd cast_node ~initialize:false
            | _, _ -> (new_node_start, g)
          end
        | _ -> (new_node_start, g)
      in
      List.fold_left (fun g s -> add_edge new_node_end s g) g succs
  | _ -> g

(** transform malloc in [fd] to Calloc *)
let transform_mallocs : Cil.fundec -> t -> t =
 fun fd g -> fold_node (transform_one_malloc fd) g g

(** for each call-node, insert a corresponding return-node *)
let insert_return_nodes : t -> t =
 fun g ->
  List.fold_left
    (fun g c ->
      match find_cmd c g with
      | Cmd.Ccall (_, Lval (Var varinfo, _), _, _)
        when varinfo.vname = "exit" || varinfo.vname = "abort" ->
          let r = returnof c g in
          let n = Node.make () in
          remove_edge c r g |> add_cmd n Cmd.Cskip |> add_edge c n
      | Cmd.Ccall (_, _, _, _) ->
          let r = returnof c g in
          add_new_node c Cmd.Cskip r g
      | _ -> g)
    g (nodesof g)

(** before each exit-node, insert a return cmd if there is not *)
let insert_return_before_exit : t -> t =
 fun g ->
  let add_return node acc =
    match find_cmd node g with
    | Cmd.Creturn _ -> acc
    | _ -> add_new_node node (Cmd.Creturn (None, locUnknown)) Node.EXIT acc
  in
  list_fold add_return (pred Node.EXIT g) g

let compute_dom : t -> t =
 fun g ->
  let dom_functions = Dom.compute_all (GDom.fromG g.graph) Node.ENTRY in
  let dom_tree =
    List.fold_left
      (fun dom_tree node ->
        List.fold_left
          (fun dom_tree child -> G.add_edge dom_tree node child)
          dom_tree
          (dom_functions.Dom.dom_tree node))
      G.empty (nodesof g)
  in
  let dom_fronts =
    List.fold_left
      (fun dom_fronts node ->
        BatMap.add node
          (NodeSet.of_list (dom_functions.Dom.dom_frontier node))
          dom_fronts)
      BatMap.empty (nodesof g)
  in
  { g with dom_tree; dom_fronts }

let compute_scc : t -> t = fun g -> { g with scc_list = Scc.scc_list g.graph }

let rec process_gvardecl :
    Cil.fundec -> Cil.lval -> Cil.location -> node -> t -> node * t =
 fun fd lv loc entry g ->
  match Cil.unrollTypeDeep (Cil.typeOfLval lv) with
  | TArray (typ, Some exp, _) ->
      let tmp = (Cil.Var (Cil.makeTempVar fd Cil.voidPtrType), Cil.NoOffset) in
      let term, g = generate_alloc_array tmp typ exp loc entry g in
      let cast_node = Node.make () in
      let cast_cmd =
        Cmd.Cset
          ( lv,
            Cil.mkCast ~kind:Cil.Explicit ~e:(Cil.Lval tmp)
              ~newt:(Cil.TPtr (typ, [])),
            loc )
      in
      let g = g |> add_cmd cast_node cast_cmd |> add_edge term cast_node in
      let term, g =
        generate_build_array fd lv typ exp loc cast_node ~initialize:true g
      in
      (term, g)
  | TInt (_, _) | TFloat (_, _) ->
      let node = Node.make () in
      let cmd = Cmd.Cset (lv, Cil.zero, loc) in
      (node, g |> add_cmd node cmd |> add_edge entry node)
  | TComp (comp, _) ->
      let term, g = generate_alloc_struct lv comp loc entry g in
      let term, g =
        generate_build_fields comp.cfields lv fd term g ~initialize:true
      in
      (term, g)
  | _ -> (entry, g)

let rec process_init :
    Cil.fundec -> Cil.lval -> Cil.init -> Cil.location -> node -> t -> node * t
    =
 fun fd lv i loc entry g ->
  match i with
  | SingleInit exp ->
      let new_node = Node.make () in
      let cmd = Cmd.Cset (lv, exp, loc) in
      let g = add_edge entry new_node (add_cmd new_node cmd g) in
      (new_node, g)
  | CompoundInit (typ, ilist) ->
      List.fold_left
        (fun (node, g) (offset, init) ->
          let lv = Cil.addOffsetLval offset lv in
          process_init fd lv init loc node g)
        (entry, g) ilist

let rec process_gvar :
    Cil.fundec ->
    Cil.lval ->
    Cil.initinfo ->
    Cil.location ->
    node ->
    t ->
    node * t =
 fun fd lv i loc entry g ->
  match (Cil.typeOfLval lv, i.init) with
  | _, None -> process_gvardecl fd lv loc entry g (* e.g., int global;     *)
  | _, Some (SingleInit exp as init) ->
      (* e.g., int global = 1; *)
      process_init fd lv init loc entry g
  | _, Some (CompoundInit (typ, ilist) as init) ->
      (* e.g., int global = { 1, 2 }; *)
      let node, g = process_gvardecl fd lv loc entry g in
      process_init fd lv init loc node g

let get_main_dec : Cil.global list -> (Cil.fundec * Cil.location) option =
 fun globals ->
  List.fold_left
    (fun s g ->
      match g with
      | Cil.GFun (fundec, loc) when fundec.svar.vname = "main" ->
          Some (fundec, loc)
      | _ -> s)
    None globals

let process_fundecl :
    Cil.fundec -> Cil.fundec -> Cil.location -> node -> t -> node * t =
 fun fd fundecl loc node g ->
  let new_node = Node.make () in
  let cmd = Cmd.Cfalloc ((Var fundecl.svar, NoOffset), fundecl, loc) in
  let g = add_edge node new_node (add_cmd new_node cmd g) in
  (new_node, g)

let generate_cmd_args : Cil.fundec -> Cil.location -> t -> node * t =
 fun fd loc g ->
  let argc, argv =
    ( (Cil.Var (List.nth fd.sformals 0), Cil.NoOffset),
      (Cil.Var (List.nth fd.sformals 1), Cil.NoOffset) )
  in
  let arg_node = Node.make () in
  let arg_cmd =
    Cmd.Ccall
      ( None,
        Cil.Lval
          (Cil.Var (Cil.makeGlobalVar "sparrow_arg" Cil.voidType), Cil.NoOffset),
        [ Cil.Lval argc; Cil.Lval argv ],
        loc )
  in

  let optind, optarg =
    ( (Cil.Var (Cil.makeGlobalVar "optind" Cil.intType), Cil.NoOffset),
      (Cil.Var (Cil.makeGlobalVar "optarg" Cil.charPtrType), Cil.NoOffset) )
  in
  let opt_node = Node.make () in
  let opt_cmd =
    Cmd.Ccall
      ( None,
        Cil.Lval
          (Cil.Var (Cil.makeGlobalVar "sparrow_opt" Cil.voidType), Cil.NoOffset),
        [ Cil.Lval optind; Cil.Lval optarg ],
        loc )
  in
  let g =
    g |> add_cmd arg_node arg_cmd |> add_cmd opt_node opt_cmd
    |> add_edge Node.ENTRY arg_node
    |> add_edge arg_node opt_node
  in
  (opt_node, g)

let init : Cil.fundec -> Cil.location -> t =
 fun fd loc ->
  let entry = Node.fromCilStmt (List.nth fd.sallstmts 0) in
  let g =
    (* add nodes *)
    (list_fold
       (fun s ->
         add_node_with_cmd (Node.fromCilStmt s) (Cmd.fromCilStmt s.skind))
       fd.sallstmts
    >>>
    (* add edges *)
    list_fold
      (fun stmt ->
        list_fold
          (fun succ -> add_edge (Node.fromCilStmt stmt) (Node.fromCilStmt succ))
          stmt.succs)
      fd.sallstmts)
      (empty fd)
  in
  let term, g =
    if fd.svar.vname = "main" && List.length fd.sformals >= 2 then
      generate_cmd_args fd loc g
    else (Node.ENTRY, g)
  in
  (* generate alloc cmds for static allocations *)
  let term, g = generate_build_vars fd fd.slocals term g in
  let g = add_edge term entry g in
  let nodes = nodesof g in
  let lasts = List.filter (fun n -> succ n g = []) nodes in
  g
  |> list_fold (fun last -> add_edge last Node.EXIT) lasts
  |> generate_assumes |> flatten_instructions |> remove_if_loop
  |> transform_mallocs fd (* generate alloc cmds for dynamic allocations *)
  |> transform_string_allocs fd (* generate salloc (string alloc) cmds *)
  |> remove_empty_nodes |> insert_return_nodes |> insert_return_before_exit

let generate_global_proc : Cil.global list -> Cil.fundec -> t =
 fun globals fd ->
  let entry = Node.ENTRY in
  let term, g =
    List.fold_left
      (fun (node, g) x ->
        match x with
        | Cil.GVar (var, init, loc) ->
            process_gvar fd (Cil.var var) init loc node g
        | Cil.GVarDecl (var, loc) ->
            process_gvardecl fd (Cil.var var) loc node g
        | Cil.GFun (fundec, loc) -> process_fundecl fd fundec loc node g
        | _ -> (node, g))
      (entry, empty fd)
      globals
  in
  let main_dec, main_loc =
    match get_main_dec globals with
    | Some (d, l) -> (d, l)
    | _ ->
        prerr_endline "Error: main not Found";
        exit 1
  in
  let call_node = Node.make () in
  let call_cmd =
    Cmd.Ccall (None, Lval (Var main_dec.svar, NoOffset), [], main_loc)
  in
  g |> add_cmd call_node call_cmd |> add_edge term call_node
  |> add_edge call_node Node.EXIT
  |> generate_assumes |> flatten_instructions |> remove_if_loop
  |> transform_string_allocs fd (* generate salloc (string alloc) cmds *)
  |> remove_empty_nodes |> insert_return_nodes

let unreachable_node : t -> NodeSet.t =
 fun g ->
  let all_nodes = NodeSet.of_list (nodesof g) in
  let rec remove_reachable_node' work acc =
    if NodeSet.is_empty work then acc
    else
      let node, work = NodeSet.pop work in
      if NodeSet.mem node acc then
        let acc = NodeSet.remove node acc in
        let succs = NodeSet.remove node (NodeSet.of_list (succ node g)) in
        let work = NodeSet.union work succs in
        remove_reachable_node' work acc
      else remove_reachable_node' work acc
  in
  remove_reachable_node' (NodeSet.singleton Node.ENTRY) all_nodes

let merge_vertex g vl =
  { g with graph = Merge.merge_vertex g.graph vl }
  |> remove_edge (List.hd vl) (List.hd vl)

let rec collect g n lval node_list exp_list =
  let s = succ n g |> List.hd in
  match (find_cmd n g, find_cmd s g) with
  | Cmd.Cset (l, e, _), _ when Cil.isConstant e ->
      begin match Cil.removeOffsetLval l with
      | l, Cil.Index (i, Cil.NoOffset)
        when CilHelper.eq_lval lval l && Cil.isConstant i ->
          let node_list, exp_list = (n :: node_list, e :: exp_list) in
          let ss = succ n g in
          if List.length ss = 1 then
            collect g (List.hd ss) lval node_list exp_list
          else (node_list, exp_list)
      | _ -> (node_list, exp_list)
      end
  | _ -> (node_list, exp_list)

let is_candidate n g =
  let is_starting_point lval =
    match Cil.removeOffsetLval lval with
    | l, Cil.Index (i, Cil.NoOffset) when Cil.isZero i -> Some l
    | _ -> None
  in
  let ss = try succ n g with _ -> [] in
  if List.length ss = 1 then
    let s = List.hd ss in
    match (find_cmd n g, find_cmd s g) with
    | Cmd.Cset (lval, e, _), _ when Cil.isIntegralType (Cil.typeOf e) ->
        is_starting_point lval
    | _ -> None
  else None

(* arr[0] = c0; arr[1] = c1; ..., arr[n] = cn; => sparrow_array_init(arr,c0, c1, ..., cn);
   salloc(arr[0], x0); x0 = s0; ..., => sparrow_array_init(arr, s0, s1, ..., sn) *)
let optimize_array_init : t -> t =
 fun g ->
  fold_node
    (fun n g ->
      match is_candidate n g with
      | Some lval ->
          let nodes, exps = collect g n lval [] [] in
          if List.length nodes > 1 then
            let new_node = Node.make () in
            let g = merge_vertex g (new_node :: nodes) in
            let args = Cil.Lval lval :: List.rev exps in
            let loc = find_cmd n g |> Cmd.location_of in
            let cmd =
              Cmd.Ccall
                ( None,
                  Cil.Lval
                    ( Cil.Var
                        (Cil.makeGlobalVar "sparrow_array_init" Cil.voidType),
                      Cil.NoOffset ),
                  args,
                  loc )
            in
            add_cmd new_node cmd g
          else g
      | _ -> g)
    g g

let optimize : t -> t = fun g -> optimize_array_init g

let print_dot : out_channel -> t -> unit =
 fun chan g ->
  fprintf chan "digraph %s {\n" g.fd.svar.vname;
  fprintf chan "{\n";
  fprintf chan "node [shape=box]\n";
  G.iter_vertex
    (fun v ->
      fprintf chan "%s [label=\"%s: %s\" %s]\n" (Node.to_string v)
        (Node.to_string v)
        (Cmd.to_string (find_cmd v g))
        (if is_callnode v g then "style=filled color=grey" else ""))
    g.graph;
  fprintf chan "}\n";
  G.iter_edges
    (fun v1 v2 ->
      fprintf chan "%s -> %s\n" (Node.to_string v1) (Node.to_string v2))
    g.graph;
  fprintf chan "}\n"

let print_dom_fronts dom_fronts =
  BatMap.iter
    (fun node fronts ->
      prerr_string (Node.to_string node ^ ": ");
      NodeSet.iter (fun fr -> prerr_string (Node.to_string fr ^ " ")) fronts;
      prerr_endline "")
    dom_fronts

let print_dom_tree dom_tree =
  prerr_endline (string_of_map Node.to_string Node.to_string dom_tree)

module Json = Yojson.Safe

let to_json : t -> Json.t =
 fun g ->
  let nodes =
    `Assoc
      (G.fold_vertex
         (fun v nodes ->
           ( Node.to_string v,
             `List
               [
                 `String (Cmd.to_string (find_cmd v g));
                 `Bool false;
                 `Bool (is_callnode v g);
               ] )
           :: nodes)
         g.graph [])
  in
  let edges =
    `List
      (G.fold_edges
         (fun v1 v2 edges ->
           `List [ `String (Node.to_string v1); `String (Node.to_string v2) ]
           :: edges)
         g.graph [])
  in
  `Assoc [ ("nodes", nodes); ("edges", edges) ]
