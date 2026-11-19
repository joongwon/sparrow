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
(** CFG for a Function. *)

open Vocab
open Sparrow_cil
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
  let initial_id = !nid
  let get_initial_id () = initial_id
  let get_next_id () = !nid
  let set_next_id value = nid := value

  let fromCilStmt : Sparrow_cil.stmt -> t =
   fun s ->
    if !nid < s.sid then nid := s.sid;
    Node s.sid

  let make () =
    nid := !nid + 1;
    Node !nid

  (* rebuild a node from its id (no counter effect) *)
  let of_id i = Node i
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
    | Calloc of lval * exp * location
    | Csalloc of lval * string * location
    | Cfalloc of lval * fundec * location
    | Cassume of exp * location
    | Ccall of lval option * exp * exp list * location
    | Creturn of exp option * location
    | Cskip

  let fromCilStmt : Sparrow_cil.stmtkind -> t =
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
    | Calloc (lv, e, _) -> "alloc(" ^ s_lv lv ^ ",[" ^ s_exp e ^ "])"
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
    | Cskip -> "skip"

  let location_of : t -> Sparrow_cil.location =
   fun c ->
    match c with
    | Cset (_, _, l)
    | Calloc (_, _, l)
    | Csalloc (_, _, l)
    | Cfalloc (_, _, l)
    | Ccall (_, _, _, l) ->
        l
    | Creturn (_, l) -> l
    | Cassume (_, l) -> l
    | _ -> Sparrow_cil.locUnknown
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
  fd : Sparrow_cil.fundec;
  graph : G.t;
  cmd_map : (node, cmd) BatMap.t;
  dom_fronts : dom_fronts;
  dom_tree : dom_tree;
  scc_list : node list list;
}

and dom_fronts = (Node.t, NodeSet.t) BatMap.t
and dom_tree = G.t

let empty : Sparrow_cil.fundec -> t =
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
let get_fd : t -> Sparrow_cil.fundec = fun g -> g.fd
let get_formals : t -> Sparrow_cil.varinfo list = fun g -> g.fd.sformals
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

let add_cmd : node -> cmd -> t -> t =
 fun n c g -> { g with cmd_map = BatMap.add n c g.cmd_map }

let add_node_with_cmd : node -> cmd -> t -> t =
 fun n c g -> g |> add_node n |> add_cmd n c

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

(* should be used only after all Sparrow_cil nodes are made *)
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

(* A node is a return-node iff it is the (unique) return-successor of its
   (unique) call-node predecessor.  The old definition only checked "the single
   predecessor is a call-node", which misclassifies the node after a synthetic
   `sparrow_array_init` Ccall (these are not real calls and the optimizer can
   leave them with succ-count <> 1): such a successor is NOT a real return-node,
   yet callof/returnof (which require the call's single successor to be this
   node) then cannot resolve it.  Requiring returnof-consistency here makes
   is_returnnode and callof agree by construction -- identical to the old
   behaviour on every well-formed call/return pair, and correct on malformed
   ones. *)
let is_returnnode : node -> t -> bool =
 fun n g ->
  match pred n g with
  | [ c ] -> (
      is_callnode c g && match succ c g with [ r ] -> r = n | _ -> false)
  | _ -> false

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

(* A return node's call is its single predecessor; other nodes are searched. *)
let callof : node -> t -> node =
 fun r g ->
  if is_returnnode r g then List.hd (pred r g)
  else
    try
      (* returnof asserts succ-length = 1; a malformed call-node elsewhere must
       not abort the search for r's own call-node, so swallow it per candidate. *)
      List.find
        (fun c -> is_callnode c g && try returnof c g = r with _ -> false)
        (nodesof g)
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
              let fassert =
                Cmd.Cassume (UnOp (LNot, e, Sparrow_cil.typeOf e), loc)
              in
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
                | Asm (a, b, c, d, e, f) -> Cmd.Cskip
                | VarDecl _ -> Cmd.Cskip)
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

let replace_node_graph : node -> node -> node -> t -> t =
 fun old entry exit g ->
  let preds = pred old g in
  let succs = succ old g in
  let g = remove_node old g in
  let g = List.fold_left (fun g p -> add_edge p entry g) g preds in
  List.fold_left (fun g s -> add_edge exit s g) g succs

(* string allocation  *)
let transform_string_allocs : Sparrow_cil.fundec -> t -> t =
 fun fd g ->
  let rec replace_str e =
    match e with
    | Const (CStr (s, _)) ->
        let tempinfo =
          Sparrow_cil.makeTempVar fd
            (Sparrow_cil.TPtr (Sparrow_cil.TInt (IChar, []), []))
        in
        let temp = (Sparrow_cil.Var tempinfo, Sparrow_cil.NoOffset) in
        (Lval temp, [ (temp, s) ])
    | Lval (Mem exp, off) -> (
        let exp', l = replace_str exp in
        match l with [] -> (e, l) | _ -> (Lval (Mem exp', off), l))
    | SizeOfStr s ->
        let tempinfo =
          Sparrow_cil.makeTempVar fd
            (Sparrow_cil.TPtr (Sparrow_cil.TInt (IChar, []), []))
        in
        let temp = (Sparrow_cil.Var tempinfo, Sparrow_cil.NoOffset) in
        (Lval temp, [ (temp, s) ])
    | SizeOfE exp -> (
        let exp', l = replace_str exp in
        match l with [] -> (e, l) | _ -> (SizeOfE exp', l))
    | AlignOfE exp -> (
        let exp', l = replace_str exp in
        match l with [] -> (e, l) | _ -> (AlignOfE exp', l))
    | UnOp (u, exp, t) -> (
        let exp', l = replace_str exp in
        match l with [] -> (e, l) | _ -> (UnOp (u, exp', t), l))
    | BinOp (b, e1, e2, t) -> (
        let e1', l1 = replace_str e1 in
        let e2', l2 = replace_str e2 in
        match l1 @ l2 with
        | [] -> (e, [])
        | _ -> (BinOp (b, e1', e2', t), l1 @ l2))
    | CastE (_, t, exp) -> (
        let exp', l = replace_str exp in
        match l with
        | [] -> (e, l)
        | _ -> (CastE (Sparrow_cil.Explicit, t, exp'), l))
    | _ -> (e, [])
  in
  let generate_sallocs l loc node g =
    List.fold_left
      (fun (node, g) (lv, s) ->
        let new_node = Node.make () in
        let g = add_edge node new_node g in
        let cmd = Cmd.Csalloc (lv, s, loc) in
        (new_node, add_cmd new_node cmd g))
      (node, g) l
  in
  (* make it consistent with manual encoding in *Sem.ml *)
  let targets =
    [
      "strcpy";
      "strcat";
      "strncpy";
      "memcpy";
      "memmove";
      "strlen";
      "fgets";
      "sprintf";
      "scanf";
      "getenv";
      "strdup";
      "gettext";
      "getpwent";
      "strchr";
      "strrchr";
    ]
  in
  fold_node
    (fun n g ->
      match find_cmd n g with
      | Cmd.Cset (lv, e, loc) -> (
          match replace_str e with
          | _, [] -> g
          | e, l ->
              let empty_node, last_node = (Node.make (), Node.make ()) in
              let g = add_cmd empty_node Cmd.Cskip g in
              let node, g = generate_sallocs l loc empty_node g in
              let cmd = Cmd.Cset (lv, e, loc) in
              let g = add_cmd last_node cmd g in
              let g = add_edge node last_node g in
              replace_node_graph n empty_node last_node g)
      | Cmd.Cassume (e, loc) -> (
          match replace_str e with
          | _, [] -> g
          | e, l ->
              let empty_node, last_node = (Node.make (), Node.make ()) in
              let g = add_cmd empty_node Cmd.Cskip g in
              let node, g = generate_sallocs l loc empty_node g in
              let cmd = Cmd.Cassume (e, loc) in
              let g = add_cmd last_node cmd g in
              let g = add_edge node last_node g in
              replace_node_graph n empty_node last_node g
              (* do not allocate memory cells for arguments of external lib calls *)
          )
      | Cmd.Ccall
          ( lv,
            Sparrow_cil.Lval (Sparrow_cil.Var f, Sparrow_cil.NoOffset),
            el,
            loc )
        when f.vstorage = Sparrow_cil.Extern
             && not (List.mem (SourceName.of_varinfo f) targets) ->
          g
      | Cmd.Ccall (lv, f, el, loc) -> (
          let el, l =
            List.fold_left
              (fun (el, l) param ->
                let e', l' = replace_str param in
                (el @ [ e' ], l @ l'))
              ([], []) el
          in
          match (el, l) with
          | _, [] -> g
          | el, l ->
              let empty_node, last_node = (Node.make (), Node.make ()) in
              let g = add_cmd empty_node Cmd.Cskip g in
              let node, g = generate_sallocs l loc empty_node g in
              let cmd = Cmd.Ccall (lv, f, el, loc) in
              let g = add_cmd last_node cmd g in
              let g = add_edge node last_node g in
              replace_node_graph n empty_node last_node g)
      | Cmd.Creturn (Some e, loc) -> (
          match replace_str e with
          | _, [] -> g
          | e, l ->
              let empty_node, last_node = (Node.make (), Node.make ()) in
              let g = add_cmd empty_node Cmd.Cskip g in
              let node, g = generate_sallocs l loc empty_node g in
              let cmd = Cmd.Creturn (Some e, loc) in
              let g = add_cmd last_node cmd g in
              let g = add_edge node last_node g in
              replace_node_graph n empty_node last_node g)
      | _ -> g)
    g g

(** transform malloc to Calloc: one uninitialized block *)
let transform_allocs : Sparrow_cil.fundec -> t -> t =
 fun fd g ->
  let transform lv exp loc node g =
    (node, add_cmd node (Cmd.Calloc (lv, exp, loc)) g)
  in
  fold_node
    (fun n g ->
      match find_cmd n g with
      | Cmd.Ccall (Some lv, Lval (Var varinfo, _), args, loc) ->
          let name = SourceName.of_varinfo varinfo in
          if name = "malloc" || name = "__builtin_alloca" then
            let new_node = Node.make () in
            let preds = pred n g in
            let succs = succ n g in
            let g = List.fold_left (fun g s -> remove_edge n s g) g succs in
            let g = List.fold_left (fun g p -> remove_edge p n g) g preds in
            let g = remove_node n g in
            let g = List.fold_left (fun g p -> add_edge p new_node g) g preds in
            let lv =
              match lv with
              | Var v, NoOffset -> (Var { v with vtype = voidPtrType }, NoOffset)
              | _ -> lv
            in
            let term, g = transform lv (List.hd args) loc new_node g in
            List.fold_left (fun g s -> add_edge term s g) g succs
          else g
      | _ -> g)
    g g

(** A direct call never returns when the callee is upstream's [exit] or [abort],
    or when its declaration carries the C11 [_Noreturn] specifier or the GNU
    [noreturn] attribute. CIL strips the underscores of [__noreturn__] and
    stores this name attribute on the varinfo (merging unions the attributes of
    every declaration); the function type is also checked, as CIL's own
    fall-through test does for indirect calls. *)
let is_noreturn_callee : varinfo -> bool =
 fun varinfo ->
  (let name = SourceName.of_varinfo varinfo in
   name = "exit" || name = "abort")
  || hasAttribute "noreturn" varinfo.vattr
  || hasAttribute "noreturn" (typeAttrs varinfo.vtype)

(** for each call-node, insert a corresponding return-node *)
let insert_return_nodes : t -> t =
 fun g ->
  List.fold_left
    (fun g c ->
      match find_cmd c g with
      | Cmd.Ccall (_, Lval (Var varinfo, _), _, _)
        when is_noreturn_callee varinfo ->
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
  (* A never-returning function (e.g. an infinite loop, or a body that only
     exit()s/abort()s) has no node flowing to EXIT, so EXIT is never added to
     the graph.  The whole program never has these (mergecil + reachability
     prune them), but a translation unit built alone can -- guard against asking
     ocamlgraph for the predecessors of a vertex that is not present. *)
  if G.mem_vertex g.graph Node.EXIT then
    list_fold add_return (pred Node.EXIT g) g
  else g

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

(* C's zero initialization of a global without initializer, through its
   arrays (one element stands for all) and fields. *)
let rec process_gvardecl :
    Sparrow_cil.fundec ->
    Sparrow_cil.lval ->
    Sparrow_cil.location ->
    node ->
    t ->
    node * t =
 fun fd lv loc entry g ->
  match Sparrow_cil.unrollTypeDeep (Sparrow_cil.typeOfLval lv) with
  | TArray _ ->
      let element =
        Sparrow_cil.addOffsetLval
          (Sparrow_cil.Index (Sparrow_cil.zero, Sparrow_cil.NoOffset))
          lv
      in
      process_gvardecl fd element loc entry g
  | TInt (_, _) | TFloat (_, _) | TEnum (_, _) ->
      let node = Node.make () in
      let cmd = Cmd.Cset (lv, Sparrow_cil.zero, loc) in
      (node, g |> add_cmd node cmd |> add_edge entry node)
  | TComp (comp, _) ->
      List.fold_left
        (fun (entry, g) field ->
          let lv =
            Sparrow_cil.addOffsetLval
              (Sparrow_cil.Field (field, Sparrow_cil.NoOffset))
              lv
          in
          process_gvardecl fd lv loc entry g)
        (entry, g) comp.cfields
  | _ -> (entry, g)

let rec process_init :
    Sparrow_cil.fundec ->
    Sparrow_cil.lval ->
    Sparrow_cil.init ->
    Sparrow_cil.location ->
    node ->
    t ->
    node * t =
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
          let lv = Sparrow_cil.addOffsetLval offset lv in
          process_init fd lv init loc node g)
        (entry, g) ilist

let get_main_dec :
    Sparrow_cil.global list ->
    (Sparrow_cil.fundec * Sparrow_cil.location) option =
 fun globals ->
  List.fold_left
    (fun s g ->
      match g with
      | Sparrow_cil.GFun (fundec, loc) when fundec.svar.vname = "main" ->
          Some (fundec, loc)
      | _ -> s)
    None globals

let process_fundecl :
    Sparrow_cil.fundec -> Sparrow_cil.location -> node -> t -> node * t =
 fun fundecl loc node g ->
  let new_node = Node.make () in
  let cmd = Cmd.Cfalloc ((Var fundecl.svar, NoOffset), fundecl, loc) in
  let g = add_edge node new_node (add_cmd new_node cmd g) in
  (new_node, g)

let generate_cmd_args :
    Sparrow_cil.fundec -> Sparrow_cil.location -> t -> node * t =
 fun fd loc g ->
  let argc, argv =
    ( (Sparrow_cil.Var (List.nth fd.sformals 0), Sparrow_cil.NoOffset),
      (Sparrow_cil.Var (List.nth fd.sformals 1), Sparrow_cil.NoOffset) )
  in
  let arg_node = Node.make () in
  let arg_cmd =
    Cmd.Ccall
      ( None,
        Sparrow_cil.Lval
          ( Sparrow_cil.Var
              (Sparrow_cil.makeGlobalVar "sparrow_arg" Sparrow_cil.voidType),
            Sparrow_cil.NoOffset ),
        [ Sparrow_cil.Lval argc; Sparrow_cil.Lval argv ],
        loc )
  in

  let optind, optarg =
    ( ( Sparrow_cil.Var (Sparrow_cil.makeGlobalVar "optind" Sparrow_cil.intType),
        Sparrow_cil.NoOffset ),
      ( Sparrow_cil.Var
          (Sparrow_cil.makeGlobalVar "optarg" Sparrow_cil.charPtrType),
        Sparrow_cil.NoOffset ) )
  in
  let opt_node = Node.make () in
  let opt_cmd =
    Cmd.Ccall
      ( None,
        Sparrow_cil.Lval
          ( Sparrow_cil.Var
              (Sparrow_cil.makeGlobalVar "sparrow_opt" Sparrow_cil.voidType),
            Sparrow_cil.NoOffset ),
        [ Sparrow_cil.Lval optind; Sparrow_cil.Lval optarg ],
        loc )
  in
  let g =
    g |> add_cmd arg_node arg_cmd |> add_cmd opt_node opt_cmd
    |> add_edge Node.ENTRY arg_node
    |> add_edge arg_node opt_node
  in
  (opt_node, g)

let init : Sparrow_cil.fundec -> Sparrow_cil.location -> t =
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
  let g = add_edge term entry g in
  let nodes = nodesof g in
  let lasts = List.filter (fun n -> succ n g = []) nodes in
  g
  |> list_fold (fun last -> add_edge last Node.EXIT) lasts
  |> generate_assumes |> flatten_instructions |> remove_if_loop
  |> transform_allocs fd (* generate alloc cmds for dynamic allocations *)
  |> transform_string_allocs fd (* generate salloc (string alloc) cmds *)
  |> remove_empty_nodes |> insert_return_nodes |> insert_return_before_exit

(* [defined_extern_storage = false] (the whole program): an [extern]
   declaration of a variable the program defines gets no storage of its own.
   C gives storage and zero initialization to definitions and tentative
   definitions only; the definition's own construction provides them.  A
   variable declared but never defined keeps the declaration's storage.  A
   translation unit alone keeps every declaration's construction.

   The whole program also constructs the storage of every definition before
   the rest of the chain.  C gives
   every object of static duration its storage before any initializer runs,
   and an initializer reads that storage when it takes the address of a
   field or an element, or lets an array decay ([&s.f], [&a[i]], [a]).
   Without its own declaration storage, a use in an earlier unit than the
   defining one would otherwise read nothing, and the result would depend on
   the order of the units.  The storage of a definition is what its
   declaration alone would construct ([process_gvardecl]); the initializer
   ([process_init]) keeps its place.  A translation unit alone keeps one
   pass: every use there follows a declaration with storage.

   The whole program also constructs every variable once.  C gives an
   object one storage and one initialization: its initialized definition's
   (a tentative definition contributes zero initialization only when no
   initialized definition exists).  The CIL merge keeps a tentative
   definition that comes first in the merge order and also the later
   initialized definition of the same variable, and both items then carry
   the shared varinfo's initializer (mergecil pass 2, [renameVisitor#vglob]);
   a later tentative definition, or a tentative definition after the
   initialized one, is dropped.  A translation unit keeps one definition of
   a variable (cabs2cil turns the others into declarations), so several
   definitions of one variable in the whole program are exactly this case:
   the first is the tentative definition and the second the initialized
   one.  Only the initialized definition constructs the variable (storage
   and initializer, at its own position); the tentative definition
   constructs nothing, as a declaration of a defined variable.  Further
   definitions repeat an initialized definition (invalid C) and construct
   nothing either. *)
let generate_global_chain ?(defined_extern_storage = true) globals fd =
  let defined =
    if defined_extern_storage then fun _ -> false
    else begin
      let names = Hashtbl.create 257 in
      List.iter
        (function
          | Sparrow_cil.GVar (variable, _, _) ->
              Hashtbl.replace names variable.Sparrow_cil.vname ()
          | _ -> ())
        globals;
      fun (variable : Sparrow_cil.varinfo) -> Hashtbl.mem names variable.vname
    end
  in
  (* the definition (global index) that constructs a variable defined more
     than once in the whole program: the second, its initialized definition *)
  let constructing =
    let table = Hashtbl.create 17 in
    if not defined_extern_storage then begin
      let occurrences = Hashtbl.create 257 in
      List.iteri
        (fun index global ->
          match global with
          | Sparrow_cil.GVar (variable, _, _) ->
              let name = variable.Sparrow_cil.vname in
              let count =
                Option.value (Hashtbl.find_opt occurrences name) ~default:0
              in
              Hashtbl.replace occurrences name (count + 1);
              if count = 1 then Hashtbl.replace table name index
          | _ -> ())
        globals
    end;
    table
  in
  let constructs (variable : Sparrow_cil.varinfo) gidx =
    match Hashtbl.find_opt constructing variable.vname with
    | None -> true
    | Some index -> index = gidx
  in
  (* (global, its index), in chain order *)
  let items = List.mapi (fun gidx global -> (global, gidx)) globals in
  let emit build (node, g) = build node g in
  (* the storage a definition constructs: none for a single initializer *)
  let definition_storage variable initinfo location =
    match initinfo.init with
    | None | Some (CompoundInit _) ->
        Some
          (fun node g ->
            process_gvardecl fd (Sparrow_cil.var variable) location node g)
    | Some (SingleInit _) -> None
  in
  let definition_initializer variable initinfo location =
    match initinfo.init with
    | None -> None
    | Some init ->
        Some
          (fun node g ->
            process_init fd (Sparrow_cil.var variable) init location node g)
  in
  let storage_first = not defined_extern_storage in
  let start = (Node.ENTRY, empty fd) in
  let start =
    if not storage_first then start
    else
      List.fold_left
        (fun acc (global, gidx) ->
          match global with
          | Sparrow_cil.GVar (variable, _, _)
            when not (constructs variable gidx) ->
              acc
          | Sparrow_cil.GVar (variable, initinfo, location) -> (
              match definition_storage variable initinfo location with
              | Some build -> emit build acc
              | None -> acc)
          | _ -> acc)
        start items
  in
  List.fold_left
    (fun acc (global, gidx) ->
      match global with
      | Sparrow_cil.GVar (variable, _, _) when not (constructs variable gidx) ->
          acc
      | Sparrow_cil.GVar (variable, initinfo, location) -> (
          let acc =
            if storage_first then acc
            else
              match definition_storage variable initinfo location with
              | Some build -> emit build acc
              | None -> acc
          in
          match definition_initializer variable initinfo location with
          | Some build -> emit build acc
          | None -> acc)
      | Sparrow_cil.GVarDecl (variable, _) when defined variable -> acc
      | Sparrow_cil.GVarDecl (variable, location) ->
          emit
            (fun node g ->
              process_gvardecl fd (Sparrow_cil.var variable) location node g)
            acc
      | Sparrow_cil.GFun (function_, location) ->
          emit (fun node g -> process_fundecl function_ location node g) acc
      | Sparrow_cil.GType _ | Sparrow_cil.GCompTag _
      | Sparrow_cil.GCompTagDecl _ | Sparrow_cil.GEnumTag _
      | Sparrow_cil.GEnumTagDecl _ | Sparrow_cil.GAsm _ | Sparrow_cil.GPragma _
      | Sparrow_cil.GText _ ->
          acc)
    start items

let generate_global_proc : Sparrow_cil.global list -> Sparrow_cil.fundec -> t =
 fun globals fd ->
  let term, g =
    generate_global_chain ~defined_extern_storage:false globals fd
  in
  let finish g =
    g |> generate_assumes |> flatten_instructions |> remove_if_loop
    |> transform_string_allocs fd (* generate salloc (string alloc) cmds *)
    |> remove_empty_nodes |> insert_return_nodes
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
  |> finish

let generate_module_global_proc :
    Sparrow_cil.global list -> Sparrow_cil.fundec -> t =
 fun globals fd ->
  let term, g = generate_global_chain globals fd in
  g |> add_edge term Node.EXIT |> generate_assumes |> flatten_instructions
  |> remove_if_loop |> transform_string_allocs fd |> remove_empty_nodes
  |> insert_return_nodes

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
  let replacement = List.hd vl in
  { g with graph = Merge.merge_vertex g.graph vl }
  |> remove_edge replacement replacement

let rec collect g n lval node_list exp_list =
  match succ n g with
  | [ s ] -> (
      match (find_cmd n g, find_cmd s g) with
      | Cmd.Csalloc (_, str, _), Cmd.Cset (l, e, _) ->
          begin match Sparrow_cil.removeOffsetLval l with
          | l, Sparrow_cil.Index (i, Sparrow_cil.NoOffset)
            when CilHelper.eq_lval lval l && Sparrow_cil.isConstant i ->
              let node_list, exp_list =
                (n :: s :: node_list, Sparrow_cil.mkString str :: exp_list)
              in
              let ss = succ s g in
              if List.length ss = 1 then
                collect g (List.hd ss) lval node_list exp_list
              else (node_list, exp_list)
          | _ -> (node_list, exp_list)
          end
      | Cmd.Cset (l, e, _), _ when Sparrow_cil.isConstant e ->
          begin match Sparrow_cil.removeOffsetLval l with
          | l, Sparrow_cil.Index (i, Sparrow_cil.NoOffset)
            when CilHelper.eq_lval lval l && Sparrow_cil.isConstant i ->
              let node_list, exp_list = (n :: node_list, e :: exp_list) in
              let ss = succ n g in
              if List.length ss = 1 then
                collect g (List.hd ss) lval node_list exp_list
              else (node_list, exp_list)
          | _ -> (node_list, exp_list)
          end
      | _ -> (node_list, exp_list))
  | _ -> (node_list, exp_list)

let is_candidate n g =
  let is_starting_point lval =
    match Sparrow_cil.removeOffsetLval lval with
    | l, Sparrow_cil.Index (i, Sparrow_cil.NoOffset) when Sparrow_cil.isZero i
      ->
        Some l
    | _ -> None
  in
  let ss = try succ n g with _ -> [] in
  if List.length ss = 1 then
    let s = List.hd ss in
    match (find_cmd n g, find_cmd s g) with
    | Cmd.Csalloc (_, _, _), Cmd.Cset (lval, e, _)
      when Sparrow_cil.isPointerType (Sparrow_cil.typeOf e) ->
        is_starting_point lval
    | Cmd.Cset (lval, e, _), _
      when Sparrow_cil.isIntegralType (Sparrow_cil.typeOf e) ->
        is_starting_point lval
    | _ -> None
  else None

(* arr[0] = c0; arr[1] = c1; ..., arr[n] = cn; => sparrow_array_init(arr,c0, c1, ..., cn);
   salloc(arr[0], x0); x0 = s0; ..., => sparrow_array_init(arr, s0, s1, ..., sn) *)
let rec make_replacement_node g replaced =
  let node = Node.make () in
  if G.mem_vertex g.graph node && not (List.mem node replaced) then
    make_replacement_node g replaced
  else node

let optimize_array_init_with make_node : t -> t =
 fun g ->
  fold_node
    (fun n g ->
      match is_candidate n g with
      | Some lval ->
          let nodes, exps = collect g n lval [] [] in
          if List.length nodes > 1 then
            let new_node = make_node g nodes in
            let g = merge_vertex g (new_node :: nodes) in
            let args = Sparrow_cil.Lval lval :: List.rev exps in
            let loc = find_cmd n g |> Cmd.location_of in
            let cmd =
              Cmd.Ccall
                ( None,
                  Sparrow_cil.Lval
                    ( Sparrow_cil.Var
                        (Sparrow_cil.makeGlobalVar "sparrow_array_init"
                           Sparrow_cil.voidType),
                      Sparrow_cil.NoOffset ),
                  args,
                  loc )
            in
            add_cmd new_node cmd g
          else g
      | _ -> g)
    g g

let collision_safe_global_replacement = ref false

let with_collision_safe_global_replacement f =
  let previous = !collision_safe_global_replacement in
  collision_safe_global_replacement := true;
  Fun.protect
    ~finally:(fun () -> collision_safe_global_replacement := previous)
    f

let optimize g =
  let optimize_array_init =
    if !collision_safe_global_replacement && get_pid g = "_G_" then
      optimize_array_init_with make_replacement_node
    else optimize_array_init_with (fun _ _ -> Node.make ())
  in
  optimize_array_init g

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
