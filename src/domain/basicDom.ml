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
(** Abstract Domain *)

open Vocab
open InterCfg

module Node = InterCfg.Node
module PowNode = PowDom.MakeCPO(Node)
module Proc = InterCfg.Proc
module PowProc = PowDom.MakeCPO(Proc)

module ExtAllocsite =
struct
  type t = Input | Unknown of string [@@deriving compare]

  let input = Input
  let unknown s = Unknown s
  let is_cmd_arg x =
    match x with
      Unknown s -> s = "arg"
    | _ -> false
  let to_string = function
    | Input -> "__extern__"
    | Unknown s -> "__extern__" ^ s
  let pp fmt x = Format.fprintf fmt "%s" (to_string x)
end

module IntAllocsite =
struct
  type t = Node.t * is_string [@@deriving compare]
  and is_string = bool

  let to_string (node,_) = Node.to_string node
  let pp fmt x = Format.fprintf fmt "%s" (to_string x)
end

module Allocsite =
struct
  type t = Internal of IntAllocsite.t | External of ExtAllocsite.t [@@deriving compare]
  let allocsite_of_node : Node.t -> t
  = fun n -> Internal (n,false)
  let allocsite_of_string : Node.t -> t
  = fun n -> Internal (n,true)

  let is_node_allocsite = function Internal (_,false) -> true | _ -> false
  let is_string_allocsite = function Internal (_,true) -> true | _ -> false
  let is_ext_allocsite = function External _ -> true | _ -> false
  (* the node of an internal allocation site *)
  let internal_node = function Internal (n, is_string) -> Some (n, is_string) | External _ -> None
  let is_cmd_arg = function External e -> ExtAllocsite.is_cmd_arg e | _ -> false

  let allocsite_of_ext = function
    | None -> External (ExtAllocsite.input)
    | Some fid -> External (ExtAllocsite.unknown fid)

  let to_string = function
    | Internal i -> IntAllocsite.to_string i
    | External e -> ExtAllocsite.to_string e

  let pp fmt = function
    | Internal i -> Format.fprintf fmt "%a" IntAllocsite.pp i
    | External e -> Format.fprintf fmt "%a" ExtAllocsite.pp e
end

(* [Sparrow_cil.typeSig] of field types, remembered per physical type.  When
   values are decoded from separately marshaled data, [Loc.compare] meets
   physically different types with equal signatures and would compute both
   signatures each time.  An entry keeps, besides the signature, the
   mutable fields [typeSig] read (composite name, kind and attributes, enum
   name, typedef target), in its walk order, and is used only while each of
   them is still physically the same; otherwise, and for the types whose
   signature reads anything else (an array length that is not an integer
   constant, an attribute that carries a type), the signature is computed as
   before.  The table is a small set-associative cache of ephemerons: it
   keeps neither a type nor its signature alive. *)
module Field_type_signature =
struct
  module C = Sparrow_cil

  exception Unmemoizable

  let rec plain_param = function
    | C.AInt _ | C.AStr _ -> ()
    | C.ACons (_, params) -> List.iter plain_param params
    | C.ASizeOfE p | C.AAlignOfE p | C.AUnOp (_, p) | C.ADot (p, _) | C.AStar p | C.AAddrOf p ->
      plain_param p
    | C.ABinOp (_, p, q) | C.AIndex (p, q) | C.AAssign (p, q) -> plain_param p; plain_param q
    | C.AQuestion (p, q, r) -> plain_param p; plain_param q; plain_param r
    | C.ASizeOf _ | C.ASizeOfS _ | C.AAlignOf _ | C.AAlignOfS _ -> raise_notrace Unmemoizable

  let plain_attributes attributes =
    List.iter (fun (C.Attr (_, params)) -> List.iter plain_param params) attributes

  let plain_length = function
    | None | Some (C.Const (C.CInt _)) -> ()
    | Some _ -> raise_notrace Unmemoizable

  (* The mutable fields [typeSigWithAttrs] reads, in reverse walk order. *)
  let rec reads acc = function
    | C.TInt (_, a) | C.TFloat (_, a) | C.TVoid a | C.TBuiltin_va_list a -> plain_attributes a; acc
    | C.TEnum (e, a) -> plain_attributes a; Obj.repr e.C.ename :: acc
    | C.TPtr (t, a) -> plain_attributes a; reads acc t
    | C.TArray (t, l, a) -> plain_length l; plain_attributes a; reads acc t
    | C.TComp (c, a) ->
      plain_attributes a; plain_attributes c.C.cattr;
      Obj.repr c.C.cattr :: Obj.repr c.C.cname :: Obj.repr c.C.cstruct :: acc
    | C.TFun (r, args, _, a) ->
      plain_attributes a;
      let acc = reads acc r in
      (match args with
       | None -> acc
       | Some args -> List.fold_left (fun acc (_, t, _) -> reads acc t) acc args)
    | C.TNamed (info, a) -> plain_attributes a; reads (Obj.repr info.C.ttype :: acc) info.C.ttype

  (* [true] when the fields read now are physically those of [snapshot]. *)
  let unchanged snapshot t =
    let position = ref 0 in
    let same value =
      let i = !position in
      if i >= Array.length snapshot || Array.unsafe_get snapshot i != value then raise_notrace Exit;
      position := i + 1 in
    let rec walk = function
      | C.TInt _ | C.TFloat _ | C.TVoid _ | C.TBuiltin_va_list _ -> ()
      | C.TEnum (e, _) -> same (Obj.repr e.C.ename)
      | C.TPtr (t, _) | C.TArray (t, _, _) -> walk t
      | C.TComp (c, _) ->
        same (Obj.repr c.C.cstruct); same (Obj.repr c.C.cname); same (Obj.repr c.C.cattr)
      | C.TFun (r, args, _, _) ->
        walk r; (match args with None -> () | Some args -> List.iter (fun (_, t, _) -> walk t) args)
      | C.TNamed (info, _) -> same (Obj.repr info.C.ttype); walk info.C.ttype in
    try walk t; !position = Array.length snapshot with Exit -> false

  (* A slot index from the type's outer constructors (any function of the
     type would do: a key is matched physically). *)
  let rec index depth = function
    | C.TInt (k, _) -> Hashtbl.hash k
    | C.TFloat (k, _) -> 0x51 + Hashtbl.hash k
    | C.TVoid _ -> 0x13
    | C.TBuiltin_va_list _ -> 0x17
    | C.TEnum (e, _) -> Hashtbl.hash e.C.ename
    | C.TComp (c, _) -> Hashtbl.hash c.C.cname
    | C.TNamed (info, _) -> Hashtbl.hash info.C.tname
    | C.TPtr (t, _) -> if depth = 0 then 0x29 else 31 * index (depth - 1) t + 0x29
    | C.TArray (t, _, _) -> if depth = 0 then 0x2b else 31 * index (depth - 1) t + 0x2b
    | C.TFun (r, _, _, _) -> if depth = 0 then 0x2f else 31 * index (depth - 1) r + 0x2f

  type entry = (C.typ, Obj.t array * C.typsig) Ephemeron.K1.t

  let ways = 4
  let sets = 1024
  let table : entry array = Array.init (ways * sets) (fun _ -> Ephemeron.K1.create ())
  let next = Array.make sets 0

  let compute t =
    let base = (index 3 t land (sets - 1)) * ways in
    let rec find way =
      if way = ways then None
      else
        let entry = Array.unsafe_get table (base + way) in
        match Ephemeron.K1.get_key entry with
        | Some key when key == t -> (
            match Ephemeron.K1.get_data entry with
            | Some (snapshot, signature) when unchanged snapshot t -> Some signature
            | _ -> None)
        | _ -> find (way + 1) in
    match find 0 with
    | Some signature -> signature
    | None ->
      let signature = C.typeSig t in
      (match reads [] t with
       | acc ->
         let set = base / ways in
         let way = next.(set) in
         let entry = table.(base + way) in
         Ephemeron.K1.set_key entry t;
         Ephemeron.K1.set_data entry (Array.of_list (List.rev acc), signature);
         next.(set) <- (way + 1) mod ways
       | exception Unmemoizable -> ());
      signature
end

module Loc =
struct
  type t = GVar of string * Sparrow_cil.typ | LVar of Proc.t * string * Sparrow_cil.typ
         | Allocsite of Allocsite.t | Field of t * field * Sparrow_cil.typ
  and field = string

  let rec compare x y =
    if x == y then 0 else
    match x, y with
    | GVar (g1, _), GVar (g2, _) -> String.compare g1 g2
    | LVar (p1, l1, _), LVar (p2, l2, _) ->
      let c = Proc.compare p1 p2 in
      if c = 0 then String.compare l1 l2 else c
    | Allocsite a1, Allocsite a2 -> Allocsite.compare a1 a2
    | Field (l1, f1, t1), Field (l2, f2, t2) ->
      (* Upstream's key: base, field name, then the field type's signature.
         Physically equal types have equal signatures, so the shortcut only
         skips the signature computation. *)
      let c = compare l1 l2 in
      if c = 0 then
        let c = String.compare f1 f2 in
        if c = 0 then
          if t1 == t2 then 0
          else
            Stdlib.compare (Field_type_signature.compute t1) (Field_type_signature.compute t2)
        else c
      else c
    | _, _ -> Stdlib.compare (tag_of_t x) (tag_of_t y)
  and tag_of_t = function GVar _ -> 0 | LVar _ -> 1 | Allocsite _ -> 2 | Field _ -> 3

  let typ = function GVar (_, t) | LVar (_, _, t) | Field (_, _, t) -> Some t | _ -> None

  (* The identity of a type as [compare] sees it on a field: its signature
     marshaled without sharing (acyclic: composites by name, attribute types
     as signatures; no floats), in hex, so two types have equal keys iff
     [Stdlib.compare] of their signatures is 0. *)
  let type_key t =
    let raw = Marshal.to_string (Sparrow_cil.typeSig t) [ Marshal.No_sharing ] in
    let digits = "0123456789abcdef" in
    String.init (2 * String.length raw) (fun i ->
        let c = Char.code raw.[i / 2] in
        digits.[if i land 1 = 0 then c lsr 4 else c land 15])

  let rec to_string = function
    | GVar (g, _) -> g
    | LVar (p, x, _) -> "(" ^ Proc.to_string p ^ "," ^ x ^ ")"
    | Allocsite a -> Allocsite.to_string a
    | Field (a, f, _) -> to_string a ^ "." ^ f

  let pp fmt x = Format.fprintf fmt "%s" (to_string x)

  let dummy = GVar ("__dummy__", Sparrow_cil.voidType)
  let null = GVar ("NULL", Sparrow_cil.voidPtrType)

  let is_null x = (x = null)
  let is_var : t -> bool = function
    | GVar _ | LVar _ -> true
    | _ -> false

  let is_gvar : t -> bool = function
    | GVar _ -> true
    | _ -> false

  let is_lvar : t -> bool = function
    | LVar _ -> true
    | _ -> false

  let is_allocsite : t -> bool = function
    | Allocsite _ -> true
    | _ -> false

  let is_string_allocsite : t -> bool = function
    | Allocsite a -> Allocsite.is_string_allocsite a
    | _ -> false

  let is_ext_allocsite : t -> bool = function
    | Allocsite a -> Allocsite.is_ext_allocsite a
    | _ -> false

  let is_field : t -> bool = function
    | Field _ -> true
    | _ -> false

  let is_local_of : Proc.t -> t -> bool = fun p x ->
    match x with
    | LVar (p',_,_) -> p = p'
    | _ -> false

  let get_proc : t -> Proc.t
  = function LVar (p, _, _) -> p | _ -> raise Not_found

  let of_gvar x typ = GVar (x,typ)
  let of_lvar p x typ = LVar (p,x,typ)
  let of_allocsite : Allocsite.t -> t = fun x -> Allocsite x
  let return_var pid typ = LVar (pid, "__return__", typ)

  (* A field location is identified by its base, its name and the signature
     of its type ([compare]); the type's spelling beyond its signature
     (typedef names) is data, and a [PowLoc] keeps whichever spelling was
     inserted first.  The constructor installs the type the caller passes. *)
  let append_field x f typ = Field (x,f,typ)

  (* Representation identity (HashconsKey).  Two locations are
     interchangeable only when they carry the SAME physical type (finer than
     [compare], which equates types of one signature).  The type is never
     traversed: it may be cyclic, and separately marshaled values carry
     their own copies. *)
  let rec rep_equal x y =
    x == y ||
    match x, y with
    | GVar (g1, t1), GVar (g2, t2) -> t1 == t2 && String.equal g1 g2
    | LVar (p1, l1, t1), LVar (p2, l2, t2) ->
      t1 == t2 && String.equal l1 l2 && String.equal p1 p2
    | Allocsite a1, Allocsite a2 -> Allocsite.compare a1 a2 = 0
    | Field (b1, f1, t1), Field (b2, f2, t2) ->
      t1 == t2 && String.equal f1 f2 && rep_equal b1 b2
    | _, _ -> false

  (* Names only; consistent with [rep_equal], which also requires them. *)
  let rec rep_hash = function
    | GVar (g, _) -> Hashtbl.hash g
    | LVar (p, l, _) -> HashconsKey.mix (Hashtbl.hash p) (Hashtbl.hash l)
    | Allocsite a -> HashconsKey.mix 2 (Hashtbl.hash a)
    | Field (b, f, _) -> HashconsKey.mix (rep_hash b) (Hashtbl.hash f)

  (* Before any domain functor is applied to [Loc]. *)
  let () = HashconsKey.register compare { HashconsKey.equal = rep_equal; hash = rep_hash }
end

module PowLoc =
struct
  include PowDom.MakeCPO (Loc)

  let prune op x e =
    match op with
      Sparrow_cil.Eq when Sparrow_cil.isZero e -> singleton Loc.null
    | Sparrow_cil.Ne when Sparrow_cil.isZero e -> remove Loc.null x
    | _ -> x
  let null = singleton Loc.null
  let append_field : t -> Sparrow_cil.fieldinfo -> t = fun ls f ->
    let add_appended l acc =
      if Loc.is_ext_allocsite l then add l acc
      else if Loc.is_null l || Loc.is_string_allocsite l then acc
      else add (Loc.append_field l f.Sparrow_cil.fname f.Sparrow_cil.ftype) acc
    in
    fold add_appended ls bot
end

module Dump = MapDom.MakeCPO (Proc) (PowLoc)
