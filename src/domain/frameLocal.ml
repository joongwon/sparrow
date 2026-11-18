(* Frame locals of recursive procedures.

   A location is a frame local of a recursive procedure p when its root is
   p's own: a variable (p, x) of p that no call node binds (not a formal of p;
   a call binds the callee's formals) and is not p's return variable, or the
   site of an allocation in p (a heap object, a local array or struct, a
   string); and
     - only p's nodes access it (it is in p's proc-local set),
     - every value of the pre-analysis memory that points to it or into it
       (to the root or one of its fields) is held in a frame local of p.
   The set is the greatest one with these properties.  A frame's copy of such
   a location is reached only through pointers in that frame: a new frame's
   copy is uninitialised (or newly allocated) at entry, no callee and no
   other frame can change the current frame's copy, and the copy is dead
   when the frame returns.  So the location leaves every call edge (call ->
   entry, exit -> return, and the recursive return's use), and an
   assignment to a frame-local variable may update strongly: the abstract
   value at a point of p describes only the frame executing there.

   The set is computed after the access analysis and before the def-use
   graph (SsaDug.make); the access analysis runs without it ([without]), so
   it records the same accesses as without frame locals. *)

open BasicDom

let rec root = function Loc.Field (l, _, _) -> root l | l -> l

(* The procedure and name of the variable a location is rooted at. *)
let variable loc = match root loc with Loc.LVar (p, x, _) -> Some (p, x) | _ -> None

let current = ref PowLoc.empty
let suspended = ref 0

let mem loc = !suspended = 0 && PowLoc.mem loc !current

let without f =
  incr suspended;
  match f () with
  | result -> decr suspended; result
  | exception e -> decr suspended; raise e

let set locations = current := locations

let locations () = !current

let compute ~(memory : ItvDom.Mem.t) ~(calls : (string list * PowLoc.t) list)
    ~(recursive_locals : (string * PowLoc.t) list) =
  let formal = Hashtbl.create 256 in
  List.iter
    (fun (callees, defs) ->
      PowLoc.iter
        (fun loc ->
          match root loc with
          | Loc.LVar (p, x, _) when List.mem p callees -> Hashtbl.replace formal (p, x) ()
          | _ -> ())
        defs)
    calls;
  (* The procedure a root is own to. *)
  let owner = function
    | Loc.LVar (p, x, _) when x <> "__return__" && not (Hashtbl.mem formal (p, x)) -> Some p
    | Loc.Allocsite a -> Option.map (fun (node, _) -> Node.get_pid node) (Allocsite.internal_node a)
    | _ -> None
  in
  (* The candidates: the roots of the recursive procedures' proc-locals own to the procedure. *)
  let candidate = Hashtbl.create 1024 in
  List.iter
    (fun (pid, locals) ->
      PowLoc.iter (fun loc -> let r = root loc in if owner r = Some pid then Hashtbl.replace candidate r pid) locals)
    recursive_locals;
  (* The candidates each root's value points to ([held]); a candidate pointed to from a root that
     is not a candidate of the same procedure leaves at once, and when a candidate leaves, so do
     the candidates its value points to. *)
  let held = Hashtbl.create 1024 and out = Queue.create () in
  let note holder target =
    let t = root target in
    match Hashtbl.find_opt candidate t with
    | None -> ()
    | Some pid ->
        if Hashtbl.find_opt candidate holder = Some pid then Hashtbl.add held holder t
        else Queue.add t out
  in
  ItvDom.Mem.iter
    (fun loc value ->
      let holder = root loc in
      PowLoc.iter (note holder) (ItvDom.Val.pow_loc_of_val value);
      PowLoc.iter (note holder) (ArrayBlk.pow_loc_of_array (ItvDom.Val.array_of_val value));
      StructBlk.iter (fun l _ -> note holder l) (ItvDom.Val.struct_of_val value))
    memory;
  while not (Queue.is_empty out) do
    let r = Queue.take out in
    if Hashtbl.mem candidate r then begin
      Hashtbl.remove candidate r;
      List.iter (fun t -> Queue.add t out) (Hashtbl.find_all held r)
    end
  done;
  List.fold_left
    (fun found (_, locals) ->
      PowLoc.union found (PowLoc.filter (fun loc -> Hashtbl.mem candidate (root loc)) locals))
    PowLoc.empty recursive_locals
