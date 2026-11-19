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
(* Canonical traversal order of the sparse fixpoint (DUG weak topological
   order and worklist priority), a function of each translation unit's own
   nodes.

   Every DUG node carries a key (module, procedure, position).  The nodes are
   numbered by ascending key and every choice the decomposition makes is a
   function of those numbers: the strongly connected components are found by
   visiting vertices and successors in ascending number, a component's head is
   its entry with the most predecessors inside the component and, on a tie,
   the smallest number, and the worklist breaks order ties by the number.
   Nothing depends on the iteration order of a hash table or on a merged
   program's internal names. *)

type position = Entry | Exit | Body of int
type key = { module_id : string; procedure : string; position : position }

let compare_position a b =
  match (a, b) with
  | Entry, Entry | Exit, Exit -> 0
  | Entry, _ -> -1
  | _, Entry -> 1
  | Exit, _ -> -1
  | _, Exit -> 1
  | Body x, Body y -> Int.compare x y

let compare_key a b =
  let c = String.compare a.module_id b.module_id in
  if c <> 0 then c
  else
    let c = String.compare a.procedure b.procedure in
    if c <> 0 then c else compare_position a.position b.position

let position_of_cfgnode n =
  if IntraCfg.is_entry n then Entry
  else if IntraCfg.is_exit n then Exit
  else Body (IntraCfg.Node.id n)

let string_of_position = function
  | Entry -> "ENTRY"
  | Exit -> "EXIT"
  | Body i -> string_of_int i

let string_of_key k =
  Printf.sprintf "%s:%s-%s" k.module_id k.procedure
    (string_of_position k.position)

(* The structural ordinal of a CFG's nodes: breadth-first from ENTRY, each
   node's successors in node-id order, then the unreached nodes in node-id
   order; ENTRY and EXIT have none.  A function of the CFG of one translation
   unit alone, so a unit built alone and the whole program (through its TU
   correspondence) give a node the same ordinal.  It
   is the position component of a body node's key. *)
let structural_ordinals (cfg : IntraCfg.t) : (IntraCfg.Node.t, int) Hashtbl.t =
  let table = Hashtbl.create 64 in
  let next = ref 0 in
  let assign node =
    if not (Hashtbl.mem table node) then begin
      Hashtbl.replace table node !next;
      incr next
    end
  in
  let is_sentinel n = IntraCfg.is_entry n || IntraCfg.is_exit n in
  let by_id a b = compare (IntraCfg.Node.id a) (IntraCfg.Node.id b) in
  let visited = Hashtbl.create 64 in
  let queue = Queue.create () in
  Queue.add IntraCfg.Node.entry queue;
  Hashtbl.replace visited IntraCfg.Node.entry ();
  while not (Queue.is_empty queue) do
    let node = Queue.take queue in
    if not (is_sentinel node) then assign node;
    List.iter
      (fun s ->
        if not (Hashtbl.mem visited s) then begin
          Hashtbl.replace visited s ();
          Queue.add s queue
        end)
      (List.sort by_id (IntraCfg.succ node cfg))
  done;
  IntraCfg.nodesof cfg
  |> List.filter (fun n -> (not (is_sentinel n)) && not (Hashtbl.mem table n))
  |> List.sort by_id |> List.iter assign;
  table

(* Without a program-level naming (a single-TU run) the key is the node's
   own name. *)
let default_key node =
  {
    module_id = "";
    procedure = InterCfg.Node.get_pid node;
    position = position_of_cfgnode (InterCfg.Node.get_cfgnode node);
  }

(* The key of a node: its procedure and its position in its CFG. *)
let key_of = default_key

(* ------------------------------------------------------------------ *)
(* Decomposition kernel over vertices 0..n-1 numbered in key order.     *)

type t = {
  succ : int array array;
  pred : int array array;
  mark_self : int array;
  mark_parent : int array;
  root : int array;
  root_gen : int array;
  comp : int array;
  comp_gen : int array;
  frame_vertex : int array;
  frame_next : int array;
  frame_child : int array;
  frame_number : int array;
  stack_number : int array;
  stack_vertex : int array;
  mutable stamp : int;
}

let make n succ =
  let degrees = Array.make n 0 in
  Array.iter (Array.iter (fun w -> degrees.(w) <- degrees.(w) + 1)) succ;
  let pred = Array.map (fun degree -> Array.make degree 0) degrees in
  Array.fill degrees 0 n 0;
  Array.iteri
    (fun v row ->
      Array.iter
        (fun w ->
          let i = degrees.(w) in
          pred.(w).(i) <- v;
          degrees.(w) <- i + 1)
        row)
    succ;
  let capacity = max 16 n in
  {
    succ;
    pred;
    mark_self = Array.make n (-1);
    mark_parent = Array.make n (-1);
    root = Array.make n 0;
    root_gen = Array.make n (-1);
    comp = Array.make n 0;
    comp_gen = Array.make n (-1);
    frame_vertex = Array.make capacity 0;
    frame_next = Array.make capacity 0;
    frame_child = Array.make capacity 0;
    frame_number = Array.make capacity 0;
    stack_number = Array.make n 0;
    stack_vertex = Array.make n 0;
    stamp = 0;
  }

let fresh t =
  t.stamp <- t.stamp + 1;
  t.stamp

(* Tarjan's components of the subgraph on [members] whose vertices satisfy
   [inside], without the edges into [cut].  Roots are tried in member order
   ([descending] reverses it) and successors in descending order (the last
   successor is visited first), which is ocamlgraph's [Components.scc] on a
   graph enumerated in ascending order.  Components come out in completion
   order (reverse topological), each in descending vertex order. *)
let components_of t ~descending members inside cut =
  let gen = fresh t in
  let numdfs = ref 0
  and numcomp = ref 0
  and stack_size = ref 0
  and frame_size = ref 0 in
  let visit v =
    if t.root_gen.(v) <> gen then begin
      incr numdfs;
      t.root_gen.(v) <- gen;
      t.root.(v) <- !numdfs;
      let i = !frame_size in
      t.frame_vertex.(i) <- v;
      t.frame_number.(i) <- !numdfs;
      t.frame_next.(i) <- Array.length t.succ.(v) - 1;
      t.frame_child.(i) <- -1;
      incr frame_size
    end
  in
  let finish () =
    while !frame_size > 0 do
      let i = !frame_size - 1 in
      let v = t.frame_vertex.(i) and child = t.frame_child.(i) in
      if child >= 0 then begin
        t.frame_child.(i) <- -1;
        if t.comp_gen.(child) <> gen then
          t.root.(v) <- min t.root.(v) t.root.(child)
      end
      else if t.frame_next.(i) >= 0 then begin
        let w = t.succ.(v).(t.frame_next.(i)) in
        t.frame_next.(i) <- t.frame_next.(i) - 1;
        if inside w && w <> cut then begin
          t.frame_child.(i) <- w;
          visit w
        end
      end
      else begin
        decr frame_size;
        let number = t.frame_number.(i) in
        if t.root.(v) = number then begin
          t.comp_gen.(v) <- gen;
          t.comp.(v) <- !numcomp;
          while !stack_size > 0 && t.stack_number.(!stack_size - 1) > number do
            decr stack_size;
            let w = t.stack_vertex.(!stack_size) in
            t.comp_gen.(w) <- gen;
            t.comp.(w) <- !numcomp
          done;
          incr numcomp
        end
        else begin
          t.stack_number.(!stack_size) <- number;
          t.stack_vertex.(!stack_size) <- v;
          incr stack_size
        end
      end
    done
  in
  let length = Array.length members in
  let member i = members.(if descending then length - 1 - i else i) in
  for i = 0 to length - 1 do
    visit (member i);
    finish ()
  done;
  let sizes = Array.make !numcomp 0 in
  Array.iter
    (fun v ->
      let c = t.comp.(v) in
      sizes.(c) <- sizes.(c) + 1)
    members;
  let components = Array.map (fun size -> Array.make size 0) sizes in
  for i = 0 to length - 1 do
    let v = member i in
    let c = t.comp.(v) in
    sizes.(c) <- sizes.(c) - 1;
    components.(c).(sizes.(c)) <- v
  done;
  components

(* Head preference: higher score first; on a tie, a call node first when
   [call_first], then the smaller number. *)
let consider ~call_first ~is_call ((candidate, score) as entry) best =
  match best with
  | None -> Some entry
  | Some (_, previous) when score > previous -> Some entry
  | Some (chosen, previous) when score = previous ->
      let priority =
        if call_first then Bool.compare (is_call chosen) (is_call candidate)
        else 0
      in
      if priority < 0 || (priority = 0 && Int.compare candidate chosen < 0) then
        Some entry
      else best
  | _ -> best

(* The head of component [scc] (marked [self]) inside the level whose members
   carry [parent] ([None]: the whole graph).  Score = predecessors inside the
   component; candidates = members with a predecessor outside it in the
   level.  A component without an entry takes its smallest vertex. *)
(* [left_out v]: [v] has a predecessor outside the whole graph that the
   caller left out (e.g. the [_G_] ENTRY of a part analysed alone).  It
   never changes the head chosen here; at the top level a component whose
   entry candidates would differ had that predecessor been present is
   reported as entry-sensitive ([entry_sensitive]: the component, the head
   chosen, the head with the left-out entries). *)
let head ?left_out ?entry_sensitive t ~call_first ~is_call ~components ~tied scc
    self parent =
  incr components;
  let outside u =
    t.mark_self.(u) <> self
    && match parent with None -> true | Some pid -> t.mark_parent.(u) = pid
  in
  let left_out =
    match (parent, left_out) with None, Some f -> Some f | _ -> None
  in
  let best = ref None and top_score = ref (-1) and top_count = ref 0 in
  let best_ext = ref None and candidates = ref 0 and candidates_ext = ref 0 in
  Array.iter
    (fun v ->
      let inside_entry = Array.exists outside t.pred.(v) in
      let left_out_entry =
        match left_out with Some f -> f v | None -> false
      in
      if inside_entry || left_out_entry then begin
        let score = ref 0 in
        let predecessors = t.pred.(v) in
        for i = 0 to Array.length predecessors - 1 do
          if t.mark_self.(predecessors.(i)) = self then incr score
        done;
        let score = !score in
        if left_out <> None then begin
          incr candidates_ext;
          best_ext := consider ~call_first ~is_call (v, score) !best_ext
        end;
        if inside_entry then begin
          incr candidates;
          if score > !top_score then begin
            top_score := score;
            top_count := 1
          end
          else if score = !top_score then incr top_count;
          best := consider ~call_first ~is_call (v, score) !best
        end
      end)
    scc;
  let chosen =
    match !best with
    | None -> Array.fold_left min max_int scc
    | Some (vertex, _) ->
        if !top_count > 1 then incr tied;
        vertex
  in
  (match (left_out, entry_sensitive) with
  | Some _, Some sink when !candidates_ext > !candidates ->
      (* The entry candidates differ with the left-out entries: reported
          even when the head would come out the
          same (a fallback head equal to the only left-out candidate, or a
          left-out candidate that loses the score). *)
      let with_ext = match !best_ext with Some (v, _) -> v | None -> chosen in
      sink := (scc, chosen, with_ext) :: !sink
  | _ -> ());
  chosen

(* Sparrow's recursive weak topological order ([get_order1]): a component of
   size s gets head order [order + 3s]; the components after it are numbered
   from [head order + 1]; then the head's incoming edges are cut and the
   component's interior is decomposed from [order]. *)
(* Band records, O(1) per component and per vertex: every component of size
   > 1 (its enclosing component, base order, head order, size, head, depth,
   top-level position) and every vertex's innermost enclosing component. *)
type band_record = {
  rec_parent : int;
  rec_base : int;
  rec_head_order : int;
  rec_size : int;
  rec_head : int;
  rec_depth : int;
  rec_top : int;
}

let order_arrays ?left_out ?entry_sensitive t ~descending_members ~call_first
    ~is_call ~components ~tied sccs =
  let count = Array.length t.succ in
  let orders = Array.make count (-1)
  and heads = Array.make count false
  and head_orders = Array.make count (-1) in
  let owner = Array.make count (-1)
  and records = ref []
  and record_count = ref 0 in
  let reverse rows =
    let last = Array.length rows - 1 in
    for i = 0 to (Array.length rows / 2) - 1 do
      let row = rows.(i) in
      rows.(i) <- rows.(last - i);
      rows.(last - i) <- row
    done;
    rows
  in
  let rec get_order sccs offset descending parent enclosing depth order =
    if offset = Array.length sccs then order
    else
      let scc = sccs.(offset) in
      let size = Array.length scc in
      if size > 1 then begin
        let headorder = order + (3 * size) in
        let self = fresh t in
        Array.iter (fun v -> t.mark_self.(v) <- self) scc;
        let head =
          head ?left_out ?entry_sensitive t ~call_first ~is_call ~components
            ~tied scc self parent
        in
        heads.(head) <- true;
        head_orders.(head) <- headorder;
        let index = !record_count in
        incr record_count;
        records :=
          {
            rec_parent = enclosing;
            rec_base = order;
            rec_head_order = headorder;
            rec_size = size;
            rec_head = head;
            rec_depth = depth;
            rec_top = (if enclosing < 0 then offset else -1);
          }
          :: !records;
        ignore
          (get_order sccs (offset + 1) descending parent enclosing depth
             (headorder + 1));
        let pid = fresh t in
        Array.iter (fun v -> t.mark_parent.(v) <- pid) scc;
        let members =
          if descending then scc
          else begin
            let members = Array.copy scc in
            Array.sort Int.compare members;
            members
          end
        in
        let inner =
          components_of t ~descending members
            (fun w -> t.mark_parent.(w) = pid)
            head
          |> reverse
        in
        get_order inner 0 true (Some pid) index (depth + 1) order
      end
      else begin
        orders.(scc.(0)) <- order;
        owner.(scc.(0)) <- enclosing;
        get_order sccs (offset + 1) descending parent enclosing depth (order + 1)
      end
  in
  let last = get_order sccs 0 descending_members None (-1) 0 0 in
  let records = Array.of_list (List.rev !records) in
  (orders, heads, head_orders, last, owner, records)

(* A violation of the band condition: a
   top-level component's ticket interval meets the next one's, or a
   component's interior is numbered past its own head order. *)
type band_violation = {
  band_kind : [ `Overlap | `Inner_overflow ];
  band_head : int; (* the component's head (a singleton: the vertex) *)
  band_size : int;
  band_depth : int;
  band_low : int;
  band_high : int; (* interval end / interior extent *)
  band_limit : int; (* next component's first ticket / own head order *)
  band_next_head : int; (* `Overlap: the next component's head, else -1 *)
}

type decomposition = {
  orders : int array; (* every vertex *)
  heads : bool array; (* loop heads, including self-loop vertices *)
  head_orders : int array; (* -1: none *)
  top_components : int array array; (* in decomposition order *)
  component_count : int;
  tied_component_count : int;
  band_violations : band_violation list;
  (* [left_out] entries that could change a top-level head: component,
     head chosen, head with the external entries *)
  entry_sensitive : (int array * int * int) list;
}

(* The band check of one decomposition, linear in the vertices and
   components: each vertex is read once (its innermost component), each
   component once (children before parents: a component's record is made
   before any of its interior's), each top-level item once. *)
let band_check orders head_orders sccs owner (records : band_record array) =
  let n = Array.length records in
  let interior = Array.make n min_int in
  Array.iteri
    (fun v o ->
      let r = owner.(v) in
      if r >= 0 && o > interior.(r) then interior.(r) <- o)
    orders;
  let extent = Array.make n 0 in
  let violations = ref [] in
  for r = n - 1 downto 0 do
    let record = records.(r) in
    extent.(r) <- max record.rec_head_order interior.(r);
    if interior.(r) > record.rec_head_order then
      violations :=
        {
          band_kind = `Inner_overflow;
          band_head = record.rec_head;
          band_size = record.rec_size;
          band_depth = record.rec_depth;
          band_low = record.rec_base;
          band_high = interior.(r);
          band_limit = record.rec_head_order;
          band_next_head = -1;
        }
        :: !violations;
    let p = record.rec_parent in
    if p >= 0 && extent.(r) > interior.(p) then interior.(p) <- extent.(r)
  done;
  let top_record = Array.make (Array.length sccs) (-1) in
  Array.iteri
    (fun r record ->
      if record.rec_top >= 0 then top_record.(record.rec_top) <- r)
    records;
  let interval i =
    match top_record.(i) with
    | -1 ->
        let v = sccs.(i).(0) in
        (orders.(v), max orders.(v) head_orders.(v), v, 1)
    | r ->
        ( records.(r).rec_base,
          extent.(r),
          records.(r).rec_head,
          records.(r).rec_size )
  in
  for i = 0 to Array.length sccs - 2 do
    let lo, hi, h, size = interval i
    and next_lo, _, next_h, _ = interval (i + 1) in
    if next_lo <= hi then
      violations :=
        {
          band_kind = `Overlap;
          band_head = h;
          band_size = size;
          band_depth = 0;
          band_low = lo;
          band_high = hi;
          band_limit = next_lo;
          band_next_head = next_h;
        }
        :: !violations
  done;
  List.rev !violations

let string_of_band_violation name v =
  Printf.sprintf "kind=%s head=%s size=%d depth=%d interval=[%d,%d] limit=%d%s"
    (match v.band_kind with
    | `Overlap -> "top-overlap"
    | `Inner_overflow -> "inner-overflow")
    (name v.band_head) v.band_size v.band_depth v.band_low v.band_high
    v.band_limit
    (if v.band_next_head >= 0 then " next=" ^ name v.band_next_head else "")

(* [successors.(v)]: ascending, duplicate-free.  [touched.(v)]: [v] is an
   endpoint of some edge.  Untouched vertices get trailing orders in
   ascending number. *)
let decompose ?(call_first = false) ?(is_call = fun _ -> false) ?left_out
    successors touched =
  let count = Array.length successors in
  let t = make count successors in
  let member_count =
    Array.fold_left (fun n b -> if b then n + 1 else n) 0 touched
  in
  let members = Array.make member_count 0 and next = ref 0 in
  for i = 0 to count - 1 do
    if touched.(i) then begin
      members.(!next) <- i;
      incr next
    end
  done;
  let components =
    components_of t ~descending:false members (fun _ -> true) (-1)
  in
  let sccs =
    Array.init (Array.length components) (fun i ->
        components.(Array.length components - 1 - i))
  in
  let component_count = ref 0 and tied = ref 0 in
  let entry_sensitive = ref [] in
  let orders, heads, head_orders, _, owner, records =
    order_arrays ?left_out ~entry_sensitive t ~descending_members:true
      ~call_first ~is_call ~components:component_count ~tied sccs
  in
  (* before the trailing (edge-free) vertices are numbered: they have no
     edge, so their tickets cannot order any propagation *)
  let band_violations = band_check orders head_orders sccs owner records in
  Array.iteri
    (fun i succ -> if Array.exists (( = ) i) succ then heads.(i) <- true)
    successors;
  let highest = Array.fold_left max 0 orders in
  let next = ref (highest + 1) in
  Array.iteri
    (fun i o ->
      if o < 0 then begin
        orders.(i) <- !next;
        incr next
      end)
    orders;
  let d =
    {
      orders;
      heads;
      head_orders;
      top_components = sccs;
      component_count = !component_count;
      tied_component_count = !tied;
      band_violations;
      entry_sensitive = List.rev !entry_sensitive;
    }
  in
  d
