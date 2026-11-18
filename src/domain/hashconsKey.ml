(* See hashconsKey.mli. *)

type 'a t = { equal : 'a -> 'a -> bool; hash : 'a -> int }

let poly () =
  { equal = (fun x y -> x == y || Stdlib.compare x y = 0); hash = Hashtbl.hash }

(* Few entries (one per domain functor application); searched only when a
   functor is applied, never per value. *)
let registry : (Obj.t * Obj.t) list ref = ref []

let register (compare : 'a -> 'a -> int) (rep : 'a t) =
  let key = Obj.repr compare in
  if List.exists (fun (resident, _) -> resident == key) !registry then
    invalid_arg "HashconsKey.register: compare closure already registered";
  registry := (key, Obj.repr rep) :: !registry

let find (compare : 'a -> 'a -> int) : 'a t =
  let key = Obj.repr compare in
  match List.find_opt (fun (resident, _) -> resident == key) !registry with
  | Some (_, rep) -> (Obj.obj rep : 'a t)
  | None -> poly ()

let mix h x = h * 0x01000193 lxor x land max_int

type 'a table = {
  lookup : 'a -> 'a option;
  add : 'a -> unit;
  reset : unit -> unit;
}

let create (type a) (rep : a t) : a table =
  let module H = Hashtbl.Make (struct
    type t = a

    let equal = rep.equal
    let hash = rep.hash
  end) in
  let table = H.create 251 in
  {
    lookup = H.find_opt table;
    add = (fun x -> H.add table x x);
    reset = (fun () -> H.reset table);
  }

let intern table x =
  match table.lookup x with
  | Some resident -> resident
  | None ->
      table.add x;
      x

let clear table = table.reset ()
