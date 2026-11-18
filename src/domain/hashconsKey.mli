(** Representation identity: the key of the abstract-domain hash-cons tables.

    [equal x y] holds only when [x] and [y] are interchangeable by every
    operation except [==] on their own blocks: the same constructors, scalars
    and tree shapes, with every embedded CIL object ([Sparrow_cil.typ]) being
    the SAME physical object.  It never descends into a CIL type, which may be
    cyclic, so it terminates on values whose types were decoded separately
    (separately marshaled values).  [hash] is bounded
    and consistent with [equal].  Hash-consing [v] to a resident [v'] with
    [equal v v'] cannot change an analysis result: [v'] is [v] up to the
    physical sharing of domain blocks.

    The domain functors ([PowDom], [MapDom], [ProdDom]) find the identity of
    their parameters here, keyed by the parameter's [compare] closure, and
    register their own.  A leaf type that embeds a CIL object ([BasicDom.Loc])
    registers its identity before any functor is applied to it.  Every other
    leaf (intervals, nodes, procedures, strings) embeds none and uses [poly].

    (The registry rather than an extra functor parameter keeps the domain
    interfaces unchanged.) *)

type 'a t = { equal : 'a -> 'a -> bool; hash : 'a -> int }

(** OCaml's structural comparison and [Hashtbl.hash]: for values without CIL
    objects, the key of a polymorphic hash-cons table. *)
val poly : unit -> 'a t

(** [register compare rep] makes [rep] the identity of the type whose
    [compare] closure is [compare] (that closure must be specific to the
    type).  Registering one closure twice is an error. *)
val register : ('a -> 'a -> int) -> 'a t -> unit

(** The registered identity of [compare]'s type, or [poly ()]. *)
val find : ('a -> 'a -> int) -> 'a t

(** Bounded hash mixing for the functors' tree hashes. *)
val mix : int -> int -> int

(** A hash-cons table on [rep]: [intern] returns the resident value
    [rep.equal] to its argument, or makes the argument resident. *)
type 'a table
val create : 'a t -> 'a table
val intern : 'a table -> 'a -> 'a
val clear : 'a table -> unit
