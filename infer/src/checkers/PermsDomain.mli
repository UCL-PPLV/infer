open! IStd

(* permission variables as identifiers *)
module Ident : sig
  type t
  type fieldname = Ident.fieldname

  val pp : Format.formatter -> t -> unit
  val to_z3 : Format.formatter -> t -> unit

  module Set : sig
    include PrettyPrintable.PPSet with type elt = t

    val to_z3 : Format.formatter -> t -> unit

    (* make a map from the names of variables in the set to the variables *)
    val mk_string_map : t -> elt String.Map.t
  end

  module Map : PrettyPrintable.PPMap with type key = t

  (* get a new fresh logical var id *)
  val mk : unit -> t
end

(* class fields *)
module Field : sig
  type t = Ident.fieldname

  val pp : Format.formatter -> t -> unit

  module Set : PrettyPrintable.PPSet with type elt = t

  module Map : sig
    include PrettyPrintable.PPMap with type key = t

(* make a new map from a set of fields into fresh logical var ids *)
    val of_fields : Set.t -> Ident.t t
  end
end

module Constr : sig
  type t = Exp.t

  val mk_sum : Ident.t -> Ident.t list -> t
  val mk_lb : Ident.t list -> t
  val mk_ub : Ident.t list -> t
  val mk_eq_one : Ident.t list -> t
  val mk_gt_zero : Ident.t list -> t

  val to_z3 : Format.formatter -> t -> unit
  val vars : t -> Ident.Set.t

  (* ordered set of permission constraints *)
  module Set : sig
    include PrettyPrintable.PPSet with type elt = t

    (* variables of a constraint set *)
    val vars : t -> Ident.Set.t
    (* variable substitution over a constraint set *)
    val to_z3 : Format.formatter -> t -> unit
  end
end

module Lock : sig
  type t =
    | This
    | Fld of Field.t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val pp : Format.formatter -> t -> unit

  module Set : PrettyPrintable.PPSet with type elt = t
  module Map : PrettyPrintable.PPMap with type key = t

  module MultiSet : sig
    type elt = t
    type t
    val empty : t
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val pp : Format.formatter -> t -> unit

    val to_set : t -> Set.t
    val singleton : elt -> t

(* val subset : t -> t -> bool *)
    val union : t -> t -> t
    val add : elt -> t -> t
    val remove : elt -> t -> t
    (* val mem : elt -> t -> bool *)
    val inter : t -> t -> t
  end
end

module Atom : sig
  module Access : sig
    type t = Read | Write
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val pp : Format.formatter -> t -> unit
  end

  type t =
    {
      access : Access.t;
      field : Field.t;
      locks : Lock.MultiSet.t;
      location : Location.t;
    }

  val compare : t -> t -> int
  val equal : t -> t -> bool
  val pp : Format.formatter -> t -> unit

  val add_locks : t -> Lock.MultiSet.t -> t

  module Set : PrettyPrintable.PPSet with type elt = t
end

module ExpSet : PrettyPrintable.PPSet with type elt = Exp.t

(* abstract state used in analyzer and transfer functions *)
type astate = {
  locks_held : Lock.MultiSet.t;
  atoms : Atom.Set.t;

  (* var ids that hold a reference to "this" object at this point *)
  this_refs: ExpSet.t;
}

module State : sig
  type t = astate

  val empty : t

  val add_ref : Exp.t -> t -> t
  val remove_ref : Exp.t -> t -> t
  val add_atom : Atom.Access.t -> Field.t -> Location.t -> t -> t
  val pp : Format.formatter -> t -> unit
end

(* summary type, omit transient parts of astate *)
type summary =
  {
    sum_atoms: Atom.Set.t;
    sum_locks: Lock.MultiSet.t;
  }

module Domain : sig
  type nonrec astate =
    | Bottom
    | NonBottom of astate

  include AbstractDomain.S with type astate := astate
end
