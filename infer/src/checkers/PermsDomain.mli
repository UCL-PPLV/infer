open! IStd

(* permission variables as identifiers *)
module Ident : sig
  type t = Ident.t
  type fieldname = Ident.fieldname

  val pp : Format.formatter -> t -> unit
  val to_z3 : Format.formatter -> t -> unit

  module Set : sig
    include PrettyPrintable.PPSet with type elt = t

    val to_z3 : Format.formatter -> t -> unit
  end

  module Map : PrettyPrintable.PPMap with type key = t

  (* get a new fresh logical var id *)
  val mk : unit -> t
end

(* class fields *)
module Field : sig
  type t = Ident.fieldname
  val equal : t -> t -> bool

  val pp : Format.formatter -> t -> unit

  module Set : sig
    include PrettyPrintable.PPSet with type elt = t

    val endomap : (elt -> elt) -> t -> t
    val map_to : (elt -> 'a) -> ('a -> 'b -> 'b) -> 'b -> t -> 'b
  end

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
  end
end

module Lock : sig
  type t =
    | This
    | Fld of Ident.fieldname
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

    val union : t -> t -> t
    val add : elt -> t -> t
    val remove : elt -> t -> t
    val inter : t -> t -> t
  end
end

module PvarMap : PrettyPrintable.PPMap with type key = Pvar.t

module Atom : sig
  module Access : sig
    type t = Read | Write
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val pp : Format.formatter -> t -> unit
  end

  type t = private
    {
      access : Access.t;
      lvalue : AccessPath.Raw.t;
      locks : Lock.MultiSet.t;
      path : CallSite.t list;
    }

  val compare : t -> t -> int
  val equal : t -> t -> bool
  val pp : Format.formatter -> t -> unit

  val is_read : t -> bool
  val is_write : t -> bool

  val mk_read : AccessPath.Raw.t -> Lock.MultiSet.t -> CallSite.t -> t
  val mk_write : AccessPath.Raw.t -> Lock.MultiSet.t -> CallSite.t -> t
  val adapt : Lock.MultiSet.t -> CallSite.t -> AccessPath.Raw.t PvarMap.t -> t -> t

  module Set : sig
    include PrettyPrintable.PPSet with type elt = t

    val endomap : (elt -> elt) -> t -> t
    val map_to : (elt -> 'a) -> ('a -> 'b -> 'b) -> 'b -> t -> 'b

(* quotient an atom set by an equivalence relation *)
    val quotient : (elt -> elt -> bool) -> t -> t list
  end

  module Map : PrettyPrintable.PPMap with type key = t

  (* Using a precondition permission variable for the heap location in the atom and
     a map from locks to lock invariant permissions,
     compile the atom into a constraint *)
  val compile : Ident.t -> Ident.t Lock.Map.t -> t -> Constr.t

end

module IdMap : sig
  (* module M = Var.Map *)

  type t = AccessPath.Raw.t Var.Map.t
  val empty : t

  val add : Var.t -> AccessPath.Raw.t -> t -> t
  val resolve : t -> Var.t -> AccessPath.Raw.t option
  val update : Var.t -> Exp.t -> Typ.t -> t -> t
end

(* abstract state used in analyzer and transfer functions *)
type astate = {
  locks_held : Lock.MultiSet.t;
  atoms : Atom.Set.t;
  (* may_point : IdMap.t; *)
  must_point : IdMap.t;
}

module State : sig
  type t = astate

  val empty : t

  val update_pvar : Pvar.t -> Exp.t -> Typ.t -> t -> t
  val update_id : Ident.t -> Exp.t -> Typ.t -> t -> t
  val remove_ids : Ident.t list -> t -> t

  (* val may_be_this : Var.t -> t -> bool *)
  val must_be_this : Var.t -> t -> bool
  val must_resolve : Exp.t -> Typ.t -> t -> AccessPath.Raw.t

  val add_read : AccessPath.Raw.t -> CallSite.t -> t -> t
  val add_write : AccessPath.Raw.t -> CallSite.t -> t -> t
  val pp : Format.formatter -> t -> unit
end

(* summary type, omit transient parts of astate, last field is formals *)
type summary = Atom.Set.t * Lock.MultiSet.t * Pvar.t list * Tenv.t

module Domain : AbstractDomain.S with type astate = astate
