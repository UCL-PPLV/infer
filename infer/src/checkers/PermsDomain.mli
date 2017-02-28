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

  val subst : t Map.t -> t -> t
end

(* class fields *)
module Field : sig
  type t = Ident.fieldname

  val pp : Format.formatter -> t -> unit

  module Set : PrettyPrintable.PPSet with type elt = t

  module Map : sig
    include PrettyPrintable.PPMap with type key = t

    (* make a new map from a set of fields into fresh logical var ids *)
    val mk : Set.t -> Ident.t t

(* extend a given variable substitution sending, for each field in the two maps,
   the variable from the first map to that of the second. *)
    val mk_theta : Ident.t Ident.Map.t -> Ident.t t -> Ident.t t -> Ident.t Ident.Map.t

  end
end

module Constr : sig
  type t = Exp.t

  val mk_sum : Ident.t -> Ident.t list -> t
  val mk_add : Ident.t -> Ident.t -> Ident.t -> t
  val mk_lb : Ident.t -> t
  val mk_ub : Ident.t -> t
  (* val mk_eq_one : Ident.t -> t *)
  val mk_eq_one : Ident.t list -> t
  (* val mk_gt_zero : Ident.t -> t *)
  val mk_gt_zero : Ident.t list -> t
  val mk_minus : Ident.t -> Ident.t -> Ident.t -> t
  val mk_le : Ident.t -> Ident.t -> t

  (* substitution over permission constraints
     NB: we only cater for operators introduced by this analyser *)
  val subst : Ident.t Ident.Map.t -> t -> t

  val to_z3 : Format.formatter -> t -> unit

  val vars : t -> Ident.Set.t

  (* ordered set of permission constraints *)
  module Set : sig
    include PrettyPrintable.PPSet with type elt = t

    (* variables of a constraint set *)
    val vars : t -> Ident.Set.t

    (* apply a function on every constraint in the set *)
    val map : (elt -> elt) -> t -> t

    (* variable substitution over a constraint set *)
    val subst : Ident.t Ident.Map.t -> t -> t

    val to_z3 : Format.formatter -> t -> unit
  end
end

module ExpSet : PrettyPrintable.PPSet with type elt = Exp.t

type perms_t = Ident.t Field.Map.t

(* abstract state used in analyzer and transfer functions *)
type astate = {
  (* permission vars for the precondition; never changes during analysis of a method *)
  pre: perms_t;

  (* permission vars for the current abstract state *)
  curr: perms_t;

  (* is the lock taken in the current state *)
  locked: bool;

  (* permission vars for the class invariant -- never changes during analysis of a method *)
  inv: perms_t;

  (* var ids that hold a reference to "this" object at this point *)
  this_refs: ExpSet.t;

  (* constraints abduced *)
  constraints: Constr.Set.t;
}

module State : sig
  type t = astate

  val empty : t

  val add_constr : Exp.t -> t-> t
  val add_ref : Exp.t -> t -> t
  val remove_ref : Exp.t -> t -> t
  (* add a mapping to the curr state *)
  val add_fld : Field.t -> Ident.t -> t -> t
  val pp : Format.formatter -> t -> unit
end

(* summary type, omit transient parts of astate *)
type summary =
  {
    sum_pre: perms_t;
    sum_inv: perms_t;
    sum_post: perms_t;
    sum_constraints: Constr.Set.t;
    (*NB sum_locked stands for whether the method definitely locks but does not
      unlock on method exit *)
    sum_locked: bool;
  }

(* Abstract domain *)
(* module Domain : sig
  type nonrec astate = astate

  (* join unions the constraints.  When the permission variable for a field
     differs in the two abstract states, then a new variable is introduced plus
     constraints that force this variable to be bound by the minimum of the two
     joined permissions. The lock state is and-ed together. *)
  val join : astate -> astate -> astate
  val widen : prev:astate -> next:astate -> num_iters:int -> astate
  val (<=) : lhs:astate -> rhs:astate -> bool
  val pp : Format.formatter -> astate -> unit
end *)

module Domain : sig
  type nonrec astate =
    | Bottom
    | NonBottom of astate

  include AbstractDomain.S with type astate := astate
end
