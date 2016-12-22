open! IStd

module F = Format
module L = Logging

module Field = struct
  type t = Ident.fieldname
  let compare = Ident.compare_fieldname
  let pp_key = Ident.pp_fieldname
  let pp_element = pp_key
end

module FieldMap = PrettyPrintable.MakePPMap(Field)
module FieldSet = PrettyPrintable.MakePPSet(Field)

module ExpSet =
  PrettyPrintable.MakePPSet
    (struct
      include Exp
      let pp_element = pp
    end)

module IdentSet =
  PrettyPrintable.MakePPSet
    (struct
      include Ident
      let pp_element = pp Pp.text
    end)

(* Holds an actual value, the set of fields of the class of "this".
   Meant to be used as an argument to the analyzer functor. *)
module type ClassFields =
sig
  val fields : FieldSet.t
end

(* get a new fresh logical var id *)
let fresh_ident () = Ident.create_fresh Ident.knormal

(* make a new map from a set of fields into fresh logical var ids *)
let mk_fmap fields =
  FieldSet.fold
    (fun f fm -> FieldMap.add f (fresh_ident ()) fm)
    fields
    FieldMap.empty

type perms_t = Ident.t FieldMap.t

(* abstract state used in analyzer and transfer functions functors *)
type astate = {
  (* permission vars for the precondition -- never changes during analysis of a method *)
  pre: perms_t;

  (* permission vars for the current abstract state *)
  curr: perms_t;

  (* permission vars for the class invariant -- never changes during analysis of a method *)
  inv: perms_t;

  (* var ids that hold a reference to "this" object at this point *)
  this_refs: IdentSet.t;

  (* constraints abduced *)
  constraints: ExpSet.t
}

(* summary type, omit transient parts of astate *)
type summary =
  {
    sum_pre: perms_t;
    sum_inv: perms_t;
    sum_constraints: ExpSet.t;
  }

let mk_summary { pre; inv; constraints } =
  {
    sum_pre = pre;
    sum_inv = inv;
    sum_constraints = constraints;
  }

(* Make an abstract domain, given the fields of the current class *)
module MakeDomain(CF : ClassFields) = struct
  type nonrec astate = astate

  let empty =
    {
      pre = FieldMap.empty;
      curr = FieldMap.empty;
      inv = FieldMap.empty;
      this_refs = IdentSet.empty;
      constraints = ExpSet.empty
    }

  let initial =
    let m = mk_fmap CF.fields in
    { empty with pre = m; curr = m; inv = mk_fmap CF.fields }

  let add_constr c a = { a with constraints = ExpSet.add c a.constraints }

  (* join unions the constraints.  When the permission variable for a field
     differs in the two abstract states, then a new variable is introduced plus
     constraints that force this variable to be bound by the minimum of the two
     joined permissions. *)
  let join a1 a2 =
    assert (FieldMap.equal Ident.equal a1.pre a2.pre) ;
    assert (FieldMap.equal Ident.equal a1.inv a2.inv) ;
    let mk_le p q = Exp.BinOp (Binop.Le, (Exp.Var p), (Exp.Var q)) in
    let mk_constr f v a = mk_le v (FieldMap.find f a.curr) in
    FieldSet.fold
      (fun f acc ->
         if Ident.equal (FieldMap.find f a1.curr) (FieldMap.find f a2.curr) then
           { acc with curr = FieldMap.add f (FieldMap.find f a1.curr) acc.curr } else
           let v = fresh_ident () in
           let acc' = add_constr (mk_constr f v a1) acc |> add_constr (mk_constr f v a2) in
           { acc' with curr = FieldMap.add f v acc.curr }
      )
      CF.fields
      { a1 with
        curr = FieldMap.empty;
        this_refs = IdentSet.inter a1.this_refs a2.this_refs;
        constraints = ExpSet.union a1.constraints a2.constraints;
      }

  let widen ~prev ~next ~num_iters:_ =
    join prev next

  let (<=) ~lhs:_ ~rhs:_ =
    false (* silly <=, FIXME for loops *)

  let pp fmt { pre; inv; curr; this_refs; constraints } =
    F.fprintf fmt "{ pre=%a; inv=%a; curr=%a; this_refs=%a; constraints=%a }"
      (FieldMap.pp ~pp_value:(Ident.pp Pp.text)) pre
      (FieldMap.pp ~pp_value:(Ident.pp Pp.text)) inv
      (FieldMap.pp ~pp_value:(Ident.pp Pp.text)) curr
      IdentSet.pp this_refs
      ExpSet.pp constraints
end
