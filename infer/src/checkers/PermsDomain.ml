open! IStd

module F = Format
module L = Logging

module IdentMap = Ident.IdentMap

module Ident = struct
  include Ident

  let subst theta v =
    if IdentMap.mem v theta then IdentMap.find v theta else v

  (* get a new fresh logical var id *)
  let mk () = create_fresh Ident.knormal
end

module Field = struct
  type t = Ident.fieldname
  let compare = Ident.compare_fieldname
  let pp_key = Ident.pp_fieldname
  let pp_element = pp_key
end

module FieldSet = PrettyPrintable.MakePPSet(Field)

module FieldMap = struct
  include PrettyPrintable.MakePPMap(Field)

  (* make a new map from a set of fields into fresh logical var ids *)
  let mk fields =
    FieldSet.fold
      (fun f fm -> add f (Ident.mk ()) fm)
      fields
      empty
end


module IdentSet =
  PrettyPrintable.MakePPSet
    (struct
      include Ident
      let pp_element = pp Pp.text
    end)

let rec exp_subst theta t =
  match t with
  | Exp.Var v -> Exp.Var (Ident.subst theta v)
  | Exp.BinOp(op, t1, t2) -> Exp.BinOp(op, exp_subst theta t1, exp_subst theta t2)
  | _ -> t

module ExpSet = struct
  include PrettyPrintable.MakePPSet
      (struct
        include Exp
        let pp_element = pp
      end)

  let vars c =
    let rec _vars = function
      | Exp.Var v ->
        IdentSet.singleton v
      | Exp.BinOp(_, t1, t2) ->
        IdentSet.union (_vars t1) (_vars t2)
      | _ -> IdentSet.empty in
    fold
      (fun exp a -> IdentSet.union (_vars exp) a)
      c
      IdentSet.empty

  let map f s = fold (fun c a -> add (f c) a) s empty

  let subst theta c = map (exp_subst theta) c

end



(* Holds an actual value, the set of fields of the class of "this".
   Meant to be used as an argument to the analyzer functor. *)
module type ClassFields =
sig
  val fields : FieldSet.t
end

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
    let m = FieldMap.mk CF.fields in
    { empty with pre = m; curr = m; inv = FieldMap.mk CF.fields }

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
           let v = Ident.mk () in
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
