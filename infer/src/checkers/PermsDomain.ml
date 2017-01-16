open! IStd

module F = Format
module L = Logging


(* permission variables as identifiers *)
module Ident = struct
  module I = struct
    include Ident
    let pp_element = pp Pp.text
    let pp_key = pp_element
  end
  include I

  let pp = pp Pp.text
  let to_z3 = pp

  module Set = struct
    include PrettyPrintable.MakePPSet(I)
    let to_z3 fmt s =
      iter (F.fprintf fmt "(declare-const %a Real)@." to_z3) s
  end

  module Map = PrettyPrintable.MakePPMap(I)

  (* get a new fresh logical var id *)
  let mk () =
    create_fresh Ident.kprimed

  let subst theta v =
    if Map.mem v theta then Map.find v theta else v
end

(* class fields *)
module Field = struct
  module F = struct
    type t = Ident.fieldname
    let compare = Ident.compare_fieldname
    let pp_key = Ident.pp_fieldname
    let pp_element = pp_key
  end

  let pp = F.pp_element

  module Set = PrettyPrintable.MakePPSet(F)

  module Map = struct
    include PrettyPrintable.MakePPMap(F)

    (* make a new map from a set of fields into fresh logical var ids *)
    let mk fields =
      Set.fold (fun f fm -> add f (Ident.mk ()) fm) fields empty
  end
end

module Constr = struct
  type t = Exp.t

  let mk_add p q r =
    Exp.eq (Exp.Var p) (Exp.BinOp (Binop.PlusA, Exp.Var q, Exp.Var r))
  let mk_sum q ps =
    let rec sum = function
      | [p] -> Exp.Var p
      | p::ps -> Exp.BinOp (Binop.PlusA, Exp.Var p, sum ps)
      | _ -> assert false in
    Exp.eq (Exp.Var q) (sum ps)
  let mk_lb p =
    Exp.BinOp (Binop.Ge, Exp.Var p, Exp.zero)
  let mk_ub p =
    Exp.BinOp (Binop.Le, Exp.Var p, Exp.one)
  let mk_eq_one p =
    Exp.eq (Exp.Var p) (Exp.one)
  let mk_gt_zero p =
    Exp.BinOp (Binop.Gt, Exp.Var p, Exp.zero)
  let mk_minus p q r =
    Exp.eq (Exp.Var p) (Exp.BinOp (Binop.MinusA, Exp.Var q, Exp.Var r))
  let mk_le p q =
    Exp.BinOp (Binop.Le, (Exp.Var p), (Exp.Var q))

  (* substitution over permission constraints
     NB: we only cater for operators introduced by this analyser *)
  let rec subst theta = function
    | Exp.Var v -> Exp.Var (Ident.subst theta v)
    | Exp.BinOp(op, t1, t2) -> Exp.BinOp(op, subst theta t1, subst theta t2)
    | t -> t

  let rec to_z3 fmt e = match e with
    | Exp.Var id ->
      F.pp_print_string fmt (Ident.to_string id)
    | Exp.BinOp(Binop.Eq, t1, t2) ->
      F.fprintf fmt "(= %a %a)" to_z3 t1 to_z3 t2
    | Exp.BinOp(op, t1, t2) ->
      F.fprintf fmt "(%s %a %a)" (Binop.str Pp.text op) to_z3 t1 to_z3 t2
    | Exp.Const _ ->
      F.pp_print_string fmt (if Exp.is_zero e then "0.0" else "1.0")
    | _ ->
      assert false

  let rec vars = function
    | Exp.Var v -> Ident.Set.singleton v
    | Exp.BinOp(_, t1, t2) -> Ident.Set.union (vars t1) (vars t2)
    | _ -> Ident.Set.empty

  (* ordered set of permission constraints *)
  module Set = struct
    include PrettyPrintable.MakePPSet
        (struct
          include Exp
          let pp_element = pp
        end)

    (* variables of a constraint set *)
    let vars c =
      fold (fun exp a -> Ident.Set.union (vars exp) a) c Ident.Set.empty

    (* apply a function on every constraint in the set *)
    let map f s =
      fold (fun c a -> add (f c) a) s empty

    (* variable substitution over a constraint set *)
    let subst theta c =
      map (subst theta) c

    let to_z3 fmt c =
      Ident.Set.to_z3 fmt (vars c) ;
      iter (F.fprintf fmt "(assert %a)@." to_z3) c
  end
end

module ExpSet = struct
  include PrettyPrintable.MakePPSet
      (struct
        include Exp
        let pp_element = pp
      end)
end

type perms_t = Ident.t Field.Map.t

(* abstract state used in analyzer and transfer functions *)
type astate = {
  (* permission vars for the precondition; never changes during analysis of a method *)
  pre: perms_t;

  (* permission vars for the current abstract state *)
  curr: perms_t;

  (* permission vars for the class invariant -- never changes during analysis of a method *)
  inv: perms_t;

  (* var ids that hold a reference to "this" object at this point *)
  this_refs: ExpSet.t;

  (* constraints abduced *)
  constraints: Constr.Set.t;
}

module State = struct
  type t = astate

  let empty =
    {
      pre = Field.Map.empty;
      curr = Field.Map.empty;
      inv = Field.Map.empty;
      this_refs = ExpSet.empty;
      constraints = Constr.Set.empty;
    }

  let add_constr c a =
    { a with constraints = Constr.Set.add c a.constraints }
  let add_ref v a =
    { a with this_refs = ExpSet.add v a.this_refs }
  let remove_ref v a =
    { a with this_refs = ExpSet.remove v a.this_refs }
  let add_fld f v a =
    { a with curr = Field.Map.add f v a.curr }

  let pp fmt { pre; inv; curr; this_refs; constraints } =
    F.fprintf fmt "{ pre=%a; inv=%a; curr=%a; this_refs=%a; constraints=%a }"
      (Field.Map.pp ~pp_value:Ident.pp) pre
      (Field.Map.pp ~pp_value:Ident.pp) inv
      (Field.Map.pp ~pp_value:Ident.pp) curr
      ExpSet.pp this_refs
      Constr.Set.pp constraints
end



(* summary type, omit transient parts of astate *)
type summary =
  {
    sum_pre: perms_t;
    sum_inv: perms_t;
    sum_constraints: Constr.Set.t
  }

(* Abstract domain *)
module Domain = struct
  type nonrec astate = astate

  (* join unions the constraints.  When the permission variable for a field
     differs in the two abstract states, then a new variable is introduced plus
     constraints that force this variable to be bound by the minimum of the two
     joined permissions. *)
  let join a1 a2 =
    assert (Field.Map.equal Ident.equal a1.pre a2.pre) ;
    assert (Field.Map.equal Ident.equal a1.inv a2.inv) ;
    let mk_constr f v a = Constr.mk_le v (Field.Map.find f a.curr) in
    Field.Map.fold
      (fun f _v acc ->
         if Ident.equal _v (Field.Map.find f a2.curr) then
           State.add_fld f _v acc
         else
           let v = Ident.mk () in
           acc |>
           State.add_constr (mk_constr f v a1) |>
           State.add_constr (mk_constr f v a2) |>
           State.add_fld f v
      )
      a1.curr
      { a1 with
        curr = Field.Map.empty;
        this_refs = ExpSet.inter a1.this_refs a2.this_refs;
        (* FIXME following assumes disjointness of all vars except pre and inv *)
        constraints = Constr.Set.union a1.constraints a2.constraints;
      }

  let widen ~prev ~next ~num_iters:_ =
    join prev next

  let (<=) ~lhs:_ ~rhs:_ =
    false (* silly <=, FIXME for loops *)

  let pp = State.pp
end
