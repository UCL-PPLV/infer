open! IStd

module F = Format
module L = Logging

(* permission variables as identifiers *)
module Ident = struct
  module I = struct
    include Ident
    let pp = pp Pp.text
  end
  include I

  let to_z3 = pp

  module Set = struct
    include PrettyPrintable.MakePPSet(I)
    let to_z3 fmt s =
      iter (F.fprintf fmt "(declare-const %a Real)@." to_z3) s

    (* make a map from the names of variables in the set to the variables *)
    let mk_string_map vars =
      let l = fold (fun v a -> (I.to_string v, v)::a) vars [] in
      let m = String.Map.of_alist_exn l in
      m
  end

  module Map = PrettyPrintable.MakePPMap(I)

  (* get a new fresh logical var id *)
  let mk () =
    create_fresh Ident.kprimed
end

(* class fields *)
module Field = struct
  module F = struct
    type t = Ident.fieldname
    let compare = Ident.compare_fieldname
    let pp = Ident.pp_fieldname
  end
  include F

  module Set = PrettyPrintable.MakePPSet(F)

  module Map = struct
    include PrettyPrintable.MakePPMap(F)

    (* make a new map from a set of fields into fresh logical var ids *)
    let of_fields fields =
      Set.fold (fun f fm -> add f (Ident.mk ()) fm) fields empty
  end
end

module Constr = struct
  type t = Exp.t

  let rec sum = function
    | [p] -> Exp.Var p
    | p::ps -> Exp.BinOp (Binop.PlusA, Exp.Var p, sum ps)
    | _ -> assert false

  let mk_sum q ps =
    Exp.eq (Exp.Var q) (sum ps)
  let mk_lb ps =
    Exp.BinOp (Binop.Ge, sum ps, Exp.zero)
  let mk_ub ps =
    Exp.BinOp (Binop.Le, sum ps, Exp.one)
  let mk_eq_one ps =
    Exp.eq (sum ps) (Exp.one)
  let mk_gt_zero ps =
    Exp.BinOp (Binop.Gt, sum ps, Exp.zero)

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
    include PrettyPrintable.MakePPSet(Exp)

    (* variables of a constraint set *)
    let vars c =
      fold (fun exp a -> Ident.Set.union (vars exp) a) c Ident.Set.empty

    (* apply a function on every constraint in the set *)
    let endomap f s =
      fold (fun c a -> add (f c) a) s empty

    let to_z3 fmt c =
      Ident.Set.to_z3 fmt (vars c) ;
      iter (F.fprintf fmt "(assert %a)@." to_z3) c
  end
end

module ExpSet = PrettyPrintable.MakePPSet(Exp)

module Lock = struct
  module L = struct
    type t =
      | This
      | Fld of Field.t[@@deriving compare]
    let equal = [%compare.equal : t]
    let pp fmt = function
      | This -> F.pp_print_string fmt "|This|"
      | Fld f -> F.fprintf fmt "F(%a)" Field.pp f
  end
  include L

  module Set = PrettyPrintable.MakePPSet(L)
  module Map = PrettyPrintable.MakePPMap(L)

  module MultiSet = struct
    module Map = PrettyPrintable.MakePPMap(L)

    type elt = t
    type t = int Map.t
    (* invariant:
       l \in m iff m[l] is defined and m[l]>0
       if m[l] is defined then m[l]<>0
       canonical form required for easy equality/compare
    *)

    let empty = Map.empty

    let singleton l = Map.add l 1 empty

    let to_set m =
      Map.fold
        (fun l n acc ->
           if n>0 then
             List.fold (List.range 0 n) ~init:acc
               ~f:(fun acc' _ -> Set.add l acc')
           else
             acc
        )
        m
        Set.empty

    let compare m1 m2 =
      Map.compare Int.compare m1 m2
    let equal = [%compare.equal : t]
    let pp fmt m =
      Map.pp ~pp_value:Int.pp fmt m

    let union m1 m2 =
      Map.merge
        (fun _ n1 n2 ->
           match n1, n2 with
           | None, None -> None
           | Some n, None | None, Some n -> Some n
           | Some n1, Some n2 ->
               if phys_equal (n1+n2) 0 then None else Some (n1+n2)
        )
        m1
        m2

    let add l m =
      union (singleton l) m

    let mem l ls =
      try Map.find l ls > 0 with Not_found -> false

    let subset m1 m2 =
      let f =
        Map.merge
          (fun _ n1 n2 ->
             match n1, n2 with
             | None, None -> None
             | None, Some n2 when 0 <= n2 -> None
             | Some n1, None when n1 <= 0 -> None
             | Some n1, Some n2 when n1 <= n2 -> None
             | _, _ -> Some false
          )
          m1
          m2
      in
      Map.is_empty f

    let inter m1 m2 =
      Map.merge
        (fun _ n1 n2 ->
           match n1, n2 with
           | None, None -> None
           | None, Some n2 -> Some (min 0 n2)
           | Some n1, None -> Some (min n1 0)
           | Some n1, Some n2 -> Some (min n1 n2)
        )
        m1
        m2

    let remove l m =
      let n = try Map.find l m with Not_found -> 0 in
      if phys_equal n 1 then
        Map.remove l m
      else
        Map.add l (n-1) m
  end
end

module Atom = struct
  module A = struct
    module Access = struct
      type t = Read | Write [@@deriving compare]
      let equal = [%compare.equal : t]
      let pp fmt = function
        | Read -> F.pp_print_string fmt "Read"
        | Write -> F.pp_print_string fmt "Write"
    end

    type t =
      {
        access : Access.t;
        field : Field.t;
        locks : Lock.MultiSet.t;
        location : Location.t
      } [@@deriving compare]
    let equal = [%compare.equal : t]

    let pp fmt {access; field; locks; location} =
      F.fprintf fmt "<Acc=%a; Fld=%a; Lks=%a; Loc=%a>"
        Access.pp access
        Field.pp field
        Lock.MultiSet.pp locks
        Location.pp location
  end
  include A

  let add_locks a lks =
    { a with locks = Lock.MultiSet.union lks a.locks }

  module Set = PrettyPrintable.MakePPSet(A)
end


(* abstract state used in analyzer and transfer functions *)
type astate = {
  locks_held : Lock.MultiSet.t;
  atoms : Atom.Set.t;

  (* var ids that hold a reference to "this" object at this point *)
  this_refs: ExpSet.t;
}

module State = struct
  type t = astate

  let empty =
    {
      locks_held = Lock.MultiSet.empty;
      atoms = Atom.Set.empty;
      this_refs = ExpSet.empty;
    }

  let add_ref v a =
    { a with this_refs = ExpSet.add v a.this_refs }
  let remove_ref v a =
    { a with this_refs = ExpSet.remove v a.this_refs }
  let add_atom access field location a =
    { a with atoms = Atom.Set.add {access; field; locks=a.locks_held; location} a.atoms }

  let pp fmt { locks_held; atoms; this_refs } =
    F.fprintf fmt "{ locks_held=%a; atoms=%a; this_refs=%a }"
      Lock.MultiSet.pp locks_held
      Atom.Set.pp atoms
      ExpSet.pp this_refs
end

(* summary type, omit transient parts of astate *)
type summary =
  {
    sum_atoms: Atom.Set.t;
    sum_locks: Lock.MultiSet.t;
  }

(* Abstract domain *)
module WithoutBottomDomain = struct
  type nonrec astate = astate

  let join a1 a2 =
      {
        locks_held = Lock.MultiSet.inter a1.locks_held a2.locks_held;
        atoms = Atom.Set.union a1.atoms a2.atoms;
        this_refs = ExpSet.inter a1.this_refs a2.this_refs
      }

  let widen ~prev ~next ~num_iters:_ =
    join prev next

  let (<=) ~lhs ~rhs =
    Atom.Set.subset lhs.atoms rhs.atoms &&
    Lock.MultiSet.subset rhs.locks_held lhs.locks_held

  let pp = State.pp
end

module Domain = AbstractDomain.BottomLifted(WithoutBottomDomain)
