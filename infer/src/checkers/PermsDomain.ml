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

  let subst theta v =
    if Map.mem v theta then Map.find v theta else v
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

    let mk m =
      fold
        (fun f _ acc -> add f (Ident.mk ()) acc)
        m
        empty

    let mk_theta theta ps qs =
      fold
        (fun f v acc -> Ident.Map.add v (find f qs) acc)
        ps
        theta

    let fresh_theta theta ps =
      fold
        (fun _ v acc -> Ident.Map.add v (Ident.mk ()) acc)
        ps
        theta
  end
end

module Constr = struct
  type t = Exp.t

  let rec sum = function
    | [p] -> Exp.Var p
    | p::ps -> Exp.BinOp (Binop.PlusA, Exp.Var p, sum ps)
    | _ -> assert false

  let mk_add p q r =
    Exp.eq (Exp.Var p) (Exp.BinOp (Binop.PlusA, Exp.Var q, Exp.Var r))
  let mk_sum q ps =
    Exp.eq (Exp.Var q) (sum ps)
  let mk_lb p =
    Exp.BinOp (Binop.Ge, Exp.Var p, Exp.zero)
  let mk_ub p =
    Exp.BinOp (Binop.Le, Exp.Var p, Exp.one)
  (* let mk_eq_one p =
    Exp.eq (Exp.Var p) (Exp.one) *)
  let mk_eq_one ps =
    Exp.eq (sum ps) (Exp.one)
  (* let mk_gt_zero p =
    Exp.BinOp (Binop.Gt, Exp.Var p, Exp.zero) *)
  let mk_gt_zero ps =
    Exp.BinOp (Binop.Gt, sum ps, Exp.zero)
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
    include PrettyPrintable.MakePPSet(Exp)

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
    type elt = t
    type t = elt list

    let empty = []

    let singleton x = [x]
    let to_list m = m

    let compare m1 m2 = List.compare L.compare m1 m2
    let equal = [%compare.equal : t]
    let pp fmt m = F.fprintf fmt "{%a}" (Pp.seq L.pp) m

    let union m1 m2 =
      List.sort ~cmp:L.compare (m1 @ m2)

    let add l m =
      union (singleton l) m

    let rec remove l = function
      | [] -> raise Not_found
      | l'::ls when L.equal l l' -> ls
      | l'::ls -> l'::(remove l ls)

    let mem l ls =
      List.mem ~equal:L.equal ls l

    (* let mem_remove l m =
      let rec aux (acc,found) = function
        | [] -> if found then Some (List.rev acc) else None
        | l'::ls when L.equal l l' -> aux (acc,true) ls
        | l'::ls -> aux (l'::acc,found) ls
      in
      aux ([], false) m

    let rec subset m1 m2 =
      match m1 with
      | [] -> true
      | l::ls ->
          match mem_remove l m2 with
          | None -> false
          | Some m2' -> subset ls m2'

    let equal m1 m2 =
       subset m1 m2 && subset m2 m1 *)

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
      } [@@deriving compare]
    let equal = [%compare.equal : t]

    let pp fmt {access; field; locks} =
      F.fprintf fmt "<Acc=%a; Fld=%a; Lks=%a>"
        Access.pp access
        Field.pp field
        Lock.MultiSet.pp locks

  end
  include A

  let add_locks a lks =
    let lks = Lock.MultiSet.to_list lks in
    { a with locks = List.fold lks ~init:a.locks ~f:(fun acc l -> Lock.MultiSet.add l acc)}
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
  let add_atom access field a =
    { a with atoms = Atom.Set.add {access; field; locks=a.locks_held} a.atoms }

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

  (* join unions the constraints.  When the permission variable for a field
     differs in the two abstract states, then a new variable is introduced plus
     constraints that force this variable to be bound by the minimum of the two
     joined permissions. The lock state is and-ed together. *)
  let join a1 a2 =
      { a1 with
        locks_held = Lock.MultiSet.union a1.locks_held a2.locks_held;
        atoms = Atom.Set.union a1.atoms a2.atoms;
      }

  let widen ~prev ~next ~num_iters:_ =
    join prev next

  let (<=) ~lhs:_ ~rhs:_ =
    false (* silly <=, FIXME for loops *)

  let pp = State.pp
end

module Domain = AbstractDomain.BottomLifted(WithoutBottomDomain)
