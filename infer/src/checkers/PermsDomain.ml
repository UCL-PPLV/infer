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
  end

  module Map = PrettyPrintable.MakePPMap(I)

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

  module Set = struct
    include PrettyPrintable.MakePPSet(F)

    let map_to f oadd oempty s =
      fold (fun x acc -> oadd (f x) acc) s oempty
    let endomap f s =
      map_to f add empty s
  end

  module Map = struct
    include PrettyPrintable.MakePPMap(F)

    (* make a new map from a set of fields into fresh logical var ids *)
    let of_fields fields =
      Set.fold (fun f fm -> add f (Ident.mk ()) fm) fields empty
  end
end

(* Constraints over permission variables *)
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
  end
end

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

module PvarMap = PrettyPrintable.MakePPMap
    (struct
      include Pvar
      let pp = pp Pp.text
    end)

let subst theta (base, accesses) =
  match base with
  | (Var.LogicalVar _, _) -> assert false
  | (Var.ProgramVar pvar, _) ->
      let argument = PvarMap.find pvar theta in
      AccessPath.append argument accesses

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
        (* field : Field.t; *)
        lvalue : AccessPath.Raw.t;
        locks : Lock.MultiSet.t;
        (* call path to access location ; non-empty list whose last item is the access location
           and every other item is the location of a method call leading to the access *)
        path : CallSite.t list;
      } [@@deriving compare]
    let equal = [%compare.equal : t]

    let pp fmt {access; lvalue; locks; path} =
      F.fprintf fmt "%a of l-value %a @@ (%a); locks held=%a"
        Access.pp access
        AccessPath.Raw.pp lvalue
        (Pp.comma_seq CallSite.pp) path
        Lock.MultiSet.pp locks
  end
  include A

  let is_read =
    function { access=Read } -> true | _ -> false
  let is_write =
    function { access=Write } -> true | _ -> false

  let mk_read lvalue locks site =
    let access = Access.Read in
    { access; lvalue; locks; path=[site] }
  let mk_write lvalue locks site =
    let access = Access.Write in
    { access; lvalue; locks; path =[site] }
  let adapt lks site theta a =
    { a with
      lvalue = subst theta a.lvalue;
      locks = Lock.MultiSet.union lks a.locks;
      path = site::a.path
    }

  let compile premap invmap { access; lvalue; locks } =
    let lmap = AccessPath.RawMap.find lvalue invmap in
    let lks = Lock.MultiSet.to_set locks in
    let invs =
      Lock.Set.fold (fun l acc -> (Lock.Map.find l lmap)::acc) lks [] in
    let p = AccessPath.RawMap.find lvalue premap in
    match access with
    | Access.Read -> Constr.mk_gt_zero (p::invs)
    | Access.Write -> Constr.mk_eq_one (p::invs)

  module Set = struct
    include PrettyPrintable.MakePPSet(A)

    let map_to f oadd oempty s =
      fold (fun x acc -> oadd (f x) acc) s oempty
    let endomap f s =
      map_to f add empty s
  end
end

module IdMap = struct
  module M = Var.Map

  type t = AccessPath.Raw.t M.t
  let empty = M.empty

  let pp fmt m = M.pp ~pp_value:AccessPath.Raw.pp fmt m
  let add = M.add

  let may_join m1 m2 =
    M.merge
      (fun _ ap1_opt ap2_opt ->
         match ap1_opt, ap2_opt with
         | Some _, None -> ap1_opt
         | None, Some _ -> ap2_opt
         | Some ap1, Some ap2 when AccessPath.Raw.equal ap1 ap2 -> ap1_opt
         | _, _ -> None
      )
      m1
      m2

  let must_join m1 m2 =
    M.merge
      (fun _ ap1_opt ap2_opt ->
         match ap1_opt, ap2_opt with
         | Some ap1, Some ap2 when AccessPath.Raw.equal ap1 ap2 -> ap1_opt
         | _, _ -> None
      )
      m1
      m2

  let submap m1 m2 =
    let m =
      M.merge
        (fun _ ap1_opt ap2_opt ->
           match ap1_opt, ap2_opt with
           | None, _ -> None
           | Some ap1, Some ap2 when AccessPath.Raw.equal ap1 ap2 -> None
           | _ -> ap1_opt
        )
        m1
        m2
    in
    M.is_empty m

  let resolve m id =
    try Some (M.find id m) with Not_found -> None

  let update lhs_id rhs_exp rhs_typ m =
    let f_resolve_id = resolve m in
    match AccessPath.of_lhs_exp rhs_exp rhs_typ ~f_resolve_id with
    | Some rhs_access_path -> add lhs_id rhs_access_path m
    | None -> m

  let remove_id v m =
    M.remove (Var.of_id v) m
end

(* abstract state used in analyzer and transfer functions *)
type astate = {
  locks_held : Lock.MultiSet.t;
  atoms : Atom.Set.t;
  (* may_point : IdMap.t; *)
  must_point : IdMap.t;
}

module State = struct
  type t = astate

  let empty =
    {
      locks_held = Lock.MultiSet.empty;
      atoms = Atom.Set.empty;
      (* may_point = IdMap.empty; *)
      must_point = IdMap.empty;
    }

  let update_pvar lhs_pvar rhs_exp lhs_typ a =
    { a with
      (* may_point = IdMap.update (Var.of_pvar lhs_pvar) rhs_exp lhs_typ a.may_point; *)
      must_point = IdMap.update (Var.of_pvar lhs_pvar) rhs_exp lhs_typ a.must_point
    }
  let update_id lhs_id rhs_exp rhs_typ a =
    { a with
      (* may_point = IdMap.update (Var.of_id lhs_id) rhs_exp rhs_typ a.may_point; *)
      must_point = IdMap.update (Var.of_id lhs_id) rhs_exp rhs_typ a.must_point
    }
  let remove_ids ids a =
    { a with
      (* may_point =
        List.fold ~f:(fun acc id -> IdMap.remove_id id acc) ~init:a.may_point ids; *)
      must_point =
        List.fold ~f:(fun acc id -> IdMap.remove_id id acc) ~init:a.must_point ids
    }

  let is_this var m =
    match IdMap.resolve m var with
    | Some ((v, _), []) -> Exp.is_this (Var.to_exp v)
    | _ -> false

  let must_be_this var a =
    is_this var a.must_point
  let must_resolve exp typ a =
    match AccessPath.of_lhs_exp exp typ ~f_resolve_id:(IdMap.resolve a.must_point) with
    | Some a -> a
    | None -> assert false

  let add_read lvalue site a =
    { a with atoms = Atom.Set.add (Atom.mk_read lvalue a.locks_held site) a.atoms }
  let add_write lvalue site a =
    { a with atoms = Atom.Set.add (Atom.mk_write lvalue a.locks_held site) a.atoms }

  let pp fmt { locks_held; atoms; must_point } =
    F.fprintf fmt "{ locks_held=%a; atoms=%a; must_point=%a }"
      Lock.MultiSet.pp locks_held
      Atom.Set.pp atoms
      (* IdMap.pp may_point *)
      IdMap.pp must_point
end

type summary = Atom.Set.t * Lock.MultiSet.t * Pvar.t list

(* Abstract domain *)
module Domain = struct
  type nonrec astate = astate

  let join a1 a2 =
      {
        locks_held = Lock.MultiSet.inter a1.locks_held a2.locks_held;
        atoms = Atom.Set.union a1.atoms a2.atoms;
        (* may_point = IdMap.may_join a1.may_point a2.may_point; *)
        must_point = IdMap.must_join a1.must_point a2.must_point
      }

  let widen ~prev ~next ~num_iters:_ =
    join prev next

  let (<=) ~lhs ~rhs =
    Atom.Set.subset lhs.atoms rhs.atoms &&
    Lock.MultiSet.subset rhs.locks_held lhs.locks_held &&
    (* IdMap.submap lhs.may_point rhs.may_point && *)
    IdMap.submap rhs.must_point lhs.must_point

  let pp = State.pp
end
