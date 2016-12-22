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

(* Make a transfer functions module given the fields of a class *)
module MakeTransferFunctions (CF : ClassFields)(CFG : ProcCfg.S) = struct
  module CFG = CFG
  module Domain = MakeDomain(CF)
  type extras = ProcData.no_extras

  (* stolen from ThreadSafety *)
  type lock_model =
    | Lock
    | Unlock
    | NoEffect

  (* stolen from ThreadSafety *)
  let get_lock_model = function
    | Procname.Java java_pname ->
      begin
        match Procname.java_get_class_name java_pname, Procname.java_get_method java_pname with
        | "java.util.concurrent.locks.Lock", "lock" ->
          Lock
        | ("java.util.concurrent.locks.ReentrantLock"
          | "java.util.concurrent.locks.ReentrantReadWriteLock$ReadLock"
          | "java.util.concurrent.locks.ReentrantReadWriteLock$WriteLock"),
          ("lock" | "tryLock" | "lockInterruptibly") ->
          Lock
        | ("java.util.concurrent.locks.Lock"
          |"java.util.concurrent.locks.ReentrantLock"
          | "java.util.concurrent.locks.ReentrantReadWriteLock$ReadLock"
          | "java.util.concurrent.locks.ReentrantReadWriteLock$WriteLock"),
          "unlock" ->
          Unlock
        | _ ->
          NoEffect
      end
    | pname when Procname.equal pname BuiltinDecl.__set_locked_attribute ->
      Lock
    | pname when Procname.equal pname BuiltinDecl.__delete_locked_attribute ->
      Unlock
    | _ ->
      NoEffect

  (* decide if a lock statement is about "this" *)
  let lock_effect_on_this pn args astate =
    (* L.out "args=%a this_refs=%a@." (PrettyPrintable.pp_collection ~pp_item:Exp.pp) (IList.map fst args) IdentSet.pp astate.this_refs; *)
    let this_arg =
      IList.length args = 1 &&
      match fst (IList.hd args) with
      | Exp.Var ident ->
      (* L.out "ident=%a this_refs=%a@." (Ident.pp Pp.text) ident IdentSet.pp astate.this_refs; *)
        IdentSet.mem ident astate.this_refs
      | _ -> false in
    if this_arg then get_lock_model pn else NoEffect

  (* add or remove permissions from invariant *)
  let hale mk_constr a =
    FieldMap.fold
      (fun f lvar acc ->
         let v = fresh_ident () in
         let cn = mk_constr v lvar (FieldMap.find f a.inv) in
         { acc with curr = FieldMap.add f v acc.curr } |> Domain.add_constr cn
      )
      a.curr
      { a with curr = FieldMap.empty }

  let mk_eq_one p = Exp.eq (Exp.Var p) (Exp.one)
  let mk_gt_zero p = Exp.BinOp (Binop.Gt, Exp.Var p, Exp.zero)
  let mk_add p q r = Exp.eq (Exp.Var p) (Exp.BinOp (Binop.PlusA, Exp.Var q, Exp.Var r))
  let mk_minus p q r = Exp.eq (Exp.Var p) (Exp.BinOp (Binop.MinusA, Exp.Var q, Exp.Var r))

  let exhale = hale mk_minus
  let inhale = hale mk_add

  let do_store fieldname astate =
    let fld_var = FieldMap.find fieldname astate.curr in
    { astate with constraints = ExpSet.add (mk_eq_one fld_var) astate.constraints }
  let do_load fieldname astate =
    let fld_var = FieldMap.find fieldname astate.curr in
    { astate with constraints = ExpSet.add (mk_gt_zero fld_var) astate.constraints }

  (* actual transfer function *)
  let exec_instr astate _ _ cmd =
    (* L.out "Analysing instruction %a@." (Sil.pp_instr Pp.text) cmd ; *)
    match cmd with
    | Sil.Store (Exp.Lfield(Exp.Var v, fieldname, _), _, _, _)
      when IdentSet.mem v astate.this_refs && FieldSet.mem fieldname CF.fields ->
      do_store fieldname astate
    | Sil.Store (Exp.Lfield(l, fieldname, _), _, _, _)
      when Exp.is_this l && FieldSet.mem fieldname CF.fields ->
      do_store fieldname astate
    | Sil.Load (_, Exp.Lfield(Exp.Var v, fieldname, _), _, _)
      when IdentSet.mem v astate.this_refs && FieldSet.mem fieldname CF.fields ->
      do_load fieldname astate
    | Sil.Load (_, Exp.Lfield(l, fieldname, _), _, _)
      when Exp.is_this l && FieldSet.mem fieldname CF.fields ->
      do_load fieldname astate
    | Sil.Load (v,l,_,_) when Exp.is_this l ->
      { astate with this_refs = IdentSet.add v astate.this_refs }
    | Sil.Load (v,Exp.Var v',_,_) when IdentSet.mem v' astate.this_refs ->
      { astate with this_refs = IdentSet.add v astate.this_refs }
    | Sil.Load (v,_,_,_) ->
      { astate with this_refs = IdentSet.remove v astate.this_refs }
    (* | Sil.Load (_,l,_,_) ->
      L.out "***Instruction %a escapes***@." (Sil.pp_instr Pp.text) cmd ;
      L.out "***Root is = %a***@." Exp.pp (Exp.root_of_lexp l) ;
      astate *)
    | Sil.Call (_, Const (Cfun pn), args, _, _) ->
      begin
        match lock_effect_on_this pn args astate with
        | Lock ->     inhale astate
        | Unlock ->   exhale astate
        | NoEffect -> astate
      end
    | _ -> astate
end

module MakeAnalyzer(CF : ClassFields) =
  AbstractInterpreter.Make
    (ProcCfg.Normal)
    (Scheduler.ReversePostorder)
    (MakeTransferFunctions(CF))

(* retrieve the fields of a given class *)
let get_fields tenv pname =
  match pname with
  | Procname.Java java_pname ->
    let current_class = Procname.java_get_class_type_name java_pname in
    begin
      match Tenv.lookup tenv current_class with
      | None -> assert false
      | Some { StructTyp.fields } ->
        FieldSet.of_list (IList.map (fun (fld, _, _) -> fld) fields)
    end
  | _ -> assert false

let method_analysis {Callbacks.proc_desc; tenv; proc_name} =
  let (module CF) =
    (module struct let fields = get_fields tenv proc_name end : ClassFields) in
  let (module Analyzer) =
    (module MakeAnalyzer(CF) :
       AbstractInterpreter.S
       with type TransferFunctions.extras = ProcData.no_extras
        and type TransferFunctions.Domain.astate = astate) in
  let _ = L.out "Analysing %a@." Procname.pp proc_name in
  match Analyzer.compute_post (ProcData.make_default proc_desc tenv) with
  | None -> L.out "Post found = None@."
  | Some a -> L.out "Post found = %a@." Analyzer.TransferFunctions.Domain.pp a

let file_analysis _ _ _ _ = ()
