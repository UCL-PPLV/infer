open! IStd

open PermsDomain

module Summary = Summary.Make (struct
    type summary = PermsDomain.summary

    let update_payload summary payload =
      { payload with Specs.permsafety = Some summary }

    let read_from_payload payload =
      payload.Specs.permsafety
  end)


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
let get_fields pname pdesc =
  match pname with
  | Procname.Java java_pname ->
    let current_class = Procname.java_get_class_type_name java_pname in
    begin
      match Tenv.lookup pdesc.ProcData.tenv current_class with
      | None -> assert false
      | Some { StructTyp.fields } ->
        FieldSet.of_list (IList.map (fun (fld, _, _) -> fld) fields)
    end
  | _ -> assert false

(* compute the summary of a method *)
let compute_post proc_name pdesc =
  let (module CF) =
    (module struct let fields = get_fields proc_name pdesc end : ClassFields) in
  let (module Analyzer) =
    (module MakeAnalyzer(CF) :
       AbstractInterpreter.S
       with type TransferFunctions.extras = ProcData.no_extras
        and type TransferFunctions.Domain.astate = astate) in
  let pdata = ProcData.make_default pdesc.ProcData.pdesc pdesc.ProcData.tenv in
  match Analyzer.compute_post pdata with
  | None -> None
  | Some a ->
    L.out "Found spec: %a@." Analyzer.TransferFunctions.Domain.pp a ;
    Some (mk_summary a)

module Interprocedural = AbstractInterpreter.Interprocedural (Summary)

(* registered method checker *)
let method_analysis callback =
  Interprocedural.compute_and_store_post
    ~compute_post:(compute_post callback.Callbacks.proc_name)
    ~make_extras:ProcData.make_empty_extras
    callback
  |> ignore


let file_analysis _ _ _ _ = ()
