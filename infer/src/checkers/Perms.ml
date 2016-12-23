open! IStd

open PermsDomain

module IdentMap = Ident.IdentMap

module Summary = struct
  include Summary.Make (struct
    type summary = PermsDomain.summary

    let update_payload summary payload =
      { payload with Specs.permsafety = Some summary }

    let read_from_payload payload =
      payload.Specs.permsafety
    end)

  let to_z3 fmt s =
    let z3_ident fmt id = F.pp_print_string fmt (Ident.to_string id) in
    let rec z3_exp fmt e = match e with
      | Exp.Var id -> z3_ident fmt id
      | Exp.BinOp(Binop.Eq, t1, t2) ->
        F.fprintf fmt "(= %a %a)" z3_exp t1 z3_exp t2
      | Exp.BinOp(op, t1, t2) ->
        F.fprintf fmt "(%s %a %a)" (Binop.str Pp.text op) z3_exp t1 z3_exp t2
      | Exp.Const _ ->
        F.pp_print_string fmt (if Exp.is_zero e then "0.0" else "1.0")
      | _ -> assert false in
    let cvars = ExpSet.vars s.sum_constraints in
      IdentSet.iter (F.fprintf fmt "(declare-const %a Real)@." (Ident.pp Pp.text)) cvars ;
      ExpSet.iter (fun c -> F.fprintf fmt "(assert %a)@." z3_exp c) s.sum_constraints ;
      F.fprintf fmt "(check-sat)@.(get-model)"

  let mk { pre; inv; constraints } =
    {
      sum_pre = pre;
      sum_inv = inv;
      sum_constraints = constraints;
    }

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

let get_class = function
  | Procname.Java java_pname -> Procname.java_get_class_type_name java_pname
  | _ -> assert false

(* retrieve the fields of a given class *)
let get_fields pname pdesc =
  match Tenv.lookup pdesc.ProcData.tenv (get_class pname) with
  | None -> assert false
  | Some { StructTyp.fields } ->
    FieldSet.of_list (IList.map (fun (fld, _, _) -> fld) fields)

module Interprocedural = AbstractInterpreter.Interprocedural (Summary)

(* compute the summary of a method *)
let compute_and_store_post callback =
  let compute_post pdesc =
    let (module CF) =
      (module struct
        let fields = get_fields callback.Callbacks.proc_name pdesc
      end : ClassFields) in
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
      Some (Summary.mk a) in
  Interprocedural.compute_and_store_post
    ~compute_post:compute_post
    ~make_extras:ProcData.make_empty_extras
    callback

(* registered method checker *)
let method_analysis callback =
  ignore (compute_and_store_post callback)


let merge s1o s2o =
  let subst_ident theta v =
    if IdentMap.mem v theta then IdentMap.find v theta else v in
  let rec subst theta t =
    match t with
    | Exp.Var v -> Exp.Var (subst_ident theta v)
    | Exp.BinOp(op, t1, t2) -> Exp.BinOp(op, subst theta t1, subst theta t2)
    | _ -> t in
  match s1o, s2o with
  | None, _ | _, None -> None
  | Some s1, Some s2 ->
  assert (FieldMap.cardinal s1.sum_pre = FieldMap.cardinal s2.sum_pre) ;
  assert (FieldMap.cardinal s1.sum_inv = FieldMap.cardinal s2.sum_inv) ;
  assert (FieldMap.cardinal s1.sum_pre = FieldMap.cardinal s2.sum_inv) ;
  let seed m1 m2 a =
    FieldMap.fold
      (fun f v (a1,a2) ->
         let newv = fresh_ident () in
         let a1' = IdentMap.add v newv a1 in
         let a2' = IdentMap.add (FieldMap.find f m2) newv a2 in
         (a1',a2'))
      m1
      a in
  let theta1, theta2 = seed s1.sum_pre s2.sum_pre (IdentMap.empty, IdentMap.empty) in
  let theta1, theta2 = seed s1.sum_inv s2.sum_inv (theta1, theta2) in
  let c1vars, c2vars = ExpSet.vars s1.sum_constraints, ExpSet.vars s1.sum_constraints in
  let exist1 = IdentSet.filter (fun v -> not (IdentMap.mem v theta1)) c1vars in
  let exist2 = IdentSet.filter (fun v -> not (IdentMap.mem v theta2)) c2vars in
  let add_fresh v a = IdentMap.add v (fresh_ident ()) a in
  let theta1 = IdentSet.fold add_fresh exist1 theta1 in
  let theta2 = IdentSet.fold add_fresh exist2 theta2 in
  let c1 = ExpSet.map (subst theta1) s1.sum_constraints in
  let c2 = ExpSet.map (subst theta2) s2.sum_constraints in
  Some {
    sum_pre = FieldMap.map (subst_ident theta1) s1.sum_pre;
    sum_inv = FieldMap.map (subst_ident theta1) s1.sum_inv;
    sum_constraints = ExpSet.union c1 c2
  }

let all_pairs =
  let pair a l = IList.map (fun b -> (a,b)) l in
  let rec aux = function
    | [] -> []
    | (x::xs) as all -> (pair x all) @ (aux xs) in
  aux

module ClassMap =
  Caml.Map.Make(struct type t = Typename.t let compare = Typename.compare end)

let read_process_lines in_channel =
  let lines = ref [] in
  begin
    try
      while true do
        lines := input_line in_channel :: !lines
      done;
    with End_of_file ->
      ()
  end;
  List.rev !lines

let file_analysis _ _ get_proc_desc file_env =
  L.out "file analysis running@." ;
  let summarise (idenv, tenv, proc_name, proc_desc) =
    let callback =
      {Callbacks.get_proc_desc; get_procs_in_file = (fun _ -> []);
       idenv; tenv; proc_name; proc_desc} in
    compute_and_store_post callback in
  let classmap =
    IList.fold_left
      (fun a ((_,_,pname,_) as p) ->
         let c = get_class pname in
         let procs = try ClassMap.find c a with Not_found -> [] in
         ClassMap.add c (p::procs) a
      )
      ClassMap.empty
      file_env in
  let process_case fmt (_,_,s) =
    match s with
    | None -> ()
    | Some sum -> F.fprintf fmt "%a@." Summary.to_z3 sum in
  let analyse_class _ procs =
    let summaries = IList.map (fun p -> (p, summarise p)) procs in
    let pairs = all_pairs summaries in
    let merged =
      IList.map (fun ((p1,s1),(p2,s2)) -> (p1,p2,merge s1 s2)) pairs in
    let in_ch,out_ch = Unix.open_process "z3 -in" in
    let fmt = F.formatter_of_out_channel out_ch in
    IList.iter (process_case fmt) merged ;
    F.pp_print_flush fmt () ;
    Out_channel.close out_ch ;
    let lines = read_process_lines in_ch in
    IList.iter (fun l -> L.out "Z3: %s@." l) lines ;
    ignore (Unix.close_process (in_ch, out_ch)) in
  ClassMap.iter analyse_class classmap
