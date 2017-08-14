open! IStd

val create_pvar_env_list : Prop.sigma -> (Exp.t * Pvar.t) list

val make_spec : Parsetree.procspec -> Tenv.t ->
  Typ.Procname.t -> Prop.exposed Prop.t * Prop.exposed Prop.t
                                         
val get_typ_from_ptr_exn : Typ.t -> Typ.t
