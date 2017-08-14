open! IStd

type c_instr_type = Sil.instr list   
type subst_type = Ident.t * Exp.t
type ident_type = Pvar.t * Typ.t
type points_to_type = Pvar.t * Exp.t

type syn_spec = ident_type list * Prop.exposed Prop.t * Prop.exposed Prop.t 

type rule_result = 
  | RSuccess of syn_spec * c_instr_type
  | RFail

val read_rule : Typ.Procname.t -> ident_type list -> 
  Prop.exposed Prop.t ->
  Prop.exposed Prop.t -> unit -> rule_result



