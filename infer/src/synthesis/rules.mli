open! IStd

type c_instr_type = Sil.instr list   
type subst_type = Ident.t * Exp.t
type ident_type = Pvar.t * Typ.t
type points_to_type = Pvar.t * Exp.t

type syn_spec = ident_type list * Prop.exposed Prop.t * Prop.exposed Prop.t 

type c_instr_node = { instrs: c_instr_type
                    ; mutable fst_succ: c_instr_node option
                    ; mutable snd_succ: c_instr_node option}

type rule_result = 
  | RSuccess of syn_spec * c_instr_node
  | RFail

val mk_c_instr_node : ?fst_succ:c_instr_node option -> ?snd_succ:c_instr_node option -> c_instr_type -> c_instr_node

val read_rule : Typ.Procname.t -> ident_type list -> 
  Prop.exposed Prop.t ->
  Prop.exposed Prop.t -> unit -> rule_result

val write_rule : ident_type list -> 
  Prop.exposed Prop.t ->
  Prop.exposed Prop.t -> unit -> rule_result


