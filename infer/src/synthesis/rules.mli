open! IStd

type rule_result = 
  | RSuccess of Sil.instr list list * Prop.exposed Prop.t * Prop.exposed Prop.t 
  | RFail

val read_rule : Typ.Procname.t -> (Pvar.t * Typ.t) list -> 
  Prop.exposed Prop.t -> Prop.exposed Prop.t -> unit -> rule_result



