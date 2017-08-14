open! IStd

type rule_result = RSuccess of Sil.instr list list | RFail

val write_rule : (Pvar.t * Pvar.t) list ->
  Prop.normal Prop.t ->
  Prop.exposed Prop.t ->
  rule_result



