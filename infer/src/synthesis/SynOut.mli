open! IStd

val print_node_instrs : Procdesc.t -> unit

val c_prog_of_sig : ?body:string -> Parsetree.proc -> string

val pprint_output : Rules.c_instr_node -> Parsetree.procspec -> string
