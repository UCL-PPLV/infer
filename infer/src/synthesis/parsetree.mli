type value = 
| Int of int
| Location of string

type hpred = 
| Hpred_empty
| Hpred_hpointsto of string * value

type atom = 
| Atom_empty

type sigma = hpred list

type pi = atom list

type a_prop = {pi: pi; sigma: sigma}

type param = {typ: string; id: string}

type proc = {ret_typ: string; id: string; params: param list}

type procspec = {pre: a_prop; proc: proc; post: a_prop}
