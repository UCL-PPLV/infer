type hpred = 
| Hpred_empty
| Hpred_hpointsto of string * string * string

type atom = 
| Atom_empty

type sigma = hpred list

type pi = atom list

type a_prop = 
| Aprop of pi * sigma

type param = 
| Param of string * string

type proc = 
| Proc of string * param list

type procspec = 
| None
| Procspec of a_prop * proc * a_prop