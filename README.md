# Infer [![Build Status](https://travis-ci.org/facebook/infer.svg?branch=master)](https://travis-ci.org/facebook/infer)

[Infer](http://fbinfer.com/) is a static analysis tool for Java,
Objective-C and C, written in [OCaml](https://ocaml.org/).

## Synthesis
Run `infer synthesize --synth-path [path-to-spec-file]`.

Spec files should be in the form
```
spec ::= "[" pre "]" function_signature "[" post "]"

function_signature ::= ret_type ident "(" params ")"
params ::= /* empty */ | param ("," param)*
param ::= type ident
type ::= "int*" /* for now */
ret_type ::= "void" /* for now */

pre/post ::= pure_formula ";" spatial_formula
pure_formula ::= /* empty for now */
spatial_formula ::= /* empty */ | hpred ("*" hpred)*
hpred ::= ident "|->" ident
```
But for now only the function name is used, pre/posts are not handled yet.

## Installation

Read our [Getting
Started](http://fbinfer.com/docs/getting-started.html) page for
details on how to install packaged versions of Infer. To build Infer
from source, see [INSTALL.md](./INSTALL.md).

## Contributing

See [CONTRIBUTING.md](./CONTRIBUTING.md).

## License

Infer is BSD-licensed. We also provide an additional patent grant.

Note: Enabling Java support may require you to download and install 
components licensed under the GPL.
