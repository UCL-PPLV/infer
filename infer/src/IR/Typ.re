/*
 * Copyright (c) 2009 - 2013 Monoidics ltd.
 * Copyright (c) 2013 - present Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 */
open! IStd;

module Hashtbl = Caml.Hashtbl;


/** The Smallfoot Intermediate Language: Types */
module L = Logging;

module F = Format;


/** Kinds of integers */
type ikind =
  | IChar /** [char] */
  | ISChar /** [signed char] */
  | IUChar /** [unsigned char] */
  | IBool /** [bool] */
  | IInt /** [int] */
  | IUInt /** [unsigned int] */
  | IShort /** [short] */
  | IUShort /** [unsigned short] */
  | ILong /** [long] */
  | IULong /** [unsigned long] */
  | ILongLong /** [long long] (or [_int64] on Microsoft Visual C) */
  | IULongLong /** [unsigned long long] (or [unsigned _int64] on Microsoft Visual C) */
  | I128 /** [__int128_t] */
  | IU128 /** [__uint128_t] */
[@@deriving compare];

let ikind_to_string =
  fun
  | IChar => "char"
  | ISChar => "signed char"
  | IUChar => "unsigned char"
  | IBool => "_Bool"
  | IInt => "int"
  | IUInt => "unsigned int"
  | IShort => "short"
  | IUShort => "unsigned short"
  | ILong => "long"
  | IULong => "unsigned long"
  | ILongLong => "long long"
  | IULongLong => "unsigned long long"
  | I128 => "__int128_t"
  | IU128 => "__uint128_t";

let ikind_is_char =
  fun
  | IChar
  | ISChar
  | IUChar => true
  | _ => false;

let ikind_is_unsigned =
  fun
  | IUChar
  | IUInt
  | IUShort
  | IULong
  | IULongLong => true
  | _ => false;

let int_of_int64_kind i ik => IntLit.of_int64_unsigned i (ikind_is_unsigned ik);


/** Kinds of floating-point numbers */
type fkind =
  | FFloat /** [float] */
  | FDouble /** [double] */
  | FLongDouble /** [long double] */
[@@deriving compare];

let fkind_to_string =
  fun
  | FFloat => "float"
  | FDouble => "double"
  | FLongDouble => "long double";


/** kind of pointer */
type ptr_kind =
  | Pk_pointer /** C/C++, Java, Objc standard/__strong pointer */
  | Pk_reference /** C++ reference */
  | Pk_objc_weak /** Obj-C __weak pointer */
  | Pk_objc_unsafe_unretained /** Obj-C __unsafe_unretained pointer */
  | Pk_objc_autoreleasing /** Obj-C __autoreleasing pointer */
[@@deriving compare];

let equal_ptr_kind = [%compare.equal : ptr_kind];

let ptr_kind_string =
  fun
  | Pk_reference => "&"
  | Pk_pointer => "*"
  | Pk_objc_weak => "__weak *"
  | Pk_objc_unsafe_unretained => "__unsafe_unretained *"
  | Pk_objc_autoreleasing => "__autoreleasing *";

module T = {
  type type_quals = {is_const: bool, is_restrict: bool, is_volatile: bool} [@@deriving compare];

  /** types for sil (structured) expressions */
  type t = {desc, quals: type_quals} [@@deriving compare]
  and desc =
    | Tint ikind /** integer type */
    | Tfloat fkind /** float type */
    | Tvoid /** void type */
    | Tfun bool /** function type with noreturn attribute */
    | Tptr t ptr_kind /** pointer type */
    | Tstruct name /** structured value type name */
    | Tarray t (option IntLit.t) (option IntLit.t) /** array type with statically fixed length and stride */
  [@@deriving compare]
  and name =
    | CStruct QualifiedCppName.t
    | CUnion QualifiedCppName.t
    | CppClass QualifiedCppName.t template_spec_info
    | JavaClass Mangled.t
    | ObjcClass QualifiedCppName.t
    | ObjcProtocol QualifiedCppName.t
  [@@deriving compare]
  and template_spec_info =
    | NoTemplate
    | Template (list (option t))
  [@@deriving compare];
  let equal_desc = [%compare.equal : desc];
  let equal_quals = [%compare.equal : type_quals];
  let equal = [%compare.equal : t];
  let hash = Hashtbl.hash;
};

include T;

let mk_type_quals ::default=? ::is_const=? ::is_restrict=? ::is_volatile=? () => {
  let default_ = {is_const: false, is_restrict: false, is_volatile: false};
  let mk_aux
      ::default=default_
      ::is_const=default.is_const
      ::is_restrict=default.is_restrict
      ::is_volatile=default.is_volatile
      () => {
    is_const,
    is_restrict,
    is_volatile
  };
  mk_aux ::?default ::?is_const ::?is_restrict ::?is_volatile ()
};

let is_const {is_const} => is_const;

let is_restrict {is_restrict} => is_restrict;

let is_volatile {is_volatile} => is_volatile;

let mk ::default=? ::quals=? desc :t => {
  let default_ = {desc, quals: mk_type_quals ()};
  let mk_aux ::default=default_ ::quals=default.quals desc => {desc, quals};
  mk_aux ::?default ::?quals desc
};

let escape pe =>
  if (Pp.equal_print_kind pe.Pp.kind Pp.HTML) {
    Escape.escape_xml
  } else {
    ident
  };


/** Pretty print a type with all the details, using the C syntax. */
let rec pp_full pe f typ => {
  let pp_quals f {quals} => {
    if (is_const quals) {
      F.fprintf f " const "
    };
    if (is_restrict quals) {
      F.fprintf f " __restrict "
    };
    if (is_volatile quals) {
      F.fprintf f " volatile "
    }
  };
  let pp_desc f {desc} =>
    switch desc {
    | Tstruct tname => F.fprintf f "%a" (pp_name_c_syntax pe) tname
    | Tint ik => F.fprintf f "%s" (ikind_to_string ik)
    | Tfloat fk => F.fprintf f "%s" (fkind_to_string fk)
    | Tvoid => F.fprintf f "void"
    | Tfun false => F.fprintf f "_fn_"
    | Tfun true => F.fprintf f "_fn_noreturn_"
    | Tptr ({desc: Tarray _ | Tfun _} as typ) pk =>
      F.fprintf f "%a(%s)" (pp_full pe) typ (ptr_kind_string pk |> escape pe)
    | Tptr typ pk => F.fprintf f "%a%s" (pp_full pe) typ (ptr_kind_string pk |> escape pe)
    | Tarray typ static_len static_stride =>
      let pp_int_opt fmt => (
        fun
        | Some x => IntLit.pp fmt x
        | None => F.fprintf fmt "_"
      );
      F.fprintf f "%a[%a*%a]" (pp_full pe) typ pp_int_opt static_len pp_int_opt static_stride
    };
  F.fprintf f "%a%a" pp_desc typ pp_quals typ
}
and pp_name_c_syntax pe f =>
  fun
  | CStruct name
  | CUnion name
  | ObjcClass name
  | ObjcProtocol name => F.fprintf f "%a" QualifiedCppName.pp name
  | CppClass name template_spec =>
    F.fprintf f "%a%a" QualifiedCppName.pp name (pp_template_spec_info pe) template_spec
  | JavaClass name => F.fprintf f "%a" Mangled.pp name
and pp_template_spec_info pe f =>
  fun
  | NoTemplate => ()
  | Template args => {
      let pp_arg_opt f => (
        fun
        | Some typ => F.fprintf f "%a" (pp_full pe) typ
        | None => F.fprintf f "_"
      );
      F.fprintf f "%s%a%s" (escape pe "<") (Pp.comma_seq pp_arg_opt) args (escape pe ">")
    };


/** Pretty print a type. Do nothing by default. */
let pp pe f te =>
  if Config.print_types {
    pp_full pe f te
  } else {
    ()
  };

let to_string typ => {
  let pp fmt => pp_full Pp.text fmt typ;
  F.asprintf "%t" pp
};

module Name = {
  type t = name [@@deriving compare];
  let equal = [%compare.equal : t];
  let qual_name =
    fun
    | CStruct name
    | CUnion name
    | ObjcClass name
    | ObjcProtocol name => name
    | CppClass name templ_args => {
        let template_suffix = F.asprintf "%a" (pp_template_spec_info Pp.text) templ_args;
        QualifiedCppName.append_template_args_to_last name args::template_suffix
      }
    | JavaClass _ => QualifiedCppName.empty;
  let unqualified_name =
    fun
    | CStruct name
    | CUnion name
    | ObjcClass name
    | ObjcProtocol name => name
    | CppClass name _ => name
    | JavaClass _ => QualifiedCppName.empty;
  let name n =>
    switch n {
    | CStruct _
    | CUnion _
    | CppClass _ _
    | ObjcClass _
    | ObjcProtocol _ => qual_name n |> QualifiedCppName.to_qual_string
    | JavaClass name => Mangled.to_string name
    };
  let pp fmt tname => {
    let prefix =
      fun
      | CStruct _ => "struct"
      | CUnion _ => "union"
      | CppClass _ _
      | JavaClass _
      | ObjcClass _ => "class"
      | ObjcProtocol _ => "protocol";
    F.fprintf fmt "%s %a" (prefix tname) (pp_name_c_syntax Pp.text) tname
  };
  let to_string = F.asprintf "%a" pp;
  let is_class =
    fun
    | CppClass _ _
    | JavaClass _
    | ObjcClass _ => true
    | _ => false;
  let is_same_type t1 t2 =>
    switch (t1, t2) {
    | (CStruct _, CStruct _)
    | (CUnion _, CUnion _)
    | (CppClass _ _, CppClass _ _)
    | (JavaClass _, JavaClass _)
    | (ObjcClass _, ObjcClass _)
    | (ObjcProtocol _, ObjcProtocol _) => true
    | _ => false
    };
  module C = {
    let from_qual_name qual_name => CStruct qual_name;
    let from_string name_str => QualifiedCppName.of_qual_string name_str |> from_qual_name;
    let union_from_qual_name qual_name => CUnion qual_name;
  };
  module Java = {
    let from_string name_str => JavaClass (Mangled.from_string name_str);
    let from_package_class package_name class_name =>
      if (String.equal package_name "") {
        from_string class_name
      } else {
        from_string (package_name ^ "." ^ class_name)
      };
    let is_class =
      fun
      | JavaClass _ => true
      | _ => false;
    let java_lang_object = from_string "java.lang.Object";
    let java_io_serializable = from_string "java.io.Serializable";
    let java_lang_cloneable = from_string "java.lang.Cloneable";
  };
  module Cpp = {
    let from_qual_name template_spec_info qual_name => CppClass qual_name template_spec_info;
    let is_class =
      fun
      | CppClass _ => true
      | _ => false;
  };
  module Objc = {
    let from_qual_name qual_name => ObjcClass qual_name;
    let from_string name_str => QualifiedCppName.of_qual_string name_str |> from_qual_name;
    let protocol_from_qual_name qual_name => ObjcProtocol qual_name;
    let is_class =
      fun
      | ObjcClass _ => true
      | _ => false;
  };
  module Set =
    Caml.Set.Make {
      type nonrec t = t;
      let compare = compare;
    };
};


/** {2 Sets and maps of types} */
module Set = Caml.Set.Make T;

module Map = Caml.Map.Make T;

module Tbl = Hashtbl.Make T;


/** dump a type with all the details. */
let d_full (t: t) => L.add_print_action (L.PTtyp_full, Obj.repr t);


/** dump a list of types. */
let d_list (tl: list t) => L.add_print_action (L.PTtyp_list, Obj.repr tl);

let name typ =>
  switch typ.desc {
  | Tstruct name => Some name
  | _ => None
  };

let unsome s =>
  fun
  | Some default_typ => default_typ
  | None => {
      L.err "No default typ in %s@." s;
      assert false
    };


/** turn a *T into a T. fails if [typ] is not a pointer type */
let strip_ptr typ =>
  switch typ.desc {
  | Tptr t _ => t
  | _ => assert false
  };


/** If an array type, return the type of the element.
    If not, return the default type if given, otherwise raise an exception */
let array_elem default_opt typ =>
  switch typ.desc {
  | Tarray t_el _ _ => t_el
  | _ => unsome "array_elem" default_opt
  };

let is_class_of_kind check_fun typ =>
  switch typ.desc {
  | Tstruct tname => check_fun tname
  | _ => false
  };

let is_objc_class = is_class_of_kind Name.Objc.is_class;

let is_cpp_class = is_class_of_kind Name.Cpp.is_class;

let is_java_class = is_class_of_kind Name.Java.is_class;

let rec is_array_of_cpp_class typ =>
  switch typ.desc {
  | Tarray typ _ _ => is_array_of_cpp_class typ
  | _ => is_cpp_class typ
  };

let is_pointer_to_cpp_class typ =>
  switch typ.desc {
  | Tptr t _ => is_cpp_class t
  | _ => false
  };

let has_block_prefix s =>
  switch (Str.split_delim (Str.regexp_string Config.anonymous_block_prefix) s) {
  | [_, _, ..._] => true
  | _ => false
  };


/** Check if type is a type for a block in objc */
let is_block_type typ => has_block_prefix (to_string typ);


/** Java types by name */
let rec java_from_string: string => t =
  fun
  | ""
  | "void" => mk Tvoid
  | "int" => mk (Tint IInt)
  | "byte" => mk (Tint IShort)
  | "short" => mk (Tint IShort)
  | "boolean" => mk (Tint IBool)
  | "char" => mk (Tint IChar)
  | "long" => mk (Tint ILong)
  | "float" => mk (Tfloat FFloat)
  | "double" => mk (Tfloat FDouble)
  | typ_str when String.contains typ_str '[' => {
      let stripped_typ = String.sub typ_str pos::0 len::(String.length typ_str - 2);
      mk (Tptr (mk (Tarray (java_from_string stripped_typ) None None)) Pk_pointer)
    }
  | typ_str => mk (Tstruct (Name.Java.from_string typ_str));

type typ = t;

module Procname = {
  /* e.g. ("", "int") for primitive types or ("java.io", "PrintWriter") for objects */
  type java_type = (option string, string);
  /* compare in inverse order */
  let compare_java_type (p1, c1) (p2, c2) =>
    [%compare : (string, option string)] (c1, p1) (c2, p2);
  type method_kind =
    | Non_Static /* in Java, procedures called with invokevirtual, invokespecial, and invokeinterface */
    | Static /* in Java, procedures called with invokestatic */
  [@@deriving compare];
  let equal_method_kind = [%compare.equal : method_kind];

  /** Type of java procedure names. */
  type java = {
    method_name: string,
    parameters: list java_type,
    class_name: Name.t,
    return_type: option java_type, /* option because constructors have no return type */
    kind: method_kind
  }
  [@@deriving compare];

  /** Type of c procedure names. */
  type c = {
    name: QualifiedCppName.t,
    mangled: option string,
    template_args: template_spec_info,
    is_generic_model: bool
  }
  [@@deriving compare];
  type objc_cpp_method_kind =
    | CPPMethod (option string) /** with mangling */
    | CPPConstructor (option string, bool) /** with mangling + is it constexpr? */
    | ObjCClassMethod
    | ObjCInstanceMethod
    | ObjCInternalMethod
  [@@deriving compare];

  /** Type of Objective C and C++ procedure names: method signatures. */
  type objc_cpp = {
    method_name: string,
    class_name: Name.t,
    kind: objc_cpp_method_kind,
    template_args: template_spec_info,
    is_generic_model: bool
  }
  [@@deriving compare];

  /** Type of Objective C block names. */
  type block = string [@@deriving compare];

  /** Type of procedure names. */
  type t =
    | Java java
    | C c
    | Linters_dummy_method
    | Block block
    | ObjC_Cpp objc_cpp
  [@@deriving compare];
  let equal = [%compare.equal : t];

  /** Level of verbosity of some to_string functions. */
  type detail_level =
    | Verbose
    | Non_verbose
    | Simple
  [@@deriving compare];
  let equal_detail_level = [%compare.equal : detail_level];
  let objc_method_kind_of_bool is_instance =>
    if is_instance {ObjCInstanceMethod} else {ObjCClassMethod};
  let empty_block = Block "";
  let is_verbose v =>
    switch v {
    | Verbose => true
    | _ => false
    };

  /** A type is a pair (package, type_name) that is translated in a string package.type_name */
  let java_type_to_string_verbosity p verbosity =>
    switch p {
    | (None, typ) => typ
    | (Some p, cls) =>
      if (is_verbose verbosity) {
        p ^ "." ^ cls
      } else {
        cls
      }
    };
  let java_type_to_string p => java_type_to_string_verbosity p Verbose;

  /** Given a list of types, it creates a unique string of types separated by commas */
  let rec java_param_list_to_string inputList verbosity =>
    switch inputList {
    | [] => ""
    | [head] => java_type_to_string_verbosity head verbosity
    | [head, ...rest] =>
      java_type_to_string_verbosity head verbosity ^ "," ^ java_param_list_to_string rest verbosity
    };

  /** It is the same as java_type_to_string, but Java return types are optional because of constructors without type */
  let java_return_type_to_string j verbosity =>
    switch j.return_type {
    | None => ""
    | Some typ => java_type_to_string_verbosity typ verbosity
    };

  /** Given a package.class_name string, it looks for the latest dot and split the string
      in two (package, class_name) */
  let split_classname package_classname =>
    switch (String.rsplit2 package_classname on::'.') {
    | Some (x, y) => (Some x, y)
    | None => (None, package_classname)
    };
  let split_typename typename => split_classname (Name.name typename);
  let c name mangled template_args ::is_generic_model => {
    name,
    mangled: Some mangled,
    template_args,
    is_generic_model
  };
  let from_string_c_fun (name: string) =>
    C {
      name: QualifiedCppName.of_qual_string name,
      mangled: None,
      template_args: NoTemplate,
      is_generic_model: false
    };
  let java class_name return_type method_name parameters kind => {
    class_name,
    return_type,
    method_name,
    parameters,
    kind
  };

  /** Create an objc procedure name from a class_name and method_name. */
  let objc_cpp class_name method_name kind template_args ::is_generic_model => {
    class_name,
    method_name,
    kind,
    template_args,
    is_generic_model
  };
  let get_default_objc_class_method objc_class => {
    let objc_cpp =
      objc_cpp objc_class "__find_class_" ObjCInternalMethod NoTemplate is_generic_model::false;
    ObjC_Cpp objc_cpp
  };

  /** Create an objc procedure name from a class_name and method_name. */
  let mangled_objc_block name => Block name;
  let is_java =
    fun
    | Java _ => true
    | _ => false;
  let is_c_method =
    fun
    | ObjC_Cpp _ => true
    | _ => false;
  let is_constexpr =
    fun
    | ObjC_Cpp {kind: CPPConstructor (_, true)} => true
    | _ => false;

  /** Replace the class name component of a procedure name.
      In case of Java, replace package and class name. */
  let replace_class t (new_class: Name.t) =>
    switch t {
    | Java j => Java {...j, class_name: new_class}
    | ObjC_Cpp osig => ObjC_Cpp {...osig, class_name: new_class}
    | C _
    | Block _
    | Linters_dummy_method => t
    };

  /** Get the class name of a Objective-C/C++ procedure name. */
  let objc_cpp_get_class_name objc_cpp => Name.name objc_cpp.class_name;
  let objc_cpp_get_class_type_name objc_cpp => objc_cpp.class_name;

  /** Return the package.classname of a java procname. */
  let java_get_class_name (j: java) => Name.name j.class_name;

  /** Return the package.classname as a typename of a java procname. */
  let java_get_class_type_name (j: java) => j.class_name;

  /** Return the class name of a java procedure name. */
  let java_get_simple_class_name (j: java) => snd (split_classname (java_get_class_name j));

  /** Return the package of a java procname. */
  let java_get_package (j: java) => fst (split_classname (java_get_class_name j));

  /** Return the method of a java procname. */
  let java_get_method (j: java) => j.method_name;

  /** Replace the method of a java procname. */
  let java_replace_method (j: java) mname => {...j, method_name: mname};

  /** Replace the return type of a java procname. */
  let java_replace_return_type j ret_type => {...j, return_type: Some ret_type};

  /** Replace the parameters of a java procname. */
  let java_replace_parameters j parameters => {...j, parameters};

  /** Return the method/function of a procname. */
  let get_method =
    fun
    | ObjC_Cpp name => name.method_name
    | C {name} => QualifiedCppName.to_qual_string name
    | Block name => name
    | Java j => j.method_name
    | Linters_dummy_method => "Linters_dummy_method";

  /** Return the language of the procedure. */
  let get_language =
    fun
    | ObjC_Cpp _ => Config.Clang
    | C _ => Config.Clang
    | Block _ => Config.Clang
    | Linters_dummy_method => Config.Clang
    | Java _ => Config.Java;

  /** Return the return type of a java procname. */
  let java_get_return_type (j: java) => java_return_type_to_string j Verbose;

  /** Return the parameters of a java procname. */
  let java_get_parameters j => j.parameters;

  /** Return the parameters of a java procname as strings. */
  let java_get_parameters_as_strings j =>
    List.map f::(fun param => java_type_to_string param) j.parameters;

  /** Return true if the java procedure is static */
  let java_is_static =
    fun
    | Java j => equal_method_kind j.kind Static
    | _ => false;
  let java_is_lambda =
    fun
    | Java j => String.is_prefix prefix::"lambda$" j.method_name
    | _ => false;

  /** Prints a string of a java procname with the given level of verbosity */
  let java_to_string ::withclass=false (j: java) verbosity =>
    switch verbosity {
    | Verbose
    | Non_verbose =>
      /* if verbose, then package.class.method(params): rtype,
         else rtype package.class.method(params)
         verbose is used for example to create unique filenames, non_verbose to create reports */
      let return_type = java_return_type_to_string j verbosity;
      let params = java_param_list_to_string j.parameters verbosity;
      let class_name = java_type_to_string_verbosity (split_typename j.class_name) verbosity;
      let separator =
        switch (j.return_type, verbosity) {
        | (None, _) => ""
        | (Some _, Verbose) => ":"
        | _ => " "
        };
      let output = class_name ^ "." ^ j.method_name ^ "(" ^ params ^ ")";
      if (equal_detail_level verbosity Verbose) {
        output ^ separator ^ return_type
      } else {
        return_type ^ separator ^ output
      }
    | Simple =>
      /* methodname(...) or without ... if there are no parameters */
      let cls_prefix =
        if withclass {
          java_type_to_string_verbosity (split_typename j.class_name) verbosity ^ "."
        } else {
          ""
        };
      let params =
        switch j.parameters {
        | [] => ""
        | _ => "..."
        };
      let method_name =
        if (String.equal j.method_name "<init>") {
          java_get_simple_class_name j
        } else {
          cls_prefix ^ j.method_name
        };
      method_name ^ "(" ^ params ^ ")"
    };

  /** Check if the class name is for an anonymous inner class. */
  let is_anonymous_inner_class_name class_name => {
    let class_name_no_package = snd (split_typename class_name);
    switch (String.rsplit2 class_name_no_package on::'$') {
    | Some (_, s) =>
      let is_int =
        try {
          ignore (int_of_string (String.strip s));
          true
        } {
        | Failure _ => false
        };
      is_int
    | None => false
    }
  };

  /** Check if the procedure belongs to an anonymous inner class. */
  let java_is_anonymous_inner_class =
    fun
    | Java j => is_anonymous_inner_class_name j.class_name
    | _ => false;

  /** Check if the last parameter is a hidden inner class, and remove it if present.
      This is used in private constructors, where a proxy constructor is generated
      with an extra parameter and calls the normal constructor. */
  let java_remove_hidden_inner_class_parameter =
    fun
    | Java js =>
      switch (List.rev js.parameters) {
      | [(_, s), ...par'] =>
        if (is_anonymous_inner_class_name (Name.Java.from_string s)) {
          Some (Java {...js, parameters: List.rev par'})
        } else {
          None
        }
      | [] => None
      }
    | _ => None;

  /** Check if the procedure name is an anonymous inner class constructor. */
  let java_is_anonymous_inner_class_constructor =
    fun
    | Java js => is_anonymous_inner_class_name js.class_name
    | _ => false;

  /** Check if the procedure name is an acess method (e.g. access$100 used to
      access private members from a nested class. */
  let java_is_access_method =
    fun
    | Java js =>
      switch (String.rsplit2 js.method_name on::'$') {
      | Some ("access", s) =>
        let is_int =
          try {
            ignore (int_of_string s);
            true
          } {
          | Failure _ => false
          };
        is_int
      | _ => false
      }
    | _ => false;

  /** Check if the procedure name is of an auto-generated method containing '$'. */
  let java_is_autogen_method =
    fun
    | Java js => String.contains js.method_name '$'
    | _ => false;

  /** Check if the proc name has the type of a java vararg.
      Note: currently only checks that the last argument has type Object[]. */
  let java_is_vararg =
    fun
    | Java js =>
      switch (List.rev js.parameters) {
      | [(_, "java.lang.Object[]"), ..._] => true
      | _ => false
      }
    | _ => false;
  let is_objc_constructor method_name =>
    String.equal method_name "new" || String.is_prefix prefix::"init" method_name;
  let is_objc_kind =
    fun
    | ObjCClassMethod
    | ObjCInstanceMethod
    | ObjCInternalMethod => true
    | _ => false;

  /** [is_constructor pname] returns true if [pname] is a constructor */
  let is_constructor =
    fun
    | Java js => String.equal js.method_name "<init>"
    | ObjC_Cpp {kind: CPPConstructor _} => true
    | ObjC_Cpp {kind, method_name} when is_objc_kind kind => is_objc_constructor method_name
    | _ => false;
  let is_objc_dealloc method_name => String.equal method_name "dealloc";

  /** [is_dealloc pname] returns true if [pname] is the dealloc method in Objective-C
      TODO: add case for C++ */
  let is_destructor =
    fun
    | ObjC_Cpp name => is_objc_dealloc name.method_name
    | _ => false;
  let java_is_close =
    fun
    | Java js => String.equal js.method_name "close"
    | _ => false;

  /** [is_class_initializer pname] returns true if [pname] is a class initializer */
  let is_class_initializer =
    fun
    | Java js => String.equal js.method_name "<clinit>"
    | _ => false;

  /** [is_infer_undefined pn] returns true if [pn] is a special Infer undefined proc */
  let is_infer_undefined pn =>
    switch pn {
    | Java j =>
      let regexp = Str.regexp "com.facebook.infer.builtins.InferUndefined";
      Str.string_match regexp (java_get_class_name j) 0
    | _ =>
      /* TODO: add cases for obj-c, c, c++ */
      false
    };
  let get_global_name_of_initializer =
    fun
    | C {name}
        when
          String.is_prefix
            prefix::Config.clang_initializer_prefix (QualifiedCppName.to_qual_string name) => {
        let name_str = QualifiedCppName.to_qual_string name;
        let prefix_len = String.length Config.clang_initializer_prefix;
        Some (String.sub name_str pos::prefix_len len::(String.length name_str - prefix_len))
      }
    | _ => None;

  /** to_string for C_function type */
  let to_readable_string (c1, c2) verbose => {
    let plain = QualifiedCppName.to_qual_string c1;
    if verbose {
      switch c2 {
      | None => plain
      | Some s => plain ^ "{" ^ s ^ "}"
      }
    } else {
      plain
    }
  };
  let c_method_kind_verbose_str kind =>
    switch kind {
    | CPPMethod m =>
      "(" ^
      (
        switch m {
        | None => ""
        | Some s => s
        }
      ) ^ ")"
    | CPPConstructor (m, is_constexpr) =>
      "{" ^
      (
        switch m {
        | None => ""
        | Some s => s
        }
      ) ^
      (if is_constexpr {"|constexpr"} else {""}) ^ "}"
    | ObjCClassMethod => "class"
    | ObjCInstanceMethod => "instance"
    | ObjCInternalMethod => "internal"
    };
  let c_method_to_string osig detail_level =>
    switch detail_level {
    | Simple => osig.method_name
    | Non_verbose => Name.name osig.class_name ^ "_" ^ osig.method_name
    | Verbose =>
      let m_str = c_method_kind_verbose_str osig.kind;
      Name.name osig.class_name ^ "_" ^ osig.method_name ^ m_str
    };

  /** Very verbose representation of an existing Procname.t */
  let to_unique_id pn =>
    switch pn {
    | Java j => java_to_string j Verbose
    | C {name, mangled} => to_readable_string (name, mangled) true
    | ObjC_Cpp osig => c_method_to_string osig Verbose
    | Block name => name
    | Linters_dummy_method => "Linters_dummy_method"
    };

  /** Convert a proc name to a string for the user to see */
  let to_string p =>
    switch p {
    | Java j => java_to_string j Non_verbose
    | C {name, mangled} => to_readable_string (name, mangled) false
    | ObjC_Cpp osig => c_method_to_string osig Non_verbose
    | Block name => name
    | Linters_dummy_method => to_unique_id p
    };

  /** Convenient representation of a procname for external tools (e.g. eclipse plugin) */
  let to_simplified_string ::withclass=false p =>
    switch p {
    | Java j => java_to_string ::withclass j Simple
    | C {name, mangled} => to_readable_string (name, mangled) false ^ "()"
    | ObjC_Cpp osig => c_method_to_string osig Simple
    | Block _ => "block"
    | Linters_dummy_method => to_unique_id p
    };

  /** Pretty print a proc name */
  let pp f pn => F.fprintf f "%s" (to_string pn);

  /** hash function for procname */
  let hash_pname = Hashtbl.hash;
  module Hash =
    Hashtbl.Make {
      type nonrec t = t;
      let equal = equal;
      let hash = hash_pname;
    };
  module Map =
    PrettyPrintable.MakePPMap {
      type nonrec t = t;
      let compare = compare;
      let pp = pp;
    };
  module Set =
    PrettyPrintable.MakePPSet {
      type nonrec t = t;
      let compare = compare;
      let pp = pp;
    };

  /** Pretty print a set of proc names */
  let pp_set fmt set => Set.iter (fun pname => F.fprintf fmt "%a " pp pname) set;
  let objc_cpp_get_class_qualifiers objc_cpp => Name.qual_name objc_cpp.class_name;
  let get_qualifiers pname =>
    switch pname {
    | C {name} => name
    | ObjC_Cpp objc_cpp =>
      objc_cpp_get_class_qualifiers objc_cpp |>
      QualifiedCppName.append_qualifier qual::objc_cpp.method_name
    | _ => QualifiedCppName.empty
    };

  /** Convert a proc name to a filename */
  let to_concrete_filename pname => {
    /* filenames for clang procs are REVERSED qualifiers with '#' as separator */
    let get_qual_name_str pname =>
      get_qualifiers pname |> QualifiedCppName.to_rev_list |> String.concat sep::"#";
    let proc_id =
      switch pname {
      | C {mangled} =>
        [get_qual_name_str pname, ...Option.to_list mangled] |> String.concat sep::"#"
      | ObjC_Cpp objc_cpp =>
        get_qual_name_str pname ^ "#" ^ c_method_kind_verbose_str objc_cpp.kind
      | _ => to_unique_id pname
      };
    Escape.escape_filename @@ DB.append_crc_cutoff proc_id
  };
  let to_generic_filename pname => {
    let proc_id =
      get_qualifiers pname |> QualifiedCppName.strip_template_args |> QualifiedCppName.to_rev_list |>
      String.concat sep::"#";
    Escape.escape_filename @@ DB.append_crc_cutoff proc_id
  };
  let to_filename pname =>
    switch pname {
    | C {is_generic_model}
    | ObjC_Cpp {is_generic_model} when Bool.equal is_generic_model true =>
      to_generic_filename pname
    | _ => to_concrete_filename pname
    };
};


/** Return the return type of [pname_java]. */
let java_proc_return_typ pname_java :t => {
  let typ = java_from_string (Procname.java_get_return_type pname_java);
  switch typ.desc {
  | Tstruct _ => mk (Tptr typ Pk_pointer)
  | _ => typ
  }
};

module Struct = {
  type field = (Fieldname.t, T.t, Annot.Item.t) [@@deriving compare];
  type fields = list field;

  /** Type for a structured value. */
  type t = {
    fields, /** non-static fields */
    statics: fields, /** static fields */
    supers: list Name.t, /** superclasses */
    methods: list Procname.t, /** methods defined */
    annots: Annot.Item.t /** annotations */
  };
  type lookup = Name.t => option t;
  let pp pe name f {fields, supers, methods, annots} =>
    if Config.debug_mode {
      /* change false to true to print the details of struct */
      F.fprintf
        f
        "%a \n\tfields: {%a\n\t}\n\tsupers: {%a\n\t}\n\tmethods: {%a\n\t}\n\tannots: {%a\n\t}"
        Name.pp
        name
        (
          Pp.seq (
            fun f (fld, t, a) =>
              F.fprintf f "\n\t\t%a %a %a" (pp_full pe) t Fieldname.pp fld Annot.Item.pp a
          )
        )
        fields
        (Pp.seq (fun f n => F.fprintf f "\n\t\t%a" Name.pp n))
        supers
        (Pp.seq (fun f m => F.fprintf f "\n\t\t%a" Procname.pp m))
        methods
        Annot.Item.pp
        annots
    } else {
      F.fprintf f "%a" Name.pp name
    };
  let internal_mk_struct ::default=? ::fields=? ::statics=? ::methods=? ::supers=? ::annots=? () => {
    let default_ = {fields: [], statics: [], methods: [], supers: [], annots: Annot.Item.empty};
    let mk_struct_
        ::default=default_
        ::fields=default.fields
        ::statics=default.statics
        ::methods=default.methods
        ::supers=default.supers
        ::annots=default.annots
        () => {
      fields,
      statics,
      methods,
      supers,
      annots
    };
    mk_struct_ ::?default ::?fields ::?statics ::?methods ::?supers ::?annots ()
  };

  /** the element typ of the final extensible array in the given typ, if any */
  let rec get_extensible_array_element_typ ::lookup (typ: T.t) =>
    switch typ.desc {
    | Tarray typ _ _ => Some typ
    | Tstruct name =>
      switch (lookup name) {
      | Some {fields} =>
        switch (List.last fields) {
        | Some (_, fld_typ, _) => get_extensible_array_element_typ ::lookup fld_typ
        | None => None
        }
      | None => None
      }
    | _ => None
    };

  /** If a struct type with field f, return the type of f. If not, return the default */
  let fld_typ ::lookup ::default fn (typ: T.t) =>
    switch typ.desc {
    | Tstruct name =>
      switch (lookup name) {
      | Some {fields} =>
        List.find f::(fun (f, _, _) => Fieldname.equal f fn) fields |>
        Option.value_map f::snd3 ::default
      | None => default
      }
    | _ => default
    };
  let get_field_type_and_annotation ::lookup fn (typ: T.t) =>
    switch typ.desc {
    | Tstruct name
    | Tptr {desc: Tstruct name} _ =>
      switch (lookup name) {
      | Some {fields, statics} =>
        List.find_map
          f::(fun (f, t, a) => Fieldname.equal f fn ? Some (t, a) : None) (fields @ statics)
      | None => None
      }
    | _ => None
    };
  let objc_ref_counter_annot = [({Annot.class_name: "ref_counter", parameters: []}, false)];

  /** Field used for objective-c reference counting */
  let objc_ref_counter_field = (Fieldname.hidden, mk (T.Tint IInt), objc_ref_counter_annot);
  let is_objc_ref_counter_field (fld, _, a) =>
    Fieldname.is_hidden fld && Annot.Item.equal a objc_ref_counter_annot;
};
