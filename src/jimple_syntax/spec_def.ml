(********************************************************
   This file is part of jStar 
	src/jimple_syntax/spec_def.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)

(** data types for specifications *)

open Jparsetree
open Vars
open Psyntax
open Spec


type methodspec =
      Dynamic of method_signature_short * (spec list)
  |   Static of method_signature_short * (spec list)

type methodspecs =
    methodspec list

type apf_define = (string * var * fldlist * Psyntax.pform * bool)

type apf_defines = apf_define list

type named_implication = (string * Psyntax.pform * Psyntax.pform)

type exportLocal_predicate = (string * var list * Psyntax.pform)

type exports_clause = (named_implication list * exportLocal_predicate list) option

type axioms_clause = named_implication list option

type class_spec = {
	class_or_interface: j_file_type;
	classname: class_name;
	extends: extends_clause;
	implements: implements_clause;
	apf: apf_defines;
	exports: exports_clause;
	axioms: axioms_clause;
	methodspecs: methodspecs }

(* The pretty printing functions below aid debugging. *)

let pp_methodspec f m =
  let (t, s, sp) = match m with
    | Dynamic (s, sp) -> ("dynamic", s, sp)
    | Static (s, sp) -> ("static", s, sp) in
  Format.fprintf f "@\n@[<2>";
  pp_method_signature_short f s;
  List.iter (fun x -> Format.fprintf f "@\n%s " t; spec2str f x) sp;
  Format.fprintf f "@]"

let pp_class_spec f {
    class_or_interface = ci;
    classname = cn;
    extends = e;
    implements = i;
    apf = apf;
    exports = ex;
    axioms = ax;
    methodspecs = m } =
  Format.fprintf f "@[<2>@[<4>";
  (match ci with
  | ClassFile -> Format.fprintf f "class";
  | InterfaceFile -> Format.fprintf f "interface");
  pp_class_name f cn;
  pp_inheritance_clause " extends" f e;
  pp_inheritance_clause " implements" f i;
  Format.fprintf f "@] {";
  (* TODO(rgrig): Prettyprint apf, exports, and axioms. *)
  List.iter (pp_methodspec f) m;
  Format.fprintf f "@]@;}@."

