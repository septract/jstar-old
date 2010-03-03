open Jparsetree
open Vars
(*open Rterm *)
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
