import Mettapedia.GSLT.LanguageDef.IndexedConstructorSignature
import Mettapedia.GSLT.LanguageDef.CarrierWellSorted
import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
import Mettapedia.GSLT.LanguageDef.CanonicalWire

/-!
# Generated typed abstract syntax for TPTP v9.2.0.0

This inert carrier is generated from the regular productions of the official
TPTP `SyntaxBNF`.  It preserves production alternatives, token categories and
lexemes, and typed repetitions.  It is not yet the semantic refinement layer:
the `:==` rows remain explicit later validators rather than parser rules.

Immediate left recursion is represented directly in the abstract syntax even
though the ParserPack regularizes it.  The parenthesized CNF-literal constructor
is the explicitly identified corpus-conformance extension.
-/

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialAbstractSyntax

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.GSLT.LanguageDef.CarrierWellSorted
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor

private def a (name : String) (args : List Pattern := []) : Pattern :=
  .apply name args

def sourceDigest : String := "f47940c43c23ed5ed8633a3b74a2847648d5ab794669430c8f0c38f138e61df6"

private def typesChunk0 : List TypeDecl := [
    { name := "Integer", carrier := .builtinInt },
    { name := "String", carrier := .builtinString },
    "Tptp92Ast:annotated-formula",
    "Tptp92Ast:annotations",
    "Tptp92Ast:assignment",
    "Tptp92Ast:assoc-connective",
    "Tptp92Ast:atom",
    "Tptp92Ast:atomic-defined-word",
    "Tptp92Ast:atomic-system-word",
    "Tptp92Ast:atomic-word",
    "Tptp92Ast:cnf-annotated",
    "Tptp92Ast:cnf-disjunction",
    "Tptp92Ast:cnf-formula",
    "Tptp92Ast:cnf-literal",
    "Tptp92Ast:comma-fof-logic-formula",
    "Tptp92Ast:comma-general-term"
  ]

private def typesPrefix0 : List TypeDecl := typesChunk0

private def typesChunk1 : List TypeDecl := [
    "Tptp92Ast:comma-parent-info",
    "Tptp92Ast:comma-tff-term",
    "Tptp92Ast:comma-thf-logic-formula",
    "Tptp92Ast:constant",
    "Tptp92Ast:creator-name",
    "Tptp92Ast:creator-source",
    "Tptp92Ast:dag-source",
    "Tptp92Ast:def-or-sys-constant",
    "Tptp92Ast:defined-constant",
    "Tptp92Ast:defined-functor",
    "Tptp92Ast:defined-infix-pred",
    "Tptp92Ast:defined-term",
    "Tptp92Ast:defined-type",
    "Tptp92Ast:external-source",
    "Tptp92Ast:file-info",
    "Tptp92Ast:file-name"
  ]

private def typesPrefix1 : List TypeDecl := typesPrefix0 ++ typesChunk1

private def typesChunk2 : List TypeDecl := [
    "Tptp92Ast:file-source",
    "Tptp92Ast:fof-and-formula",
    "Tptp92Ast:fof-annotated",
    "Tptp92Ast:fof-arguments",
    "Tptp92Ast:fof-atomic-formula",
    "Tptp92Ast:fof-binary-assoc",
    "Tptp92Ast:fof-binary-formula",
    "Tptp92Ast:fof-binary-nonassoc",
    "Tptp92Ast:fof-defined-atomic-formula",
    "Tptp92Ast:fof-defined-atomic-term",
    "Tptp92Ast:fof-defined-infix-formula",
    "Tptp92Ast:fof-defined-plain-formula",
    "Tptp92Ast:fof-defined-plain-term",
    "Tptp92Ast:fof-defined-term",
    "Tptp92Ast:fof-formula",
    "Tptp92Ast:fof-formula-tuple"
  ]

private def typesPrefix2 : List TypeDecl := typesPrefix1 ++ typesChunk2

private def typesChunk3 : List TypeDecl := [
    "Tptp92Ast:fof-formula-tuple-list",
    "Tptp92Ast:fof-function-term",
    "Tptp92Ast:fof-infix-unary",
    "Tptp92Ast:fof-logic-formula",
    "Tptp92Ast:fof-or-formula",
    "Tptp92Ast:fof-plain-atomic-formula",
    "Tptp92Ast:fof-plain-term",
    "Tptp92Ast:fof-quantified-formula",
    "Tptp92Ast:fof-quantifier",
    "Tptp92Ast:fof-sequent",
    "Tptp92Ast:fof-system-atomic-formula",
    "Tptp92Ast:fof-system-term",
    "Tptp92Ast:fof-term",
    "Tptp92Ast:fof-unary-formula",
    "Tptp92Ast:fof-unit-formula",
    "Tptp92Ast:fof-unitary-formula"
  ]

private def typesPrefix3 : List TypeDecl := typesPrefix2 ++ typesChunk3

private def typesChunk4 : List TypeDecl := [
    "Tptp92Ast:fof-variable-list",
    "Tptp92Ast:formula-data",
    "Tptp92Ast:formula-role",
    "Tptp92Ast:formula-selection",
    "Tptp92Ast:functor",
    "Tptp92Ast:general-data",
    "Tptp92Ast:general-function",
    "Tptp92Ast:general-list",
    "Tptp92Ast:general-term",
    "Tptp92Ast:general-terms",
    "Tptp92Ast:gentzen-arrow",
    "Tptp92Ast:identical",
    "Tptp92Ast:include",
    "Tptp92Ast:include-optionals",
    "Tptp92Ast:inference-record",
    "Tptp92Ast:inference-rule"
  ]

private def typesPrefix4 : List TypeDecl := typesPrefix3 ++ typesChunk4

private def typesChunk5 : List TypeDecl := [
    "Tptp92Ast:infix-equality",
    "Tptp92Ast:infix-inequality",
    "Tptp92Ast:internal-source",
    "Tptp92Ast:intro-type",
    "Tptp92Ast:name",
    "Tptp92Ast:name-list",
    "Tptp92Ast:nhf-key-pair",
    "Tptp92Ast:nhf-long-connective",
    "Tptp92Ast:nhf-parameter",
    "Tptp92Ast:nhf-parameter-list",
    "Tptp92Ast:nonassoc-connective",
    "Tptp92Ast:nothing",
    "Tptp92Ast:ntf-connective-name",
    "Tptp92Ast:ntf-index",
    "Tptp92Ast:ntf-short-connective",
    "Tptp92Ast:number"
  ]

private def typesPrefix5 : List TypeDecl := typesPrefix4 ++ typesChunk5

private def typesChunk6 : List TypeDecl := [
    "Tptp92Ast:nxf-atom",
    "Tptp92Ast:nxf-key-pair",
    "Tptp92Ast:nxf-long-connective",
    "Tptp92Ast:nxf-parameter",
    "Tptp92Ast:nxf-parameter-list",
    "Tptp92Ast:optional-info",
    "Tptp92Ast:parent-details",
    "Tptp92Ast:parent-info",
    "Tptp92Ast:parent-list",
    "Tptp92Ast:parents",
    "Tptp92Ast:source",
    "Tptp92Ast:source-span",
    "Tptp92Ast:sources",
    "Tptp92Ast:space-name",
    "Tptp92Ast:subtype-sign",
    "Tptp92Ast:system-constant"
  ]

private def typesPrefix6 : List TypeDecl := typesPrefix5 ++ typesChunk6

private def typesChunk7 : List TypeDecl := [
    "Tptp92Ast:system-functor",
    "Tptp92Ast:tcf-annotated",
    "Tptp92Ast:tcf-formula",
    "Tptp92Ast:tcf-logic-formula",
    "Tptp92Ast:tcf-quantified-formula",
    "Tptp92Ast:tf1-quantified-type",
    "Tptp92Ast:tff-and-formula",
    "Tptp92Ast:tff-annotated",
    "Tptp92Ast:tff-arguments",
    "Tptp92Ast:tff-atom-typing",
    "Tptp92Ast:tff-atom-typing-list",
    "Tptp92Ast:tff-atomic-formula",
    "Tptp92Ast:tff-atomic-type",
    "Tptp92Ast:tff-binary-assoc",
    "Tptp92Ast:tff-binary-formula",
    "Tptp92Ast:tff-binary-nonassoc"
  ]

private def typesPrefix7 : List TypeDecl := typesPrefix6 ++ typesChunk7

private def typesChunk8 : List TypeDecl := [
    "Tptp92Ast:tff-defined-atomic",
    "Tptp92Ast:tff-defined-infix",
    "Tptp92Ast:tff-defined-plain",
    "Tptp92Ast:tff-formula",
    "Tptp92Ast:tff-infix-unary",
    "Tptp92Ast:tff-logic-formula",
    "Tptp92Ast:tff-mapping-type",
    "Tptp92Ast:tff-monotype",
    "Tptp92Ast:tff-non-atomic-type",
    "Tptp92Ast:tff-or-formula",
    "Tptp92Ast:tff-plain-atomic",
    "Tptp92Ast:tff-prefix-unary",
    "Tptp92Ast:tff-preunit-formula",
    "Tptp92Ast:tff-quantified-formula",
    "Tptp92Ast:tff-quantifier",
    "Tptp92Ast:tff-subtype"
  ]

private def typesPrefix8 : List TypeDecl := typesPrefix7 ++ typesChunk8

private def typesChunk9 : List TypeDecl := [
    "Tptp92Ast:tff-system-atomic",
    "Tptp92Ast:tff-term",
    "Tptp92Ast:tff-top-level-type",
    "Tptp92Ast:tff-type-arguments",
    "Tptp92Ast:tff-type-list",
    "Tptp92Ast:tff-typed-variable",
    "Tptp92Ast:tff-unary-connective",
    "Tptp92Ast:tff-unary-formula",
    "Tptp92Ast:tff-unit-formula",
    "Tptp92Ast:tff-unitary-formula",
    "Tptp92Ast:tff-unitary-term",
    "Tptp92Ast:tff-unitary-type",
    "Tptp92Ast:tff-variable",
    "Tptp92Ast:tff-variable-list",
    "Tptp92Ast:tff-xprod-type",
    "Tptp92Ast:th0-quantifier"
  ]

private def typesPrefix9 : List TypeDecl := typesPrefix8 ++ typesChunk9

private def typesChunk10 : List TypeDecl := [
    "Tptp92Ast:th1-defined-term",
    "Tptp92Ast:theory",
    "Tptp92Ast:theory-name",
    "Tptp92Ast:thf-and-formula",
    "Tptp92Ast:thf-annotated",
    "Tptp92Ast:thf-apply-formula",
    "Tptp92Ast:thf-apply-type",
    "Tptp92Ast:thf-arguments",
    "Tptp92Ast:thf-atom-typing",
    "Tptp92Ast:thf-atom-typing-list",
    "Tptp92Ast:thf-atomic-formula",
    "Tptp92Ast:thf-binary-assoc",
    "Tptp92Ast:thf-binary-formula",
    "Tptp92Ast:thf-binary-nonassoc",
    "Tptp92Ast:thf-binary-type",
    "Tptp92Ast:thf-conn-term"
  ]

private def typesPrefix10 : List TypeDecl := typesPrefix9 ++ typesChunk10

private def typesChunk11 : List TypeDecl := [
    "Tptp92Ast:thf-defined-atomic",
    "Tptp92Ast:thf-defined-infix",
    "Tptp92Ast:thf-defined-term",
    "Tptp92Ast:thf-definition",
    "Tptp92Ast:thf-fof-function",
    "Tptp92Ast:thf-formula",
    "Tptp92Ast:thf-formula-list",
    "Tptp92Ast:thf-infix-unary",
    "Tptp92Ast:thf-let",
    "Tptp92Ast:thf-let-defn",
    "Tptp92Ast:thf-let-defn-list",
    "Tptp92Ast:thf-let-defns",
    "Tptp92Ast:thf-let-types",
    "Tptp92Ast:thf-logic-formula",
    "Tptp92Ast:thf-mapping-type",
    "Tptp92Ast:thf-or-formula"
  ]

private def typesPrefix11 : List TypeDecl := typesPrefix10 ++ typesChunk11

private def typesChunk12 : List TypeDecl := [
    "Tptp92Ast:thf-plain-atomic",
    "Tptp92Ast:thf-prefix-unary",
    "Tptp92Ast:thf-preunit-formula",
    "Tptp92Ast:thf-quantification",
    "Tptp92Ast:thf-quantified-formula",
    "Tptp92Ast:thf-quantifier",
    "Tptp92Ast:thf-sequent",
    "Tptp92Ast:thf-subtype",
    "Tptp92Ast:thf-system-atomic",
    "Tptp92Ast:thf-top-level-type",
    "Tptp92Ast:thf-tuple",
    "Tptp92Ast:thf-typed-variable",
    "Tptp92Ast:thf-unary-connective",
    "Tptp92Ast:thf-unary-formula",
    "Tptp92Ast:thf-union-type",
    "Tptp92Ast:thf-unit-formula"
  ]

private def typesPrefix12 : List TypeDecl := typesPrefix11 ++ typesChunk12

private def typesChunk13 : List TypeDecl := [
    "Tptp92Ast:thf-unitary-formula",
    "Tptp92Ast:thf-unitary-term",
    "Tptp92Ast:thf-unitary-type",
    "Tptp92Ast:thf-variable-list",
    "Tptp92Ast:thf-xprod-type",
    "Tptp92Ast:tpi-annotated",
    "Tptp92Ast:tpi-formula",
    "Tptp92Ast:tptp-file",
    "Tptp92Ast:tptp-input",
    "Tptp92Ast:txf-definition",
    "Tptp92Ast:txf-let",
    "Tptp92Ast:txf-let-defn",
    "Tptp92Ast:txf-let-defn-list",
    "Tptp92Ast:txf-let-defns",
    "Tptp92Ast:txf-let-lhs",
    "Tptp92Ast:txf-let-types"
  ]

private def typesPrefix13 : List TypeDecl := typesPrefix12 ++ typesChunk13

private def typesChunk14 : List TypeDecl := [
    "Tptp92Ast:txf-sequent",
    "Tptp92Ast:txf-tuple",
    "Tptp92Ast:txf-tuple-type",
    "Tptp92Ast:txf-unitary-formula",
    "Tptp92Ast:type-constant",
    "Tptp92Ast:type-functor",
    "Tptp92Ast:type-quantifier",
    "Tptp92Ast:unary-connective",
    "Tptp92Ast:untyped-atom",
    "Tptp92Ast:useful-info",
    "Tptp92Ast:variable",
    "Tptp92AstList:tptp92ast-comma-fof-logic-formula",
    "Tptp92AstList:tptp92ast-comma-general-term",
    "Tptp92AstList:tptp92ast-comma-parent-info",
    "Tptp92AstList:tptp92ast-comma-tff-term",
    "Tptp92AstList:tptp92ast-comma-thf-logic-formula"
  ]

private def typesPrefix14 : List TypeDecl := typesPrefix13 ++ typesChunk14

private def typesChunk15 : List TypeDecl := [
    "Tptp92AstList:tptp92ast-tptp-input",
    "Tptp92AstToken:back-quoted",
    "Tptp92AstToken:distinct-object",
    "Tptp92AstToken:dollar-dollar-word",
    "Tptp92AstToken:dollar-word",
    "Tptp92AstToken:integer",
    "Tptp92AstToken:lower-word",
    "Tptp92AstToken:rational",
    "Tptp92AstToken:real",
    "Tptp92AstToken:single-quoted",
    "Tptp92AstToken:upper-word"
  ]

private def typesPrefix15 : List TypeDecl := typesPrefix14 ++ typesChunk15

def types : List TypeDecl := typesPrefix15

set_option maxRecDepth 10000

private def sort_Integer : Fin types.length := ⟨0, by decide⟩
private def sort_String : Fin types.length := ⟨1, by decide⟩
private def sort_Tptp92Ast_annotated_formula : Fin types.length := ⟨2, by decide⟩
private def sort_Tptp92Ast_annotations : Fin types.length := ⟨3, by decide⟩
private def sort_Tptp92Ast_assignment : Fin types.length := ⟨4, by decide⟩
private def sort_Tptp92Ast_assoc_connective : Fin types.length := ⟨5, by decide⟩
private def sort_Tptp92Ast_atom : Fin types.length := ⟨6, by decide⟩
private def sort_Tptp92Ast_atomic_defined_word : Fin types.length := ⟨7, by decide⟩
private def sort_Tptp92Ast_atomic_system_word : Fin types.length := ⟨8, by decide⟩
private def sort_Tptp92Ast_atomic_word : Fin types.length := ⟨9, by decide⟩
private def sort_Tptp92Ast_cnf_annotated : Fin types.length := ⟨10, by decide⟩
private def sort_Tptp92Ast_cnf_disjunction : Fin types.length := ⟨11, by decide⟩
private def sort_Tptp92Ast_cnf_formula : Fin types.length := ⟨12, by decide⟩
private def sort_Tptp92Ast_cnf_literal : Fin types.length := ⟨13, by decide⟩
private def sort_Tptp92Ast_comma_fof_logic_formula : Fin types.length := ⟨14, by decide⟩
private def sort_Tptp92Ast_comma_general_term : Fin types.length := ⟨15, by decide⟩
private def sort_Tptp92Ast_comma_parent_info : Fin types.length := ⟨16, by decide⟩
private def sort_Tptp92Ast_comma_tff_term : Fin types.length := ⟨17, by decide⟩
private def sort_Tptp92Ast_comma_thf_logic_formula : Fin types.length := ⟨18, by decide⟩
private def sort_Tptp92Ast_constant : Fin types.length := ⟨19, by decide⟩
private def sort_Tptp92Ast_creator_name : Fin types.length := ⟨20, by decide⟩
private def sort_Tptp92Ast_creator_source : Fin types.length := ⟨21, by decide⟩
private def sort_Tptp92Ast_dag_source : Fin types.length := ⟨22, by decide⟩
private def sort_Tptp92Ast_def_or_sys_constant : Fin types.length := ⟨23, by decide⟩
private def sort_Tptp92Ast_defined_constant : Fin types.length := ⟨24, by decide⟩
private def sort_Tptp92Ast_defined_functor : Fin types.length := ⟨25, by decide⟩
private def sort_Tptp92Ast_defined_infix_pred : Fin types.length := ⟨26, by decide⟩
private def sort_Tptp92Ast_defined_term : Fin types.length := ⟨27, by decide⟩
private def sort_Tptp92Ast_defined_type : Fin types.length := ⟨28, by decide⟩
private def sort_Tptp92Ast_external_source : Fin types.length := ⟨29, by decide⟩
private def sort_Tptp92Ast_file_info : Fin types.length := ⟨30, by decide⟩
private def sort_Tptp92Ast_file_name : Fin types.length := ⟨31, by decide⟩
private def sort_Tptp92Ast_file_source : Fin types.length := ⟨32, by decide⟩
private def sort_Tptp92Ast_fof_and_formula : Fin types.length := ⟨33, by decide⟩
private def sort_Tptp92Ast_fof_annotated : Fin types.length := ⟨34, by decide⟩
private def sort_Tptp92Ast_fof_arguments : Fin types.length := ⟨35, by decide⟩
private def sort_Tptp92Ast_fof_atomic_formula : Fin types.length := ⟨36, by decide⟩
private def sort_Tptp92Ast_fof_binary_assoc : Fin types.length := ⟨37, by decide⟩
private def sort_Tptp92Ast_fof_binary_formula : Fin types.length := ⟨38, by decide⟩
private def sort_Tptp92Ast_fof_binary_nonassoc : Fin types.length := ⟨39, by decide⟩
private def sort_Tptp92Ast_fof_defined_atomic_formula : Fin types.length := ⟨40, by decide⟩
private def sort_Tptp92Ast_fof_defined_atomic_term : Fin types.length := ⟨41, by decide⟩
private def sort_Tptp92Ast_fof_defined_infix_formula : Fin types.length := ⟨42, by decide⟩
private def sort_Tptp92Ast_fof_defined_plain_formula : Fin types.length := ⟨43, by decide⟩
private def sort_Tptp92Ast_fof_defined_plain_term : Fin types.length := ⟨44, by decide⟩
private def sort_Tptp92Ast_fof_defined_term : Fin types.length := ⟨45, by decide⟩
private def sort_Tptp92Ast_fof_formula : Fin types.length := ⟨46, by decide⟩
private def sort_Tptp92Ast_fof_formula_tuple : Fin types.length := ⟨47, by decide⟩
private def sort_Tptp92Ast_fof_formula_tuple_list : Fin types.length := ⟨48, by decide⟩
private def sort_Tptp92Ast_fof_function_term : Fin types.length := ⟨49, by decide⟩
private def sort_Tptp92Ast_fof_infix_unary : Fin types.length := ⟨50, by decide⟩
private def sort_Tptp92Ast_fof_logic_formula : Fin types.length := ⟨51, by decide⟩
private def sort_Tptp92Ast_fof_or_formula : Fin types.length := ⟨52, by decide⟩
private def sort_Tptp92Ast_fof_plain_atomic_formula : Fin types.length := ⟨53, by decide⟩
private def sort_Tptp92Ast_fof_plain_term : Fin types.length := ⟨54, by decide⟩
private def sort_Tptp92Ast_fof_quantified_formula : Fin types.length := ⟨55, by decide⟩
private def sort_Tptp92Ast_fof_quantifier : Fin types.length := ⟨56, by decide⟩
private def sort_Tptp92Ast_fof_sequent : Fin types.length := ⟨57, by decide⟩
private def sort_Tptp92Ast_fof_system_atomic_formula : Fin types.length := ⟨58, by decide⟩
private def sort_Tptp92Ast_fof_system_term : Fin types.length := ⟨59, by decide⟩
private def sort_Tptp92Ast_fof_term : Fin types.length := ⟨60, by decide⟩
private def sort_Tptp92Ast_fof_unary_formula : Fin types.length := ⟨61, by decide⟩
private def sort_Tptp92Ast_fof_unit_formula : Fin types.length := ⟨62, by decide⟩
private def sort_Tptp92Ast_fof_unitary_formula : Fin types.length := ⟨63, by decide⟩
private def sort_Tptp92Ast_fof_variable_list : Fin types.length := ⟨64, by decide⟩
private def sort_Tptp92Ast_formula_data : Fin types.length := ⟨65, by decide⟩
private def sort_Tptp92Ast_formula_role : Fin types.length := ⟨66, by decide⟩
private def sort_Tptp92Ast_formula_selection : Fin types.length := ⟨67, by decide⟩
private def sort_Tptp92Ast_functor : Fin types.length := ⟨68, by decide⟩
private def sort_Tptp92Ast_general_data : Fin types.length := ⟨69, by decide⟩
private def sort_Tptp92Ast_general_function : Fin types.length := ⟨70, by decide⟩
private def sort_Tptp92Ast_general_list : Fin types.length := ⟨71, by decide⟩
private def sort_Tptp92Ast_general_term : Fin types.length := ⟨72, by decide⟩
private def sort_Tptp92Ast_general_terms : Fin types.length := ⟨73, by decide⟩
private def sort_Tptp92Ast_gentzen_arrow : Fin types.length := ⟨74, by decide⟩
private def sort_Tptp92Ast_identical : Fin types.length := ⟨75, by decide⟩
private def sort_Tptp92Ast_include : Fin types.length := ⟨76, by decide⟩
private def sort_Tptp92Ast_include_optionals : Fin types.length := ⟨77, by decide⟩
private def sort_Tptp92Ast_inference_record : Fin types.length := ⟨78, by decide⟩
private def sort_Tptp92Ast_inference_rule : Fin types.length := ⟨79, by decide⟩
private def sort_Tptp92Ast_infix_equality : Fin types.length := ⟨80, by decide⟩
private def sort_Tptp92Ast_infix_inequality : Fin types.length := ⟨81, by decide⟩
private def sort_Tptp92Ast_internal_source : Fin types.length := ⟨82, by decide⟩
private def sort_Tptp92Ast_intro_type : Fin types.length := ⟨83, by decide⟩
private def sort_Tptp92Ast_name : Fin types.length := ⟨84, by decide⟩
private def sort_Tptp92Ast_name_list : Fin types.length := ⟨85, by decide⟩
private def sort_Tptp92Ast_nhf_key_pair : Fin types.length := ⟨86, by decide⟩
private def sort_Tptp92Ast_nhf_long_connective : Fin types.length := ⟨87, by decide⟩
private def sort_Tptp92Ast_nhf_parameter : Fin types.length := ⟨88, by decide⟩
private def sort_Tptp92Ast_nhf_parameter_list : Fin types.length := ⟨89, by decide⟩
private def sort_Tptp92Ast_nonassoc_connective : Fin types.length := ⟨90, by decide⟩
private def sort_Tptp92Ast_nothing : Fin types.length := ⟨91, by decide⟩
private def sort_Tptp92Ast_ntf_connective_name : Fin types.length := ⟨92, by decide⟩
private def sort_Tptp92Ast_ntf_index : Fin types.length := ⟨93, by decide⟩
private def sort_Tptp92Ast_ntf_short_connective : Fin types.length := ⟨94, by decide⟩
private def sort_Tptp92Ast_number : Fin types.length := ⟨95, by decide⟩
private def sort_Tptp92Ast_nxf_atom : Fin types.length := ⟨96, by decide⟩
private def sort_Tptp92Ast_nxf_key_pair : Fin types.length := ⟨97, by decide⟩
private def sort_Tptp92Ast_nxf_long_connective : Fin types.length := ⟨98, by decide⟩
private def sort_Tptp92Ast_nxf_parameter : Fin types.length := ⟨99, by decide⟩
private def sort_Tptp92Ast_nxf_parameter_list : Fin types.length := ⟨100, by decide⟩
private def sort_Tptp92Ast_optional_info : Fin types.length := ⟨101, by decide⟩
private def sort_Tptp92Ast_parent_details : Fin types.length := ⟨102, by decide⟩
private def sort_Tptp92Ast_parent_info : Fin types.length := ⟨103, by decide⟩
private def sort_Tptp92Ast_parent_list : Fin types.length := ⟨104, by decide⟩
private def sort_Tptp92Ast_parents : Fin types.length := ⟨105, by decide⟩
private def sort_Tptp92Ast_source : Fin types.length := ⟨106, by decide⟩
private def sort_Tptp92Ast_source_span : Fin types.length := ⟨107, by decide⟩
private def sort_Tptp92Ast_sources : Fin types.length := ⟨108, by decide⟩
private def sort_Tptp92Ast_space_name : Fin types.length := ⟨109, by decide⟩
private def sort_Tptp92Ast_subtype_sign : Fin types.length := ⟨110, by decide⟩
private def sort_Tptp92Ast_system_constant : Fin types.length := ⟨111, by decide⟩
private def sort_Tptp92Ast_system_functor : Fin types.length := ⟨112, by decide⟩
private def sort_Tptp92Ast_tcf_annotated : Fin types.length := ⟨113, by decide⟩
private def sort_Tptp92Ast_tcf_formula : Fin types.length := ⟨114, by decide⟩
private def sort_Tptp92Ast_tcf_logic_formula : Fin types.length := ⟨115, by decide⟩
private def sort_Tptp92Ast_tcf_quantified_formula : Fin types.length := ⟨116, by decide⟩
private def sort_Tptp92Ast_tf1_quantified_type : Fin types.length := ⟨117, by decide⟩
private def sort_Tptp92Ast_tff_and_formula : Fin types.length := ⟨118, by decide⟩
private def sort_Tptp92Ast_tff_annotated : Fin types.length := ⟨119, by decide⟩
private def sort_Tptp92Ast_tff_arguments : Fin types.length := ⟨120, by decide⟩
private def sort_Tptp92Ast_tff_atom_typing : Fin types.length := ⟨121, by decide⟩
private def sort_Tptp92Ast_tff_atom_typing_list : Fin types.length := ⟨122, by decide⟩
private def sort_Tptp92Ast_tff_atomic_formula : Fin types.length := ⟨123, by decide⟩
private def sort_Tptp92Ast_tff_atomic_type : Fin types.length := ⟨124, by decide⟩
private def sort_Tptp92Ast_tff_binary_assoc : Fin types.length := ⟨125, by decide⟩
private def sort_Tptp92Ast_tff_binary_formula : Fin types.length := ⟨126, by decide⟩
private def sort_Tptp92Ast_tff_binary_nonassoc : Fin types.length := ⟨127, by decide⟩
private def sort_Tptp92Ast_tff_defined_atomic : Fin types.length := ⟨128, by decide⟩
private def sort_Tptp92Ast_tff_defined_infix : Fin types.length := ⟨129, by decide⟩
private def sort_Tptp92Ast_tff_defined_plain : Fin types.length := ⟨130, by decide⟩
private def sort_Tptp92Ast_tff_formula : Fin types.length := ⟨131, by decide⟩
private def sort_Tptp92Ast_tff_infix_unary : Fin types.length := ⟨132, by decide⟩
private def sort_Tptp92Ast_tff_logic_formula : Fin types.length := ⟨133, by decide⟩
private def sort_Tptp92Ast_tff_mapping_type : Fin types.length := ⟨134, by decide⟩
private def sort_Tptp92Ast_tff_monotype : Fin types.length := ⟨135, by decide⟩
private def sort_Tptp92Ast_tff_non_atomic_type : Fin types.length := ⟨136, by decide⟩
private def sort_Tptp92Ast_tff_or_formula : Fin types.length := ⟨137, by decide⟩
private def sort_Tptp92Ast_tff_plain_atomic : Fin types.length := ⟨138, by decide⟩
private def sort_Tptp92Ast_tff_prefix_unary : Fin types.length := ⟨139, by decide⟩
private def sort_Tptp92Ast_tff_preunit_formula : Fin types.length := ⟨140, by decide⟩
private def sort_Tptp92Ast_tff_quantified_formula : Fin types.length := ⟨141, by decide⟩
private def sort_Tptp92Ast_tff_quantifier : Fin types.length := ⟨142, by decide⟩
private def sort_Tptp92Ast_tff_subtype : Fin types.length := ⟨143, by decide⟩
private def sort_Tptp92Ast_tff_system_atomic : Fin types.length := ⟨144, by decide⟩
private def sort_Tptp92Ast_tff_term : Fin types.length := ⟨145, by decide⟩
private def sort_Tptp92Ast_tff_top_level_type : Fin types.length := ⟨146, by decide⟩
private def sort_Tptp92Ast_tff_type_arguments : Fin types.length := ⟨147, by decide⟩
private def sort_Tptp92Ast_tff_type_list : Fin types.length := ⟨148, by decide⟩
private def sort_Tptp92Ast_tff_typed_variable : Fin types.length := ⟨149, by decide⟩
private def sort_Tptp92Ast_tff_unary_connective : Fin types.length := ⟨150, by decide⟩
private def sort_Tptp92Ast_tff_unary_formula : Fin types.length := ⟨151, by decide⟩
private def sort_Tptp92Ast_tff_unit_formula : Fin types.length := ⟨152, by decide⟩
private def sort_Tptp92Ast_tff_unitary_formula : Fin types.length := ⟨153, by decide⟩
private def sort_Tptp92Ast_tff_unitary_term : Fin types.length := ⟨154, by decide⟩
private def sort_Tptp92Ast_tff_unitary_type : Fin types.length := ⟨155, by decide⟩
private def sort_Tptp92Ast_tff_variable : Fin types.length := ⟨156, by decide⟩
private def sort_Tptp92Ast_tff_variable_list : Fin types.length := ⟨157, by decide⟩
private def sort_Tptp92Ast_tff_xprod_type : Fin types.length := ⟨158, by decide⟩
private def sort_Tptp92Ast_th0_quantifier : Fin types.length := ⟨159, by decide⟩
private def sort_Tptp92Ast_th1_defined_term : Fin types.length := ⟨160, by decide⟩
private def sort_Tptp92Ast_theory : Fin types.length := ⟨161, by decide⟩
private def sort_Tptp92Ast_theory_name : Fin types.length := ⟨162, by decide⟩
private def sort_Tptp92Ast_thf_and_formula : Fin types.length := ⟨163, by decide⟩
private def sort_Tptp92Ast_thf_annotated : Fin types.length := ⟨164, by decide⟩
private def sort_Tptp92Ast_thf_apply_formula : Fin types.length := ⟨165, by decide⟩
private def sort_Tptp92Ast_thf_apply_type : Fin types.length := ⟨166, by decide⟩
private def sort_Tptp92Ast_thf_arguments : Fin types.length := ⟨167, by decide⟩
private def sort_Tptp92Ast_thf_atom_typing : Fin types.length := ⟨168, by decide⟩
private def sort_Tptp92Ast_thf_atom_typing_list : Fin types.length := ⟨169, by decide⟩
private def sort_Tptp92Ast_thf_atomic_formula : Fin types.length := ⟨170, by decide⟩
private def sort_Tptp92Ast_thf_binary_assoc : Fin types.length := ⟨171, by decide⟩
private def sort_Tptp92Ast_thf_binary_formula : Fin types.length := ⟨172, by decide⟩
private def sort_Tptp92Ast_thf_binary_nonassoc : Fin types.length := ⟨173, by decide⟩
private def sort_Tptp92Ast_thf_binary_type : Fin types.length := ⟨174, by decide⟩
private def sort_Tptp92Ast_thf_conn_term : Fin types.length := ⟨175, by decide⟩
private def sort_Tptp92Ast_thf_defined_atomic : Fin types.length := ⟨176, by decide⟩
private def sort_Tptp92Ast_thf_defined_infix : Fin types.length := ⟨177, by decide⟩
private def sort_Tptp92Ast_thf_defined_term : Fin types.length := ⟨178, by decide⟩
private def sort_Tptp92Ast_thf_definition : Fin types.length := ⟨179, by decide⟩
private def sort_Tptp92Ast_thf_fof_function : Fin types.length := ⟨180, by decide⟩
private def sort_Tptp92Ast_thf_formula : Fin types.length := ⟨181, by decide⟩
private def sort_Tptp92Ast_thf_formula_list : Fin types.length := ⟨182, by decide⟩
private def sort_Tptp92Ast_thf_infix_unary : Fin types.length := ⟨183, by decide⟩
private def sort_Tptp92Ast_thf_let : Fin types.length := ⟨184, by decide⟩
private def sort_Tptp92Ast_thf_let_defn : Fin types.length := ⟨185, by decide⟩
private def sort_Tptp92Ast_thf_let_defn_list : Fin types.length := ⟨186, by decide⟩
private def sort_Tptp92Ast_thf_let_defns : Fin types.length := ⟨187, by decide⟩
private def sort_Tptp92Ast_thf_let_types : Fin types.length := ⟨188, by decide⟩
private def sort_Tptp92Ast_thf_logic_formula : Fin types.length := ⟨189, by decide⟩
private def sort_Tptp92Ast_thf_mapping_type : Fin types.length := ⟨190, by decide⟩
private def sort_Tptp92Ast_thf_or_formula : Fin types.length := ⟨191, by decide⟩
private def sort_Tptp92Ast_thf_plain_atomic : Fin types.length := ⟨192, by decide⟩
private def sort_Tptp92Ast_thf_prefix_unary : Fin types.length := ⟨193, by decide⟩
private def sort_Tptp92Ast_thf_preunit_formula : Fin types.length := ⟨194, by decide⟩
private def sort_Tptp92Ast_thf_quantification : Fin types.length := ⟨195, by decide⟩
private def sort_Tptp92Ast_thf_quantified_formula : Fin types.length := ⟨196, by decide⟩
private def sort_Tptp92Ast_thf_quantifier : Fin types.length := ⟨197, by decide⟩
private def sort_Tptp92Ast_thf_sequent : Fin types.length := ⟨198, by decide⟩
private def sort_Tptp92Ast_thf_subtype : Fin types.length := ⟨199, by decide⟩
private def sort_Tptp92Ast_thf_system_atomic : Fin types.length := ⟨200, by decide⟩
private def sort_Tptp92Ast_thf_top_level_type : Fin types.length := ⟨201, by decide⟩
private def sort_Tptp92Ast_thf_tuple : Fin types.length := ⟨202, by decide⟩
private def sort_Tptp92Ast_thf_typed_variable : Fin types.length := ⟨203, by decide⟩
private def sort_Tptp92Ast_thf_unary_connective : Fin types.length := ⟨204, by decide⟩
private def sort_Tptp92Ast_thf_unary_formula : Fin types.length := ⟨205, by decide⟩
private def sort_Tptp92Ast_thf_union_type : Fin types.length := ⟨206, by decide⟩
private def sort_Tptp92Ast_thf_unit_formula : Fin types.length := ⟨207, by decide⟩
private def sort_Tptp92Ast_thf_unitary_formula : Fin types.length := ⟨208, by decide⟩
private def sort_Tptp92Ast_thf_unitary_term : Fin types.length := ⟨209, by decide⟩
private def sort_Tptp92Ast_thf_unitary_type : Fin types.length := ⟨210, by decide⟩
private def sort_Tptp92Ast_thf_variable_list : Fin types.length := ⟨211, by decide⟩
private def sort_Tptp92Ast_thf_xprod_type : Fin types.length := ⟨212, by decide⟩
private def sort_Tptp92Ast_tpi_annotated : Fin types.length := ⟨213, by decide⟩
private def sort_Tptp92Ast_tpi_formula : Fin types.length := ⟨214, by decide⟩
private def sort_Tptp92Ast_tptp_file : Fin types.length := ⟨215, by decide⟩
private def sort_Tptp92Ast_tptp_input : Fin types.length := ⟨216, by decide⟩
private def sort_Tptp92Ast_txf_definition : Fin types.length := ⟨217, by decide⟩
private def sort_Tptp92Ast_txf_let : Fin types.length := ⟨218, by decide⟩
private def sort_Tptp92Ast_txf_let_defn : Fin types.length := ⟨219, by decide⟩
private def sort_Tptp92Ast_txf_let_defn_list : Fin types.length := ⟨220, by decide⟩
private def sort_Tptp92Ast_txf_let_defns : Fin types.length := ⟨221, by decide⟩
private def sort_Tptp92Ast_txf_let_lhs : Fin types.length := ⟨222, by decide⟩
private def sort_Tptp92Ast_txf_let_types : Fin types.length := ⟨223, by decide⟩
private def sort_Tptp92Ast_txf_sequent : Fin types.length := ⟨224, by decide⟩
private def sort_Tptp92Ast_txf_tuple : Fin types.length := ⟨225, by decide⟩
private def sort_Tptp92Ast_txf_tuple_type : Fin types.length := ⟨226, by decide⟩
private def sort_Tptp92Ast_txf_unitary_formula : Fin types.length := ⟨227, by decide⟩
private def sort_Tptp92Ast_type_constant : Fin types.length := ⟨228, by decide⟩
private def sort_Tptp92Ast_type_functor : Fin types.length := ⟨229, by decide⟩
private def sort_Tptp92Ast_type_quantifier : Fin types.length := ⟨230, by decide⟩
private def sort_Tptp92Ast_unary_connective : Fin types.length := ⟨231, by decide⟩
private def sort_Tptp92Ast_untyped_atom : Fin types.length := ⟨232, by decide⟩
private def sort_Tptp92Ast_useful_info : Fin types.length := ⟨233, by decide⟩
private def sort_Tptp92Ast_variable : Fin types.length := ⟨234, by decide⟩
private def sort_Tptp92AstList_tptp92ast_comma_fof_logic_formula : Fin types.length := ⟨235, by decide⟩
private def sort_Tptp92AstList_tptp92ast_comma_general_term : Fin types.length := ⟨236, by decide⟩
private def sort_Tptp92AstList_tptp92ast_comma_parent_info : Fin types.length := ⟨237, by decide⟩
private def sort_Tptp92AstList_tptp92ast_comma_tff_term : Fin types.length := ⟨238, by decide⟩
private def sort_Tptp92AstList_tptp92ast_comma_thf_logic_formula : Fin types.length := ⟨239, by decide⟩
private def sort_Tptp92AstList_tptp92ast_tptp_input : Fin types.length := ⟨240, by decide⟩
private def sort_Tptp92AstToken_back_quoted : Fin types.length := ⟨241, by decide⟩
private def sort_Tptp92AstToken_distinct_object : Fin types.length := ⟨242, by decide⟩
private def sort_Tptp92AstToken_dollar_dollar_word : Fin types.length := ⟨243, by decide⟩
private def sort_Tptp92AstToken_dollar_word : Fin types.length := ⟨244, by decide⟩
private def sort_Tptp92AstToken_integer : Fin types.length := ⟨245, by decide⟩
private def sort_Tptp92AstToken_lower_word : Fin types.length := ⟨246, by decide⟩
private def sort_Tptp92AstToken_rational : Fin types.length := ⟨247, by decide⟩
private def sort_Tptp92AstToken_real : Fin types.length := ⟨248, by decide⟩
private def sort_Tptp92AstToken_single_quoted : Fin types.length := ⟨249, by decide⟩
private def sort_Tptp92AstToken_upper_word : Fin types.length := ⟨250, by decide⟩

private def parameter (name : String) (typeIndex : Fin types.length) :
    IndexedConstructorSignature.Parameter types :=
  { name, typeIndex }

private def constructor (label : String) (categoryIndex : Fin types.length)
    (params : List (IndexedConstructorSignature.Parameter types)) :
    IndexedConstructorSignature.Constructor types :=
  { label, categoryIndex, params }

private def constructorsChunk0 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:annotated-formula:alt-1" sort_Tptp92Ast_annotated_formula [parameter "thf-annotated" sort_Tptp92Ast_thf_annotated],
    constructor "tptp92-ast:annotated-formula:alt-2" sort_Tptp92Ast_annotated_formula [parameter "tff-annotated" sort_Tptp92Ast_tff_annotated],
    constructor "tptp92-ast:annotated-formula:alt-3" sort_Tptp92Ast_annotated_formula [parameter "tcf-annotated" sort_Tptp92Ast_tcf_annotated],
    constructor "tptp92-ast:annotated-formula:alt-4" sort_Tptp92Ast_annotated_formula [parameter "fof-annotated" sort_Tptp92Ast_fof_annotated],
    constructor "tptp92-ast:annotated-formula:alt-5" sort_Tptp92Ast_annotated_formula [parameter "cnf-annotated" sort_Tptp92Ast_cnf_annotated],
    constructor "tptp92-ast:annotated-formula:alt-6" sort_Tptp92Ast_annotated_formula [parameter "tpi-annotated" sort_Tptp92Ast_tpi_annotated],
    constructor "tptp92-ast:annotations:alt-1" sort_Tptp92Ast_annotations [parameter "source" sort_Tptp92Ast_source, parameter "optional-info" sort_Tptp92Ast_optional_info],
    constructor "tptp92-ast:annotations:alt-2" sort_Tptp92Ast_annotations [],
    constructor "tptp92-ast:assignment:alt-1" sort_Tptp92Ast_assignment [],
    constructor "tptp92-ast:assoc-connective:alt-1" sort_Tptp92Ast_assoc_connective [],
    constructor "tptp92-ast:assoc-connective:alt-2" sort_Tptp92Ast_assoc_connective [],
    constructor "tptp92-ast:atom:alt-1" sort_Tptp92Ast_atom [parameter "untyped-atom" sort_Tptp92Ast_untyped_atom],
    constructor "tptp92-ast:atom:alt-2" sort_Tptp92Ast_atom [parameter "defined-constant" sort_Tptp92Ast_defined_constant],
    constructor "tptp92-ast:atomic-defined-word:alt-1" sort_Tptp92Ast_atomic_defined_word [parameter "dollar-word" sort_Tptp92AstToken_dollar_word],
    constructor "tptp92-ast:atomic-system-word:alt-1" sort_Tptp92Ast_atomic_system_word [parameter "dollar-dollar-word" sort_Tptp92AstToken_dollar_dollar_word],
    constructor "tptp92-ast:atomic-word:alt-1" sort_Tptp92Ast_atomic_word [parameter "lower-word" sort_Tptp92AstToken_lower_word]
  ]

private def constructorsPrefix0 : List (IndexedConstructorSignature.Constructor types) := constructorsChunk0

private def constructorsChunk1 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:atomic-word:alt-2" sort_Tptp92Ast_atomic_word [parameter "single-quoted" sort_Tptp92AstToken_single_quoted],
    constructor "tptp92-ast:atomic-word:alt-3" sort_Tptp92Ast_atomic_word [parameter "back-quoted" sort_Tptp92AstToken_back_quoted],
    constructor "tptp92-ast:cnf-annotated:alt-1" sort_Tptp92Ast_cnf_annotated [parameter "name" sort_Tptp92Ast_name, parameter "formula-role" sort_Tptp92Ast_formula_role, parameter "cnf-formula" sort_Tptp92Ast_cnf_formula, parameter "annotations" sort_Tptp92Ast_annotations],
    constructor "tptp92-ast:cnf-disjunction:alt-1" sort_Tptp92Ast_cnf_disjunction [parameter "cnf-literal" sort_Tptp92Ast_cnf_literal],
    constructor "tptp92-ast:cnf-disjunction:alt-2" sort_Tptp92Ast_cnf_disjunction [parameter "cnf-disjunction" sort_Tptp92Ast_cnf_disjunction, parameter "cnf-literal" sort_Tptp92Ast_cnf_literal],
    constructor "tptp92-ast:cnf-formula:alt-1" sort_Tptp92Ast_cnf_formula [parameter "cnf-disjunction" sort_Tptp92Ast_cnf_disjunction],
    constructor "tptp92-ast:cnf-formula:alt-2" sort_Tptp92Ast_cnf_formula [parameter "cnf-formula" sort_Tptp92Ast_cnf_formula],
    constructor "tptp92-ast:cnf-literal:alt-1" sort_Tptp92Ast_cnf_literal [parameter "fof-atomic-formula" sort_Tptp92Ast_fof_atomic_formula],
    constructor "tptp92-ast:cnf-literal:alt-2" sort_Tptp92Ast_cnf_literal [parameter "fof-atomic-formula" sort_Tptp92Ast_fof_atomic_formula],
    constructor "tptp92-ast:cnf-literal:alt-3" sort_Tptp92Ast_cnf_literal [parameter "fof-atomic-formula" sort_Tptp92Ast_fof_atomic_formula],
    constructor "tptp92-ast:cnf-literal:alt-4" sort_Tptp92Ast_cnf_literal [parameter "fof-infix-unary" sort_Tptp92Ast_fof_infix_unary],
    constructor "tptp92-ast:cnf-literal:corpus-parenthesized" sort_Tptp92Ast_cnf_literal [parameter "body" sort_Tptp92Ast_cnf_literal],
    constructor "tptp92-ast:comma-fof-logic-formula:alt-1" sort_Tptp92Ast_comma_fof_logic_formula [parameter "fof-logic-formula" sort_Tptp92Ast_fof_logic_formula],
    constructor "tptp92-ast:comma-general-term:alt-1" sort_Tptp92Ast_comma_general_term [parameter "general-term" sort_Tptp92Ast_general_term],
    constructor "tptp92-ast:comma-parent-info:alt-1" sort_Tptp92Ast_comma_parent_info [parameter "parent-info" sort_Tptp92Ast_parent_info],
    constructor "tptp92-ast:comma-tff-term:alt-1" sort_Tptp92Ast_comma_tff_term [parameter "tff-term" sort_Tptp92Ast_tff_term]
  ]

private def constructorsPrefix1 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix0 ++ constructorsChunk1

private def constructorsChunk2 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:comma-thf-logic-formula:alt-1" sort_Tptp92Ast_comma_thf_logic_formula [parameter "thf-logic-formula" sort_Tptp92Ast_thf_logic_formula],
    constructor "tptp92-ast:constant:alt-1" sort_Tptp92Ast_constant [parameter "functor" sort_Tptp92Ast_functor],
    constructor "tptp92-ast:creator-name:alt-1" sort_Tptp92Ast_creator_name [parameter "atomic-word" sort_Tptp92Ast_atomic_word],
    constructor "tptp92-ast:creator-source:alt-1" sort_Tptp92Ast_creator_source [parameter "creator-name" sort_Tptp92Ast_creator_name, parameter "useful-info" sort_Tptp92Ast_useful_info, parameter "parents" sort_Tptp92Ast_parents],
    constructor "tptp92-ast:dag-source:alt-1" sort_Tptp92Ast_dag_source [parameter "name" sort_Tptp92Ast_name],
    constructor "tptp92-ast:dag-source:alt-2" sort_Tptp92Ast_dag_source [parameter "inference-record" sort_Tptp92Ast_inference_record],
    constructor "tptp92-ast:def-or-sys-constant:alt-1" sort_Tptp92Ast_def_or_sys_constant [parameter "defined-constant" sort_Tptp92Ast_defined_constant],
    constructor "tptp92-ast:def-or-sys-constant:alt-2" sort_Tptp92Ast_def_or_sys_constant [parameter "system-constant" sort_Tptp92Ast_system_constant],
    constructor "tptp92-ast:defined-constant:alt-1" sort_Tptp92Ast_defined_constant [parameter "defined-functor" sort_Tptp92Ast_defined_functor],
    constructor "tptp92-ast:defined-functor:alt-1" sort_Tptp92Ast_defined_functor [parameter "atomic-defined-word" sort_Tptp92Ast_atomic_defined_word],
    constructor "tptp92-ast:defined-infix-pred:alt-1" sort_Tptp92Ast_defined_infix_pred [parameter "infix-equality" sort_Tptp92Ast_infix_equality],
    constructor "tptp92-ast:defined-term:alt-1" sort_Tptp92Ast_defined_term [parameter "number" sort_Tptp92Ast_number],
    constructor "tptp92-ast:defined-term:alt-2" sort_Tptp92Ast_defined_term [parameter "distinct-object" sort_Tptp92AstToken_distinct_object],
    constructor "tptp92-ast:defined-type:alt-1" sort_Tptp92Ast_defined_type [parameter "atomic-defined-word" sort_Tptp92Ast_atomic_defined_word],
    constructor "tptp92-ast:external-source:alt-1" sort_Tptp92Ast_external_source [parameter "file-source" sort_Tptp92Ast_file_source],
    constructor "tptp92-ast:external-source:alt-2" sort_Tptp92Ast_external_source [parameter "theory" sort_Tptp92Ast_theory]
  ]

private def constructorsPrefix2 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix1 ++ constructorsChunk2

private def constructorsChunk3 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:external-source:alt-3" sort_Tptp92Ast_external_source [parameter "creator-source" sort_Tptp92Ast_creator_source],
    constructor "tptp92-ast:file-info:alt-1" sort_Tptp92Ast_file_info [parameter "name" sort_Tptp92Ast_name],
    constructor "tptp92-ast:file-info:alt-2" sort_Tptp92Ast_file_info [],
    constructor "tptp92-ast:file-name:alt-1" sort_Tptp92Ast_file_name [parameter "atomic-word" sort_Tptp92Ast_atomic_word],
    constructor "tptp92-ast:file-source:alt-1" sort_Tptp92Ast_file_source [parameter "file-name" sort_Tptp92Ast_file_name, parameter "file-info" sort_Tptp92Ast_file_info],
    constructor "tptp92-ast:fof-and-formula:alt-1" sort_Tptp92Ast_fof_and_formula [parameter "fof-unit-formula-1" sort_Tptp92Ast_fof_unit_formula, parameter "fof-unit-formula-2" sort_Tptp92Ast_fof_unit_formula],
    constructor "tptp92-ast:fof-and-formula:alt-2" sort_Tptp92Ast_fof_and_formula [parameter "fof-and-formula" sort_Tptp92Ast_fof_and_formula, parameter "fof-unit-formula" sort_Tptp92Ast_fof_unit_formula],
    constructor "tptp92-ast:fof-annotated:alt-1" sort_Tptp92Ast_fof_annotated [parameter "name" sort_Tptp92Ast_name, parameter "formula-role" sort_Tptp92Ast_formula_role, parameter "fof-formula" sort_Tptp92Ast_fof_formula, parameter "annotations" sort_Tptp92Ast_annotations],
    constructor "tptp92-ast:fof-arguments:alt-1" sort_Tptp92Ast_fof_arguments [parameter "fof-term" sort_Tptp92Ast_fof_term],
    constructor "tptp92-ast:fof-arguments:alt-2" sort_Tptp92Ast_fof_arguments [parameter "fof-term" sort_Tptp92Ast_fof_term, parameter "fof-arguments" sort_Tptp92Ast_fof_arguments],
    constructor "tptp92-ast:fof-atomic-formula:alt-1" sort_Tptp92Ast_fof_atomic_formula [parameter "fof-plain-atomic-formula" sort_Tptp92Ast_fof_plain_atomic_formula],
    constructor "tptp92-ast:fof-atomic-formula:alt-2" sort_Tptp92Ast_fof_atomic_formula [parameter "fof-defined-atomic-formula" sort_Tptp92Ast_fof_defined_atomic_formula],
    constructor "tptp92-ast:fof-atomic-formula:alt-3" sort_Tptp92Ast_fof_atomic_formula [parameter "fof-system-atomic-formula" sort_Tptp92Ast_fof_system_atomic_formula],
    constructor "tptp92-ast:fof-binary-assoc:alt-1" sort_Tptp92Ast_fof_binary_assoc [parameter "fof-or-formula" sort_Tptp92Ast_fof_or_formula],
    constructor "tptp92-ast:fof-binary-assoc:alt-2" sort_Tptp92Ast_fof_binary_assoc [parameter "fof-and-formula" sort_Tptp92Ast_fof_and_formula],
    constructor "tptp92-ast:fof-binary-formula:alt-1" sort_Tptp92Ast_fof_binary_formula [parameter "fof-binary-nonassoc" sort_Tptp92Ast_fof_binary_nonassoc]
  ]

private def constructorsPrefix3 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix2 ++ constructorsChunk3

private def constructorsChunk4 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:fof-binary-formula:alt-2" sort_Tptp92Ast_fof_binary_formula [parameter "fof-binary-assoc" sort_Tptp92Ast_fof_binary_assoc],
    constructor "tptp92-ast:fof-binary-nonassoc:alt-1" sort_Tptp92Ast_fof_binary_nonassoc [parameter "fof-unit-formula-1" sort_Tptp92Ast_fof_unit_formula, parameter "nonassoc-connective" sort_Tptp92Ast_nonassoc_connective, parameter "fof-unit-formula-2" sort_Tptp92Ast_fof_unit_formula],
    constructor "tptp92-ast:fof-defined-atomic-formula:alt-1" sort_Tptp92Ast_fof_defined_atomic_formula [parameter "fof-defined-plain-formula" sort_Tptp92Ast_fof_defined_plain_formula],
    constructor "tptp92-ast:fof-defined-atomic-formula:alt-2" sort_Tptp92Ast_fof_defined_atomic_formula [parameter "fof-defined-infix-formula" sort_Tptp92Ast_fof_defined_infix_formula],
    constructor "tptp92-ast:fof-defined-atomic-term:alt-1" sort_Tptp92Ast_fof_defined_atomic_term [parameter "fof-defined-plain-term" sort_Tptp92Ast_fof_defined_plain_term],
    constructor "tptp92-ast:fof-defined-infix-formula:alt-1" sort_Tptp92Ast_fof_defined_infix_formula [parameter "fof-term-1" sort_Tptp92Ast_fof_term, parameter "defined-infix-pred" sort_Tptp92Ast_defined_infix_pred, parameter "fof-term-2" sort_Tptp92Ast_fof_term],
    constructor "tptp92-ast:fof-defined-plain-formula:alt-1" sort_Tptp92Ast_fof_defined_plain_formula [parameter "fof-defined-plain-term" sort_Tptp92Ast_fof_defined_plain_term],
    constructor "tptp92-ast:fof-defined-plain-term:alt-1" sort_Tptp92Ast_fof_defined_plain_term [parameter "defined-constant" sort_Tptp92Ast_defined_constant],
    constructor "tptp92-ast:fof-defined-plain-term:alt-2" sort_Tptp92Ast_fof_defined_plain_term [parameter "defined-functor" sort_Tptp92Ast_defined_functor, parameter "fof-arguments" sort_Tptp92Ast_fof_arguments],
    constructor "tptp92-ast:fof-defined-term:alt-1" sort_Tptp92Ast_fof_defined_term [parameter "defined-term" sort_Tptp92Ast_defined_term],
    constructor "tptp92-ast:fof-defined-term:alt-2" sort_Tptp92Ast_fof_defined_term [parameter "fof-defined-atomic-term" sort_Tptp92Ast_fof_defined_atomic_term],
    constructor "tptp92-ast:fof-formula-tuple-list:alt-1" sort_Tptp92Ast_fof_formula_tuple_list [parameter "fof-logic-formula" sort_Tptp92Ast_fof_logic_formula, parameter "comma-fof-logic-formula" sort_Tptp92AstList_tptp92ast_comma_fof_logic_formula],
    constructor "tptp92-ast:fof-formula-tuple:alt-1" sort_Tptp92Ast_fof_formula_tuple [],
    constructor "tptp92-ast:fof-formula-tuple:alt-2" sort_Tptp92Ast_fof_formula_tuple [parameter "fof-formula-tuple-list" sort_Tptp92Ast_fof_formula_tuple_list],
    constructor "tptp92-ast:fof-formula:alt-1" sort_Tptp92Ast_fof_formula [parameter "fof-logic-formula" sort_Tptp92Ast_fof_logic_formula],
    constructor "tptp92-ast:fof-formula:alt-2" sort_Tptp92Ast_fof_formula [parameter "fof-sequent" sort_Tptp92Ast_fof_sequent]
  ]

private def constructorsPrefix4 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix3 ++ constructorsChunk4

private def constructorsChunk5 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:fof-function-term:alt-1" sort_Tptp92Ast_fof_function_term [parameter "fof-plain-term" sort_Tptp92Ast_fof_plain_term],
    constructor "tptp92-ast:fof-function-term:alt-2" sort_Tptp92Ast_fof_function_term [parameter "fof-defined-term" sort_Tptp92Ast_fof_defined_term],
    constructor "tptp92-ast:fof-function-term:alt-3" sort_Tptp92Ast_fof_function_term [parameter "fof-system-term" sort_Tptp92Ast_fof_system_term],
    constructor "tptp92-ast:fof-infix-unary:alt-1" sort_Tptp92Ast_fof_infix_unary [parameter "fof-term-1" sort_Tptp92Ast_fof_term, parameter "infix-inequality" sort_Tptp92Ast_infix_inequality, parameter "fof-term-2" sort_Tptp92Ast_fof_term],
    constructor "tptp92-ast:fof-logic-formula:alt-1" sort_Tptp92Ast_fof_logic_formula [parameter "fof-binary-formula" sort_Tptp92Ast_fof_binary_formula],
    constructor "tptp92-ast:fof-logic-formula:alt-2" sort_Tptp92Ast_fof_logic_formula [parameter "fof-unary-formula" sort_Tptp92Ast_fof_unary_formula],
    constructor "tptp92-ast:fof-logic-formula:alt-3" sort_Tptp92Ast_fof_logic_formula [parameter "fof-unitary-formula" sort_Tptp92Ast_fof_unitary_formula],
    constructor "tptp92-ast:fof-or-formula:alt-1" sort_Tptp92Ast_fof_or_formula [parameter "fof-unit-formula-1" sort_Tptp92Ast_fof_unit_formula, parameter "fof-unit-formula-2" sort_Tptp92Ast_fof_unit_formula],
    constructor "tptp92-ast:fof-or-formula:alt-2" sort_Tptp92Ast_fof_or_formula [parameter "fof-or-formula" sort_Tptp92Ast_fof_or_formula, parameter "fof-unit-formula" sort_Tptp92Ast_fof_unit_formula],
    constructor "tptp92-ast:fof-plain-atomic-formula:alt-1" sort_Tptp92Ast_fof_plain_atomic_formula [parameter "fof-plain-term" sort_Tptp92Ast_fof_plain_term],
    constructor "tptp92-ast:fof-plain-term:alt-1" sort_Tptp92Ast_fof_plain_term [parameter "constant" sort_Tptp92Ast_constant],
    constructor "tptp92-ast:fof-plain-term:alt-2" sort_Tptp92Ast_fof_plain_term [parameter "functor" sort_Tptp92Ast_functor, parameter "fof-arguments" sort_Tptp92Ast_fof_arguments],
    constructor "tptp92-ast:fof-quantified-formula:alt-1" sort_Tptp92Ast_fof_quantified_formula [parameter "fof-quantifier" sort_Tptp92Ast_fof_quantifier, parameter "fof-variable-list" sort_Tptp92Ast_fof_variable_list, parameter "fof-unit-formula" sort_Tptp92Ast_fof_unit_formula],
    constructor "tptp92-ast:fof-quantifier:alt-1" sort_Tptp92Ast_fof_quantifier [],
    constructor "tptp92-ast:fof-quantifier:alt-2" sort_Tptp92Ast_fof_quantifier [],
    constructor "tptp92-ast:fof-sequent:alt-1" sort_Tptp92Ast_fof_sequent [parameter "fof-formula-tuple-1" sort_Tptp92Ast_fof_formula_tuple, parameter "gentzen-arrow" sort_Tptp92Ast_gentzen_arrow, parameter "fof-formula-tuple-2" sort_Tptp92Ast_fof_formula_tuple]
  ]

private def constructorsPrefix5 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix4 ++ constructorsChunk5

private def constructorsChunk6 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:fof-sequent:alt-2" sort_Tptp92Ast_fof_sequent [parameter "fof-sequent" sort_Tptp92Ast_fof_sequent],
    constructor "tptp92-ast:fof-system-atomic-formula:alt-1" sort_Tptp92Ast_fof_system_atomic_formula [parameter "fof-system-term" sort_Tptp92Ast_fof_system_term],
    constructor "tptp92-ast:fof-system-term:alt-1" sort_Tptp92Ast_fof_system_term [parameter "system-constant" sort_Tptp92Ast_system_constant],
    constructor "tptp92-ast:fof-system-term:alt-2" sort_Tptp92Ast_fof_system_term [parameter "system-functor" sort_Tptp92Ast_system_functor, parameter "fof-arguments" sort_Tptp92Ast_fof_arguments],
    constructor "tptp92-ast:fof-term:alt-1" sort_Tptp92Ast_fof_term [parameter "fof-function-term" sort_Tptp92Ast_fof_function_term],
    constructor "tptp92-ast:fof-term:alt-2" sort_Tptp92Ast_fof_term [parameter "variable" sort_Tptp92Ast_variable],
    constructor "tptp92-ast:fof-unary-formula:alt-1" sort_Tptp92Ast_fof_unary_formula [parameter "unary-connective" sort_Tptp92Ast_unary_connective, parameter "fof-unit-formula" sort_Tptp92Ast_fof_unit_formula],
    constructor "tptp92-ast:fof-unary-formula:alt-2" sort_Tptp92Ast_fof_unary_formula [parameter "fof-infix-unary" sort_Tptp92Ast_fof_infix_unary],
    constructor "tptp92-ast:fof-unit-formula:alt-1" sort_Tptp92Ast_fof_unit_formula [parameter "fof-unitary-formula" sort_Tptp92Ast_fof_unitary_formula],
    constructor "tptp92-ast:fof-unit-formula:alt-2" sort_Tptp92Ast_fof_unit_formula [parameter "fof-unary-formula" sort_Tptp92Ast_fof_unary_formula],
    constructor "tptp92-ast:fof-unitary-formula:alt-1" sort_Tptp92Ast_fof_unitary_formula [parameter "fof-quantified-formula" sort_Tptp92Ast_fof_quantified_formula],
    constructor "tptp92-ast:fof-unitary-formula:alt-2" sort_Tptp92Ast_fof_unitary_formula [parameter "fof-atomic-formula" sort_Tptp92Ast_fof_atomic_formula],
    constructor "tptp92-ast:fof-unitary-formula:alt-3" sort_Tptp92Ast_fof_unitary_formula [parameter "fof-logic-formula" sort_Tptp92Ast_fof_logic_formula],
    constructor "tptp92-ast:fof-variable-list:alt-1" sort_Tptp92Ast_fof_variable_list [parameter "variable" sort_Tptp92Ast_variable],
    constructor "tptp92-ast:fof-variable-list:alt-2" sort_Tptp92Ast_fof_variable_list [parameter "variable" sort_Tptp92Ast_variable, parameter "fof-variable-list" sort_Tptp92Ast_fof_variable_list],
    constructor "tptp92-ast:formula-data:alt-1" sort_Tptp92Ast_formula_data [parameter "thf-formula" sort_Tptp92Ast_thf_formula]
  ]

private def constructorsPrefix6 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix5 ++ constructorsChunk6

private def constructorsChunk7 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:formula-data:alt-2" sort_Tptp92Ast_formula_data [parameter "tff-formula" sort_Tptp92Ast_tff_formula],
    constructor "tptp92-ast:formula-data:alt-3" sort_Tptp92Ast_formula_data [parameter "fof-formula" sort_Tptp92Ast_fof_formula],
    constructor "tptp92-ast:formula-data:alt-4" sort_Tptp92Ast_formula_data [parameter "cnf-formula" sort_Tptp92Ast_cnf_formula],
    constructor "tptp92-ast:formula-data:alt-5" sort_Tptp92Ast_formula_data [parameter "fof-term" sort_Tptp92Ast_fof_term],
    constructor "tptp92-ast:formula-role:alt-1" sort_Tptp92Ast_formula_role [parameter "lower-word" sort_Tptp92AstToken_lower_word],
    constructor "tptp92-ast:formula-role:alt-2" sort_Tptp92Ast_formula_role [parameter "lower-word" sort_Tptp92AstToken_lower_word, parameter "general-term" sort_Tptp92Ast_general_term],
    constructor "tptp92-ast:formula-selection:alt-1" sort_Tptp92Ast_formula_selection [parameter "name-list" sort_Tptp92Ast_name_list],
    constructor "tptp92-ast:formula-selection:alt-2" sort_Tptp92Ast_formula_selection [],
    constructor "tptp92-ast:functor:alt-1" sort_Tptp92Ast_functor [parameter "atomic-word" sort_Tptp92Ast_atomic_word],
    constructor "tptp92-ast:general-data:alt-1" sort_Tptp92Ast_general_data [parameter "atomic-word" sort_Tptp92Ast_atomic_word],
    constructor "tptp92-ast:general-data:alt-2" sort_Tptp92Ast_general_data [parameter "general-function" sort_Tptp92Ast_general_function],
    constructor "tptp92-ast:general-data:alt-3" sort_Tptp92Ast_general_data [parameter "variable" sort_Tptp92Ast_variable],
    constructor "tptp92-ast:general-data:alt-4" sort_Tptp92Ast_general_data [parameter "number" sort_Tptp92Ast_number],
    constructor "tptp92-ast:general-data:alt-5" sort_Tptp92Ast_general_data [parameter "distinct-object" sort_Tptp92AstToken_distinct_object],
    constructor "tptp92-ast:general-data:alt-6" sort_Tptp92Ast_general_data [parameter "formula-data" sort_Tptp92Ast_formula_data],
    constructor "tptp92-ast:general-function:alt-1" sort_Tptp92Ast_general_function [parameter "atomic-word" sort_Tptp92Ast_atomic_word, parameter "general-terms" sort_Tptp92Ast_general_terms]
  ]

private def constructorsPrefix7 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix6 ++ constructorsChunk7

private def constructorsChunk8 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:general-list:alt-1" sort_Tptp92Ast_general_list [],
    constructor "tptp92-ast:general-list:alt-2" sort_Tptp92Ast_general_list [parameter "general-terms" sort_Tptp92Ast_general_terms],
    constructor "tptp92-ast:general-term:alt-1" sort_Tptp92Ast_general_term [parameter "general-data" sort_Tptp92Ast_general_data],
    constructor "tptp92-ast:general-term:alt-2" sort_Tptp92Ast_general_term [parameter "general-data" sort_Tptp92Ast_general_data, parameter "general-term" sort_Tptp92Ast_general_term],
    constructor "tptp92-ast:general-term:alt-3" sort_Tptp92Ast_general_term [parameter "general-list" sort_Tptp92Ast_general_list],
    constructor "tptp92-ast:general-terms:alt-1" sort_Tptp92Ast_general_terms [parameter "general-term" sort_Tptp92Ast_general_term, parameter "comma-general-term" sort_Tptp92AstList_tptp92ast_comma_general_term],
    constructor "tptp92-ast:gentzen-arrow:alt-1" sort_Tptp92Ast_gentzen_arrow [],
    constructor "tptp92-ast:identical:alt-1" sort_Tptp92Ast_identical [],
    constructor "tptp92-ast:include-optionals:alt-1" sort_Tptp92Ast_include_optionals [],
    constructor "tptp92-ast:include-optionals:alt-2" sort_Tptp92Ast_include_optionals [parameter "formula-selection" sort_Tptp92Ast_formula_selection],
    constructor "tptp92-ast:include-optionals:alt-3" sort_Tptp92Ast_include_optionals [parameter "formula-selection" sort_Tptp92Ast_formula_selection, parameter "space-name" sort_Tptp92Ast_space_name],
    constructor "tptp92-ast:include:alt-1" sort_Tptp92Ast_include [parameter "file-name" sort_Tptp92Ast_file_name, parameter "include-optionals" sort_Tptp92Ast_include_optionals],
    constructor "tptp92-ast:inference-record:alt-1" sort_Tptp92Ast_inference_record [parameter "inference-rule" sort_Tptp92Ast_inference_rule, parameter "useful-info" sort_Tptp92Ast_useful_info, parameter "parents" sort_Tptp92Ast_parents],
    constructor "tptp92-ast:inference-rule:alt-1" sort_Tptp92Ast_inference_rule [parameter "atomic-word" sort_Tptp92Ast_atomic_word],
    constructor "tptp92-ast:infix-equality:alt-1" sort_Tptp92Ast_infix_equality [],
    constructor "tptp92-ast:infix-inequality:alt-1" sort_Tptp92Ast_infix_inequality []
  ]

private def constructorsPrefix8 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix7 ++ constructorsChunk8

private def constructorsChunk9 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:internal-source:alt-1" sort_Tptp92Ast_internal_source [parameter "intro-type" sort_Tptp92Ast_intro_type, parameter "useful-info" sort_Tptp92Ast_useful_info, parameter "parents" sort_Tptp92Ast_parents],
    constructor "tptp92-ast:intro-type:alt-1" sort_Tptp92Ast_intro_type [parameter "atomic-word" sort_Tptp92Ast_atomic_word],
    constructor "tptp92-ast:list:tptp92ast-comma-fof-logic-formula:cons" sort_Tptp92AstList_tptp92ast_comma_fof_logic_formula [parameter "first" sort_Tptp92Ast_comma_fof_logic_formula, parameter "rest" sort_Tptp92AstList_tptp92ast_comma_fof_logic_formula],
    constructor "tptp92-ast:list:tptp92ast-comma-fof-logic-formula:nil" sort_Tptp92AstList_tptp92ast_comma_fof_logic_formula [],
    constructor "tptp92-ast:list:tptp92ast-comma-general-term:cons" sort_Tptp92AstList_tptp92ast_comma_general_term [parameter "first" sort_Tptp92Ast_comma_general_term, parameter "rest" sort_Tptp92AstList_tptp92ast_comma_general_term],
    constructor "tptp92-ast:list:tptp92ast-comma-general-term:nil" sort_Tptp92AstList_tptp92ast_comma_general_term [],
    constructor "tptp92-ast:list:tptp92ast-comma-parent-info:cons" sort_Tptp92AstList_tptp92ast_comma_parent_info [parameter "first" sort_Tptp92Ast_comma_parent_info, parameter "rest" sort_Tptp92AstList_tptp92ast_comma_parent_info],
    constructor "tptp92-ast:list:tptp92ast-comma-parent-info:nil" sort_Tptp92AstList_tptp92ast_comma_parent_info [],
    constructor "tptp92-ast:list:tptp92ast-comma-tff-term:cons" sort_Tptp92AstList_tptp92ast_comma_tff_term [parameter "first" sort_Tptp92Ast_comma_tff_term, parameter "rest" sort_Tptp92AstList_tptp92ast_comma_tff_term],
    constructor "tptp92-ast:list:tptp92ast-comma-tff-term:nil" sort_Tptp92AstList_tptp92ast_comma_tff_term [],
    constructor "tptp92-ast:list:tptp92ast-comma-thf-logic-formula:cons" sort_Tptp92AstList_tptp92ast_comma_thf_logic_formula [parameter "first" sort_Tptp92Ast_comma_thf_logic_formula, parameter "rest" sort_Tptp92AstList_tptp92ast_comma_thf_logic_formula],
    constructor "tptp92-ast:list:tptp92ast-comma-thf-logic-formula:nil" sort_Tptp92AstList_tptp92ast_comma_thf_logic_formula [],
    constructor "tptp92-ast:list:tptp92ast-tptp-input:cons" sort_Tptp92AstList_tptp92ast_tptp_input [parameter "first" sort_Tptp92Ast_tptp_input, parameter "rest" sort_Tptp92AstList_tptp92ast_tptp_input],
    constructor "tptp92-ast:list:tptp92ast-tptp-input:nil" sort_Tptp92AstList_tptp92ast_tptp_input [],
    constructor "tptp92-ast:name-list:alt-1" sort_Tptp92Ast_name_list [parameter "name" sort_Tptp92Ast_name],
    constructor "tptp92-ast:name-list:alt-2" sort_Tptp92Ast_name_list [parameter "name" sort_Tptp92Ast_name, parameter "name-list" sort_Tptp92Ast_name_list]
  ]

private def constructorsPrefix9 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix8 ++ constructorsChunk9

private def constructorsChunk10 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:name:alt-1" sort_Tptp92Ast_name [parameter "atomic-word" sort_Tptp92Ast_atomic_word],
    constructor "tptp92-ast:name:alt-2" sort_Tptp92Ast_name [parameter "integer" sort_Tptp92AstToken_integer],
    constructor "tptp92-ast:nhf-key-pair:alt-1" sort_Tptp92Ast_nhf_key_pair [parameter "thf-definition" sort_Tptp92Ast_thf_definition],
    constructor "tptp92-ast:nhf-long-connective:alt-1" sort_Tptp92Ast_nhf_long_connective [parameter "ntf-connective-name" sort_Tptp92Ast_ntf_connective_name],
    constructor "tptp92-ast:nhf-long-connective:alt-2" sort_Tptp92Ast_nhf_long_connective [parameter "ntf-connective-name" sort_Tptp92Ast_ntf_connective_name, parameter "nhf-parameter-list" sort_Tptp92Ast_nhf_parameter_list],
    constructor "tptp92-ast:nhf-parameter-list:alt-1" sort_Tptp92Ast_nhf_parameter_list [parameter "nhf-parameter" sort_Tptp92Ast_nhf_parameter],
    constructor "tptp92-ast:nhf-parameter-list:alt-2" sort_Tptp92Ast_nhf_parameter_list [parameter "nhf-parameter" sort_Tptp92Ast_nhf_parameter, parameter "nhf-parameter-list" sort_Tptp92Ast_nhf_parameter_list],
    constructor "tptp92-ast:nhf-parameter:alt-1" sort_Tptp92Ast_nhf_parameter [parameter "ntf-index" sort_Tptp92Ast_ntf_index],
    constructor "tptp92-ast:nhf-parameter:alt-2" sort_Tptp92Ast_nhf_parameter [parameter "nhf-key-pair" sort_Tptp92Ast_nhf_key_pair],
    constructor "tptp92-ast:nonassoc-connective:alt-1" sort_Tptp92Ast_nonassoc_connective [],
    constructor "tptp92-ast:nonassoc-connective:alt-2" sort_Tptp92Ast_nonassoc_connective [],
    constructor "tptp92-ast:nonassoc-connective:alt-3" sort_Tptp92Ast_nonassoc_connective [],
    constructor "tptp92-ast:nonassoc-connective:alt-4" sort_Tptp92Ast_nonassoc_connective [],
    constructor "tptp92-ast:nonassoc-connective:alt-5" sort_Tptp92Ast_nonassoc_connective [],
    constructor "tptp92-ast:nonassoc-connective:alt-6" sort_Tptp92Ast_nonassoc_connective [],
    constructor "tptp92-ast:nothing:alt-1" sort_Tptp92Ast_nothing []
  ]

private def constructorsPrefix10 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix9 ++ constructorsChunk10

private def constructorsChunk11 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:ntf-connective-name:alt-1" sort_Tptp92Ast_ntf_connective_name [parameter "def-or-sys-constant" sort_Tptp92Ast_def_or_sys_constant],
    constructor "tptp92-ast:ntf-index:alt-1" sort_Tptp92Ast_ntf_index [parameter "tff-unitary-term" sort_Tptp92Ast_tff_unitary_term],
    constructor "tptp92-ast:ntf-short-connective:alt-1" sort_Tptp92Ast_ntf_short_connective [],
    constructor "tptp92-ast:ntf-short-connective:alt-2" sort_Tptp92Ast_ntf_short_connective [],
    constructor "tptp92-ast:ntf-short-connective:alt-3" sort_Tptp92Ast_ntf_short_connective [],
    constructor "tptp92-ast:ntf-short-connective:alt-4" sort_Tptp92Ast_ntf_short_connective [],
    constructor "tptp92-ast:number:alt-1" sort_Tptp92Ast_number [parameter "integer" sort_Tptp92AstToken_integer],
    constructor "tptp92-ast:number:alt-2" sort_Tptp92Ast_number [parameter "rational" sort_Tptp92AstToken_rational],
    constructor "tptp92-ast:number:alt-3" sort_Tptp92Ast_number [parameter "real" sort_Tptp92AstToken_real],
    constructor "tptp92-ast:nxf-atom:alt-1" sort_Tptp92Ast_nxf_atom [parameter "nxf-long-connective" sort_Tptp92Ast_nxf_long_connective, parameter "tff-arguments" sort_Tptp92Ast_tff_arguments],
    constructor "tptp92-ast:nxf-key-pair:alt-1" sort_Tptp92Ast_nxf_key_pair [parameter "txf-definition" sort_Tptp92Ast_txf_definition],
    constructor "tptp92-ast:nxf-long-connective:alt-1" sort_Tptp92Ast_nxf_long_connective [parameter "ntf-connective-name" sort_Tptp92Ast_ntf_connective_name],
    constructor "tptp92-ast:nxf-long-connective:alt-2" sort_Tptp92Ast_nxf_long_connective [parameter "ntf-connective-name" sort_Tptp92Ast_ntf_connective_name, parameter "nxf-parameter-list" sort_Tptp92Ast_nxf_parameter_list],
    constructor "tptp92-ast:nxf-parameter-list:alt-1" sort_Tptp92Ast_nxf_parameter_list [parameter "nxf-parameter" sort_Tptp92Ast_nxf_parameter],
    constructor "tptp92-ast:nxf-parameter-list:alt-2" sort_Tptp92Ast_nxf_parameter_list [parameter "nxf-parameter" sort_Tptp92Ast_nxf_parameter, parameter "nxf-parameter-list" sort_Tptp92Ast_nxf_parameter_list],
    constructor "tptp92-ast:nxf-parameter:alt-1" sort_Tptp92Ast_nxf_parameter [parameter "ntf-index" sort_Tptp92Ast_ntf_index]
  ]

private def constructorsPrefix11 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix10 ++ constructorsChunk11

private def constructorsChunk12 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:nxf-parameter:alt-2" sort_Tptp92Ast_nxf_parameter [parameter "nxf-key-pair" sort_Tptp92Ast_nxf_key_pair],
    constructor "tptp92-ast:optional-info:alt-1" sort_Tptp92Ast_optional_info [parameter "useful-info" sort_Tptp92Ast_useful_info],
    constructor "tptp92-ast:optional-info:alt-2" sort_Tptp92Ast_optional_info [],
    constructor "tptp92-ast:parent-details:alt-1" sort_Tptp92Ast_parent_details [parameter "general-term" sort_Tptp92Ast_general_term],
    constructor "tptp92-ast:parent-details:alt-2" sort_Tptp92Ast_parent_details [],
    constructor "tptp92-ast:parent-info:alt-1" sort_Tptp92Ast_parent_info [parameter "source" sort_Tptp92Ast_source, parameter "parent-details" sort_Tptp92Ast_parent_details],
    constructor "tptp92-ast:parent-list:alt-1" sort_Tptp92Ast_parent_list [parameter "parent-info" sort_Tptp92Ast_parent_info, parameter "comma-parent-info" sort_Tptp92AstList_tptp92ast_comma_parent_info],
    constructor "tptp92-ast:parents:alt-1" sort_Tptp92Ast_parents [],
    constructor "tptp92-ast:parents:alt-2" sort_Tptp92Ast_parents [parameter "parent-list" sort_Tptp92Ast_parent_list],
    constructor "tptp92-ast:source-span" sort_Tptp92Ast_source_span [parameter "start" sort_Integer, parameter "stop" sort_Integer],
    constructor "tptp92-ast:source:alt-1" sort_Tptp92Ast_source [parameter "dag-source" sort_Tptp92Ast_dag_source],
    constructor "tptp92-ast:source:alt-2" sort_Tptp92Ast_source [parameter "internal-source" sort_Tptp92Ast_internal_source],
    constructor "tptp92-ast:source:alt-3" sort_Tptp92Ast_source [parameter "external-source" sort_Tptp92Ast_external_source],
    constructor "tptp92-ast:source:alt-4" sort_Tptp92Ast_source [],
    constructor "tptp92-ast:source:alt-5" sort_Tptp92Ast_source [parameter "sources" sort_Tptp92Ast_sources],
    constructor "tptp92-ast:sources:alt-1" sort_Tptp92Ast_sources [parameter "source" sort_Tptp92Ast_source]
  ]

private def constructorsPrefix12 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix11 ++ constructorsChunk12

private def constructorsChunk13 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:sources:alt-2" sort_Tptp92Ast_sources [parameter "source" sort_Tptp92Ast_source, parameter "sources" sort_Tptp92Ast_sources],
    constructor "tptp92-ast:space-name:alt-1" sort_Tptp92Ast_space_name [parameter "name" sort_Tptp92Ast_name],
    constructor "tptp92-ast:subtype-sign:alt-1" sort_Tptp92Ast_subtype_sign [],
    constructor "tptp92-ast:system-constant:alt-1" sort_Tptp92Ast_system_constant [parameter "system-functor" sort_Tptp92Ast_system_functor],
    constructor "tptp92-ast:system-functor:alt-1" sort_Tptp92Ast_system_functor [parameter "atomic-system-word" sort_Tptp92Ast_atomic_system_word],
    constructor "tptp92-ast:tcf-annotated:alt-1" sort_Tptp92Ast_tcf_annotated [parameter "name" sort_Tptp92Ast_name, parameter "formula-role" sort_Tptp92Ast_formula_role, parameter "tcf-formula" sort_Tptp92Ast_tcf_formula, parameter "annotations" sort_Tptp92Ast_annotations],
    constructor "tptp92-ast:tcf-formula:alt-1" sort_Tptp92Ast_tcf_formula [parameter "tcf-logic-formula" sort_Tptp92Ast_tcf_logic_formula],
    constructor "tptp92-ast:tcf-formula:alt-2" sort_Tptp92Ast_tcf_formula [parameter "tff-atom-typing" sort_Tptp92Ast_tff_atom_typing],
    constructor "tptp92-ast:tcf-logic-formula:alt-1" sort_Tptp92Ast_tcf_logic_formula [parameter "tcf-quantified-formula" sort_Tptp92Ast_tcf_quantified_formula],
    constructor "tptp92-ast:tcf-logic-formula:alt-2" sort_Tptp92Ast_tcf_logic_formula [parameter "cnf-formula" sort_Tptp92Ast_cnf_formula],
    constructor "tptp92-ast:tcf-quantified-formula:alt-1" sort_Tptp92Ast_tcf_quantified_formula [parameter "tff-variable-list" sort_Tptp92Ast_tff_variable_list, parameter "tcf-logic-formula" sort_Tptp92Ast_tcf_logic_formula],
    constructor "tptp92-ast:tf1-quantified-type:alt-1" sort_Tptp92Ast_tf1_quantified_type [parameter "type-quantifier" sort_Tptp92Ast_type_quantifier, parameter "tff-variable-list" sort_Tptp92Ast_tff_variable_list, parameter "tff-monotype" sort_Tptp92Ast_tff_monotype],
    constructor "tptp92-ast:tff-and-formula:alt-1" sort_Tptp92Ast_tff_and_formula [parameter "tff-unit-formula-1" sort_Tptp92Ast_tff_unit_formula, parameter "tff-unit-formula-2" sort_Tptp92Ast_tff_unit_formula],
    constructor "tptp92-ast:tff-and-formula:alt-2" sort_Tptp92Ast_tff_and_formula [parameter "tff-and-formula" sort_Tptp92Ast_tff_and_formula, parameter "tff-unit-formula" sort_Tptp92Ast_tff_unit_formula],
    constructor "tptp92-ast:tff-annotated:alt-1" sort_Tptp92Ast_tff_annotated [parameter "name" sort_Tptp92Ast_name, parameter "formula-role" sort_Tptp92Ast_formula_role, parameter "tff-formula" sort_Tptp92Ast_tff_formula, parameter "annotations" sort_Tptp92Ast_annotations],
    constructor "tptp92-ast:tff-arguments:alt-1" sort_Tptp92Ast_tff_arguments [parameter "tff-term" sort_Tptp92Ast_tff_term, parameter "comma-tff-term" sort_Tptp92AstList_tptp92ast_comma_tff_term]
  ]

private def constructorsPrefix13 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix12 ++ constructorsChunk13

private def constructorsChunk14 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:tff-atom-typing-list:alt-1" sort_Tptp92Ast_tff_atom_typing_list [parameter "tff-atom-typing" sort_Tptp92Ast_tff_atom_typing],
    constructor "tptp92-ast:tff-atom-typing-list:alt-2" sort_Tptp92Ast_tff_atom_typing_list [parameter "tff-atom-typing" sort_Tptp92Ast_tff_atom_typing, parameter "tff-atom-typing-list" sort_Tptp92Ast_tff_atom_typing_list],
    constructor "tptp92-ast:tff-atom-typing:alt-1" sort_Tptp92Ast_tff_atom_typing [parameter "untyped-atom" sort_Tptp92Ast_untyped_atom, parameter "tff-top-level-type" sort_Tptp92Ast_tff_top_level_type],
    constructor "tptp92-ast:tff-atom-typing:alt-2" sort_Tptp92Ast_tff_atom_typing [parameter "tff-atom-typing" sort_Tptp92Ast_tff_atom_typing],
    constructor "tptp92-ast:tff-atomic-formula:alt-1" sort_Tptp92Ast_tff_atomic_formula [parameter "tff-plain-atomic" sort_Tptp92Ast_tff_plain_atomic],
    constructor "tptp92-ast:tff-atomic-formula:alt-2" sort_Tptp92Ast_tff_atomic_formula [parameter "tff-defined-atomic" sort_Tptp92Ast_tff_defined_atomic],
    constructor "tptp92-ast:tff-atomic-formula:alt-3" sort_Tptp92Ast_tff_atomic_formula [parameter "tff-system-atomic" sort_Tptp92Ast_tff_system_atomic],
    constructor "tptp92-ast:tff-atomic-type:alt-1" sort_Tptp92Ast_tff_atomic_type [parameter "type-constant" sort_Tptp92Ast_type_constant],
    constructor "tptp92-ast:tff-atomic-type:alt-2" sort_Tptp92Ast_tff_atomic_type [parameter "defined-type" sort_Tptp92Ast_defined_type],
    constructor "tptp92-ast:tff-atomic-type:alt-3" sort_Tptp92Ast_tff_atomic_type [parameter "variable" sort_Tptp92Ast_variable],
    constructor "tptp92-ast:tff-atomic-type:alt-4" sort_Tptp92Ast_tff_atomic_type [parameter "type-functor" sort_Tptp92Ast_type_functor, parameter "tff-type-arguments" sort_Tptp92Ast_tff_type_arguments],
    constructor "tptp92-ast:tff-atomic-type:alt-5" sort_Tptp92Ast_tff_atomic_type [parameter "tff-atomic-type" sort_Tptp92Ast_tff_atomic_type],
    constructor "tptp92-ast:tff-atomic-type:alt-6" sort_Tptp92Ast_tff_atomic_type [parameter "txf-tuple-type" sort_Tptp92Ast_txf_tuple_type],
    constructor "tptp92-ast:tff-binary-assoc:alt-1" sort_Tptp92Ast_tff_binary_assoc [parameter "tff-or-formula" sort_Tptp92Ast_tff_or_formula],
    constructor "tptp92-ast:tff-binary-assoc:alt-2" sort_Tptp92Ast_tff_binary_assoc [parameter "tff-and-formula" sort_Tptp92Ast_tff_and_formula],
    constructor "tptp92-ast:tff-binary-formula:alt-1" sort_Tptp92Ast_tff_binary_formula [parameter "tff-binary-nonassoc" sort_Tptp92Ast_tff_binary_nonassoc]
  ]

private def constructorsPrefix14 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix13 ++ constructorsChunk14

private def constructorsChunk15 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:tff-binary-formula:alt-2" sort_Tptp92Ast_tff_binary_formula [parameter "tff-binary-assoc" sort_Tptp92Ast_tff_binary_assoc],
    constructor "tptp92-ast:tff-binary-nonassoc:alt-1" sort_Tptp92Ast_tff_binary_nonassoc [parameter "tff-unit-formula-1" sort_Tptp92Ast_tff_unit_formula, parameter "nonassoc-connective" sort_Tptp92Ast_nonassoc_connective, parameter "tff-unit-formula-2" sort_Tptp92Ast_tff_unit_formula],
    constructor "tptp92-ast:tff-defined-atomic:alt-1" sort_Tptp92Ast_tff_defined_atomic [parameter "tff-defined-plain" sort_Tptp92Ast_tff_defined_plain],
    constructor "tptp92-ast:tff-defined-infix:alt-1" sort_Tptp92Ast_tff_defined_infix [parameter "tff-unitary-term-1" sort_Tptp92Ast_tff_unitary_term, parameter "defined-infix-pred" sort_Tptp92Ast_defined_infix_pred, parameter "tff-unitary-term-2" sort_Tptp92Ast_tff_unitary_term],
    constructor "tptp92-ast:tff-defined-plain:alt-1" sort_Tptp92Ast_tff_defined_plain [parameter "defined-constant" sort_Tptp92Ast_defined_constant],
    constructor "tptp92-ast:tff-defined-plain:alt-2" sort_Tptp92Ast_tff_defined_plain [parameter "defined-functor" sort_Tptp92Ast_defined_functor, parameter "tff-arguments" sort_Tptp92Ast_tff_arguments],
    constructor "tptp92-ast:tff-defined-plain:alt-3" sort_Tptp92Ast_tff_defined_plain [parameter "nxf-atom" sort_Tptp92Ast_nxf_atom],
    constructor "tptp92-ast:tff-defined-plain:alt-4" sort_Tptp92Ast_tff_defined_plain [parameter "txf-let" sort_Tptp92Ast_txf_let],
    constructor "tptp92-ast:tff-formula:alt-1" sort_Tptp92Ast_tff_formula [parameter "tff-logic-formula" sort_Tptp92Ast_tff_logic_formula],
    constructor "tptp92-ast:tff-formula:alt-2" sort_Tptp92Ast_tff_formula [parameter "tff-atom-typing" sort_Tptp92Ast_tff_atom_typing],
    constructor "tptp92-ast:tff-formula:alt-3" sort_Tptp92Ast_tff_formula [parameter "tff-subtype" sort_Tptp92Ast_tff_subtype],
    constructor "tptp92-ast:tff-infix-unary:alt-1" sort_Tptp92Ast_tff_infix_unary [parameter "tff-unitary-term-1" sort_Tptp92Ast_tff_unitary_term, parameter "infix-inequality" sort_Tptp92Ast_infix_inequality, parameter "tff-unitary-term-2" sort_Tptp92Ast_tff_unitary_term],
    constructor "tptp92-ast:tff-logic-formula:alt-1" sort_Tptp92Ast_tff_logic_formula [parameter "tff-unitary-formula" sort_Tptp92Ast_tff_unitary_formula],
    constructor "tptp92-ast:tff-logic-formula:alt-2" sort_Tptp92Ast_tff_logic_formula [parameter "tff-unary-formula" sort_Tptp92Ast_tff_unary_formula],
    constructor "tptp92-ast:tff-logic-formula:alt-3" sort_Tptp92Ast_tff_logic_formula [parameter "tff-binary-formula" sort_Tptp92Ast_tff_binary_formula],
    constructor "tptp92-ast:tff-logic-formula:alt-4" sort_Tptp92Ast_tff_logic_formula [parameter "tff-defined-infix" sort_Tptp92Ast_tff_defined_infix]
  ]

private def constructorsPrefix15 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix14 ++ constructorsChunk15

private def constructorsChunk16 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:tff-logic-formula:alt-5" sort_Tptp92Ast_tff_logic_formula [parameter "txf-definition" sort_Tptp92Ast_txf_definition],
    constructor "tptp92-ast:tff-logic-formula:alt-6" sort_Tptp92Ast_tff_logic_formula [parameter "txf-sequent" sort_Tptp92Ast_txf_sequent],
    constructor "tptp92-ast:tff-mapping-type:alt-1" sort_Tptp92Ast_tff_mapping_type [parameter "tff-unitary-type" sort_Tptp92Ast_tff_unitary_type, parameter "tff-atomic-type" sort_Tptp92Ast_tff_atomic_type],
    constructor "tptp92-ast:tff-monotype:alt-1" sort_Tptp92Ast_tff_monotype [parameter "tff-atomic-type" sort_Tptp92Ast_tff_atomic_type],
    constructor "tptp92-ast:tff-monotype:alt-2" sort_Tptp92Ast_tff_monotype [parameter "tff-mapping-type" sort_Tptp92Ast_tff_mapping_type],
    constructor "tptp92-ast:tff-monotype:alt-3" sort_Tptp92Ast_tff_monotype [parameter "tf1-quantified-type" sort_Tptp92Ast_tf1_quantified_type],
    constructor "tptp92-ast:tff-non-atomic-type:alt-1" sort_Tptp92Ast_tff_non_atomic_type [parameter "tff-mapping-type" sort_Tptp92Ast_tff_mapping_type],
    constructor "tptp92-ast:tff-non-atomic-type:alt-2" sort_Tptp92Ast_tff_non_atomic_type [parameter "tf1-quantified-type" sort_Tptp92Ast_tf1_quantified_type],
    constructor "tptp92-ast:tff-non-atomic-type:alt-3" sort_Tptp92Ast_tff_non_atomic_type [parameter "tff-non-atomic-type" sort_Tptp92Ast_tff_non_atomic_type],
    constructor "tptp92-ast:tff-or-formula:alt-1" sort_Tptp92Ast_tff_or_formula [parameter "tff-unit-formula-1" sort_Tptp92Ast_tff_unit_formula, parameter "tff-unit-formula-2" sort_Tptp92Ast_tff_unit_formula],
    constructor "tptp92-ast:tff-or-formula:alt-2" sort_Tptp92Ast_tff_or_formula [parameter "tff-or-formula" sort_Tptp92Ast_tff_or_formula, parameter "tff-unit-formula" sort_Tptp92Ast_tff_unit_formula],
    constructor "tptp92-ast:tff-plain-atomic:alt-1" sort_Tptp92Ast_tff_plain_atomic [parameter "constant" sort_Tptp92Ast_constant],
    constructor "tptp92-ast:tff-plain-atomic:alt-2" sort_Tptp92Ast_tff_plain_atomic [parameter "functor" sort_Tptp92Ast_functor, parameter "tff-arguments" sort_Tptp92Ast_tff_arguments],
    constructor "tptp92-ast:tff-prefix-unary:alt-1" sort_Tptp92Ast_tff_prefix_unary [parameter "tff-unary-connective" sort_Tptp92Ast_tff_unary_connective, parameter "tff-preunit-formula" sort_Tptp92Ast_tff_preunit_formula],
    constructor "tptp92-ast:tff-preunit-formula:alt-1" sort_Tptp92Ast_tff_preunit_formula [parameter "tff-unitary-formula" sort_Tptp92Ast_tff_unitary_formula],
    constructor "tptp92-ast:tff-preunit-formula:alt-2" sort_Tptp92Ast_tff_preunit_formula [parameter "tff-prefix-unary" sort_Tptp92Ast_tff_prefix_unary]
  ]

private def constructorsPrefix16 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix15 ++ constructorsChunk16

private def constructorsChunk17 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:tff-quantified-formula:alt-1" sort_Tptp92Ast_tff_quantified_formula [parameter "tff-quantifier" sort_Tptp92Ast_tff_quantifier, parameter "tff-variable-list" sort_Tptp92Ast_tff_variable_list, parameter "tff-unit-formula" sort_Tptp92Ast_tff_unit_formula],
    constructor "tptp92-ast:tff-quantifier:alt-1" sort_Tptp92Ast_tff_quantifier [parameter "fof-quantifier" sort_Tptp92Ast_fof_quantifier],
    constructor "tptp92-ast:tff-quantifier:alt-2" sort_Tptp92Ast_tff_quantifier [],
    constructor "tptp92-ast:tff-subtype:alt-1" sort_Tptp92Ast_tff_subtype [parameter "untyped-atom" sort_Tptp92Ast_untyped_atom, parameter "subtype-sign" sort_Tptp92Ast_subtype_sign, parameter "atom" sort_Tptp92Ast_atom],
    constructor "tptp92-ast:tff-system-atomic:alt-1" sort_Tptp92Ast_tff_system_atomic [parameter "system-constant" sort_Tptp92Ast_system_constant],
    constructor "tptp92-ast:tff-system-atomic:alt-2" sort_Tptp92Ast_tff_system_atomic [parameter "system-functor" sort_Tptp92Ast_system_functor, parameter "tff-arguments" sort_Tptp92Ast_tff_arguments],
    constructor "tptp92-ast:tff-term:alt-1" sort_Tptp92Ast_tff_term [parameter "tff-logic-formula" sort_Tptp92Ast_tff_logic_formula],
    constructor "tptp92-ast:tff-term:alt-2" sort_Tptp92Ast_tff_term [parameter "defined-term" sort_Tptp92Ast_defined_term],
    constructor "tptp92-ast:tff-term:alt-3" sort_Tptp92Ast_tff_term [parameter "txf-tuple" sort_Tptp92Ast_txf_tuple],
    constructor "tptp92-ast:tff-top-level-type:alt-1" sort_Tptp92Ast_tff_top_level_type [parameter "tff-atomic-type" sort_Tptp92Ast_tff_atomic_type],
    constructor "tptp92-ast:tff-top-level-type:alt-2" sort_Tptp92Ast_tff_top_level_type [parameter "tff-non-atomic-type" sort_Tptp92Ast_tff_non_atomic_type],
    constructor "tptp92-ast:tff-type-arguments:alt-1" sort_Tptp92Ast_tff_type_arguments [parameter "tff-atomic-type" sort_Tptp92Ast_tff_atomic_type],
    constructor "tptp92-ast:tff-type-arguments:alt-2" sort_Tptp92Ast_tff_type_arguments [parameter "tff-atomic-type" sort_Tptp92Ast_tff_atomic_type, parameter "tff-type-arguments" sort_Tptp92Ast_tff_type_arguments],
    constructor "tptp92-ast:tff-type-list:alt-1" sort_Tptp92Ast_tff_type_list [parameter "tff-top-level-type" sort_Tptp92Ast_tff_top_level_type],
    constructor "tptp92-ast:tff-type-list:alt-2" sort_Tptp92Ast_tff_type_list [parameter "tff-top-level-type" sort_Tptp92Ast_tff_top_level_type, parameter "tff-type-list" sort_Tptp92Ast_tff_type_list],
    constructor "tptp92-ast:tff-typed-variable:alt-1" sort_Tptp92Ast_tff_typed_variable [parameter "variable" sort_Tptp92Ast_variable, parameter "tff-atomic-type" sort_Tptp92Ast_tff_atomic_type]
  ]

private def constructorsPrefix17 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix16 ++ constructorsChunk17

private def constructorsChunk18 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:tff-unary-connective:alt-1" sort_Tptp92Ast_tff_unary_connective [parameter "unary-connective" sort_Tptp92Ast_unary_connective],
    constructor "tptp92-ast:tff-unary-connective:alt-2" sort_Tptp92Ast_tff_unary_connective [parameter "ntf-short-connective" sort_Tptp92Ast_ntf_short_connective],
    constructor "tptp92-ast:tff-unary-formula:alt-1" sort_Tptp92Ast_tff_unary_formula [parameter "tff-prefix-unary" sort_Tptp92Ast_tff_prefix_unary],
    constructor "tptp92-ast:tff-unary-formula:alt-2" sort_Tptp92Ast_tff_unary_formula [parameter "tff-infix-unary" sort_Tptp92Ast_tff_infix_unary],
    constructor "tptp92-ast:tff-unit-formula:alt-1" sort_Tptp92Ast_tff_unit_formula [parameter "tff-unitary-formula" sort_Tptp92Ast_tff_unitary_formula],
    constructor "tptp92-ast:tff-unit-formula:alt-2" sort_Tptp92Ast_tff_unit_formula [parameter "tff-unary-formula" sort_Tptp92Ast_tff_unary_formula],
    constructor "tptp92-ast:tff-unit-formula:alt-3" sort_Tptp92Ast_tff_unit_formula [parameter "tff-defined-infix" sort_Tptp92Ast_tff_defined_infix],
    constructor "tptp92-ast:tff-unitary-formula:alt-1" sort_Tptp92Ast_tff_unitary_formula [parameter "tff-quantified-formula" sort_Tptp92Ast_tff_quantified_formula],
    constructor "tptp92-ast:tff-unitary-formula:alt-2" sort_Tptp92Ast_tff_unitary_formula [parameter "tff-atomic-formula" sort_Tptp92Ast_tff_atomic_formula],
    constructor "tptp92-ast:tff-unitary-formula:alt-3" sort_Tptp92Ast_tff_unitary_formula [parameter "txf-unitary-formula" sort_Tptp92Ast_txf_unitary_formula],
    constructor "tptp92-ast:tff-unitary-formula:alt-4" sort_Tptp92Ast_tff_unitary_formula [parameter "tff-logic-formula" sort_Tptp92Ast_tff_logic_formula],
    constructor "tptp92-ast:tff-unitary-term:alt-1" sort_Tptp92Ast_tff_unitary_term [parameter "tff-atomic-formula" sort_Tptp92Ast_tff_atomic_formula],
    constructor "tptp92-ast:tff-unitary-term:alt-2" sort_Tptp92Ast_tff_unitary_term [parameter "defined-term" sort_Tptp92Ast_defined_term],
    constructor "tptp92-ast:tff-unitary-term:alt-3" sort_Tptp92Ast_tff_unitary_term [parameter "txf-tuple" sort_Tptp92Ast_txf_tuple],
    constructor "tptp92-ast:tff-unitary-term:alt-4" sort_Tptp92Ast_tff_unitary_term [parameter "variable" sort_Tptp92Ast_variable],
    constructor "tptp92-ast:tff-unitary-term:alt-5" sort_Tptp92Ast_tff_unitary_term [parameter "tff-logic-formula" sort_Tptp92Ast_tff_logic_formula]
  ]

private def constructorsPrefix18 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix17 ++ constructorsChunk18

private def constructorsChunk19 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:tff-unitary-type:alt-1" sort_Tptp92Ast_tff_unitary_type [parameter "tff-atomic-type" sort_Tptp92Ast_tff_atomic_type],
    constructor "tptp92-ast:tff-unitary-type:alt-2" sort_Tptp92Ast_tff_unitary_type [parameter "tff-xprod-type" sort_Tptp92Ast_tff_xprod_type],
    constructor "tptp92-ast:tff-variable-list:alt-1" sort_Tptp92Ast_tff_variable_list [parameter "tff-variable" sort_Tptp92Ast_tff_variable],
    constructor "tptp92-ast:tff-variable-list:alt-2" sort_Tptp92Ast_tff_variable_list [parameter "tff-variable" sort_Tptp92Ast_tff_variable, parameter "tff-variable-list" sort_Tptp92Ast_tff_variable_list],
    constructor "tptp92-ast:tff-variable:alt-1" sort_Tptp92Ast_tff_variable [parameter "tff-typed-variable" sort_Tptp92Ast_tff_typed_variable],
    constructor "tptp92-ast:tff-variable:alt-2" sort_Tptp92Ast_tff_variable [parameter "variable" sort_Tptp92Ast_variable],
    constructor "tptp92-ast:tff-xprod-type:alt-1" sort_Tptp92Ast_tff_xprod_type [parameter "tff-unitary-type" sort_Tptp92Ast_tff_unitary_type, parameter "tff-atomic-type" sort_Tptp92Ast_tff_atomic_type],
    constructor "tptp92-ast:tff-xprod-type:alt-2" sort_Tptp92Ast_tff_xprod_type [parameter "tff-xprod-type" sort_Tptp92Ast_tff_xprod_type, parameter "tff-atomic-type" sort_Tptp92Ast_tff_atomic_type],
    constructor "tptp92-ast:th0-quantifier:alt-1" sort_Tptp92Ast_th0_quantifier [],
    constructor "tptp92-ast:th0-quantifier:alt-2" sort_Tptp92Ast_th0_quantifier [],
    constructor "tptp92-ast:th0-quantifier:alt-3" sort_Tptp92Ast_th0_quantifier [],
    constructor "tptp92-ast:th1-defined-term:alt-1" sort_Tptp92Ast_th1_defined_term [],
    constructor "tptp92-ast:th1-defined-term:alt-2" sort_Tptp92Ast_th1_defined_term [],
    constructor "tptp92-ast:th1-defined-term:alt-3" sort_Tptp92Ast_th1_defined_term [],
    constructor "tptp92-ast:th1-defined-term:alt-4" sort_Tptp92Ast_th1_defined_term [],
    constructor "tptp92-ast:th1-defined-term:alt-5" sort_Tptp92Ast_th1_defined_term []
  ]

private def constructorsPrefix19 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix18 ++ constructorsChunk19

private def constructorsChunk20 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:theory-name:alt-1" sort_Tptp92Ast_theory_name [parameter "atomic-word" sort_Tptp92Ast_atomic_word],
    constructor "tptp92-ast:theory:alt-1" sort_Tptp92Ast_theory [parameter "theory-name" sort_Tptp92Ast_theory_name, parameter "optional-info" sort_Tptp92Ast_optional_info],
    constructor "tptp92-ast:thf-and-formula:alt-1" sort_Tptp92Ast_thf_and_formula [parameter "thf-unit-formula-1" sort_Tptp92Ast_thf_unit_formula, parameter "thf-unit-formula-2" sort_Tptp92Ast_thf_unit_formula],
    constructor "tptp92-ast:thf-and-formula:alt-2" sort_Tptp92Ast_thf_and_formula [parameter "thf-and-formula" sort_Tptp92Ast_thf_and_formula, parameter "thf-unit-formula" sort_Tptp92Ast_thf_unit_formula],
    constructor "tptp92-ast:thf-annotated:alt-1" sort_Tptp92Ast_thf_annotated [parameter "name" sort_Tptp92Ast_name, parameter "formula-role" sort_Tptp92Ast_formula_role, parameter "thf-formula" sort_Tptp92Ast_thf_formula, parameter "annotations" sort_Tptp92Ast_annotations],
    constructor "tptp92-ast:thf-apply-formula:alt-1" sort_Tptp92Ast_thf_apply_formula [parameter "thf-unit-formula-1" sort_Tptp92Ast_thf_unit_formula, parameter "thf-unit-formula-2" sort_Tptp92Ast_thf_unit_formula],
    constructor "tptp92-ast:thf-apply-formula:alt-2" sort_Tptp92Ast_thf_apply_formula [parameter "thf-apply-formula" sort_Tptp92Ast_thf_apply_formula, parameter "thf-unit-formula" sort_Tptp92Ast_thf_unit_formula],
    constructor "tptp92-ast:thf-apply-type:alt-1" sort_Tptp92Ast_thf_apply_type [parameter "thf-apply-formula" sort_Tptp92Ast_thf_apply_formula],
    constructor "tptp92-ast:thf-arguments:alt-1" sort_Tptp92Ast_thf_arguments [parameter "thf-formula-list" sort_Tptp92Ast_thf_formula_list],
    constructor "tptp92-ast:thf-atom-typing-list:alt-1" sort_Tptp92Ast_thf_atom_typing_list [parameter "thf-atom-typing" sort_Tptp92Ast_thf_atom_typing],
    constructor "tptp92-ast:thf-atom-typing-list:alt-2" sort_Tptp92Ast_thf_atom_typing_list [parameter "thf-atom-typing" sort_Tptp92Ast_thf_atom_typing, parameter "thf-atom-typing-list" sort_Tptp92Ast_thf_atom_typing_list],
    constructor "tptp92-ast:thf-atom-typing:alt-1" sort_Tptp92Ast_thf_atom_typing [parameter "untyped-atom" sort_Tptp92Ast_untyped_atom, parameter "thf-top-level-type" sort_Tptp92Ast_thf_top_level_type],
    constructor "tptp92-ast:thf-atom-typing:alt-2" sort_Tptp92Ast_thf_atom_typing [parameter "thf-atom-typing" sort_Tptp92Ast_thf_atom_typing],
    constructor "tptp92-ast:thf-atomic-formula:alt-1" sort_Tptp92Ast_thf_atomic_formula [parameter "thf-plain-atomic" sort_Tptp92Ast_thf_plain_atomic],
    constructor "tptp92-ast:thf-atomic-formula:alt-2" sort_Tptp92Ast_thf_atomic_formula [parameter "thf-defined-atomic" sort_Tptp92Ast_thf_defined_atomic],
    constructor "tptp92-ast:thf-atomic-formula:alt-3" sort_Tptp92Ast_thf_atomic_formula [parameter "thf-system-atomic" sort_Tptp92Ast_thf_system_atomic]
  ]

private def constructorsPrefix20 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix19 ++ constructorsChunk20

private def constructorsChunk21 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:thf-atomic-formula:alt-4" sort_Tptp92Ast_thf_atomic_formula [parameter "thf-fof-function" sort_Tptp92Ast_thf_fof_function],
    constructor "tptp92-ast:thf-binary-assoc:alt-1" sort_Tptp92Ast_thf_binary_assoc [parameter "thf-or-formula" sort_Tptp92Ast_thf_or_formula],
    constructor "tptp92-ast:thf-binary-assoc:alt-2" sort_Tptp92Ast_thf_binary_assoc [parameter "thf-and-formula" sort_Tptp92Ast_thf_and_formula],
    constructor "tptp92-ast:thf-binary-assoc:alt-3" sort_Tptp92Ast_thf_binary_assoc [parameter "thf-apply-formula" sort_Tptp92Ast_thf_apply_formula],
    constructor "tptp92-ast:thf-binary-formula:alt-1" sort_Tptp92Ast_thf_binary_formula [parameter "thf-binary-nonassoc" sort_Tptp92Ast_thf_binary_nonassoc],
    constructor "tptp92-ast:thf-binary-formula:alt-2" sort_Tptp92Ast_thf_binary_formula [parameter "thf-binary-assoc" sort_Tptp92Ast_thf_binary_assoc],
    constructor "tptp92-ast:thf-binary-formula:alt-3" sort_Tptp92Ast_thf_binary_formula [parameter "thf-binary-type" sort_Tptp92Ast_thf_binary_type],
    constructor "tptp92-ast:thf-binary-nonassoc:alt-1" sort_Tptp92Ast_thf_binary_nonassoc [parameter "thf-unit-formula-1" sort_Tptp92Ast_thf_unit_formula, parameter "nonassoc-connective" sort_Tptp92Ast_nonassoc_connective, parameter "thf-unit-formula-2" sort_Tptp92Ast_thf_unit_formula],
    constructor "tptp92-ast:thf-binary-type:alt-1" sort_Tptp92Ast_thf_binary_type [parameter "thf-mapping-type" sort_Tptp92Ast_thf_mapping_type],
    constructor "tptp92-ast:thf-binary-type:alt-2" sort_Tptp92Ast_thf_binary_type [parameter "thf-xprod-type" sort_Tptp92Ast_thf_xprod_type],
    constructor "tptp92-ast:thf-binary-type:alt-3" sort_Tptp92Ast_thf_binary_type [parameter "thf-union-type" sort_Tptp92Ast_thf_union_type],
    constructor "tptp92-ast:thf-conn-term:alt-1" sort_Tptp92Ast_thf_conn_term [parameter "nonassoc-connective" sort_Tptp92Ast_nonassoc_connective],
    constructor "tptp92-ast:thf-conn-term:alt-2" sort_Tptp92Ast_thf_conn_term [parameter "assoc-connective" sort_Tptp92Ast_assoc_connective],
    constructor "tptp92-ast:thf-conn-term:alt-3" sort_Tptp92Ast_thf_conn_term [parameter "infix-equality" sort_Tptp92Ast_infix_equality],
    constructor "tptp92-ast:thf-conn-term:alt-4" sort_Tptp92Ast_thf_conn_term [parameter "infix-inequality" sort_Tptp92Ast_infix_inequality],
    constructor "tptp92-ast:thf-conn-term:alt-5" sort_Tptp92Ast_thf_conn_term [parameter "thf-unary-connective" sort_Tptp92Ast_thf_unary_connective]
  ]

private def constructorsPrefix21 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix20 ++ constructorsChunk21

private def constructorsChunk22 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:thf-defined-atomic:alt-1" sort_Tptp92Ast_thf_defined_atomic [parameter "defined-constant" sort_Tptp92Ast_defined_constant],
    constructor "tptp92-ast:thf-defined-atomic:alt-2" sort_Tptp92Ast_thf_defined_atomic [parameter "thf-defined-term" sort_Tptp92Ast_thf_defined_term],
    constructor "tptp92-ast:thf-defined-atomic:alt-3" sort_Tptp92Ast_thf_defined_atomic [parameter "thf-conn-term" sort_Tptp92Ast_thf_conn_term],
    constructor "tptp92-ast:thf-defined-atomic:alt-4" sort_Tptp92Ast_thf_defined_atomic [parameter "nhf-long-connective" sort_Tptp92Ast_nhf_long_connective],
    constructor "tptp92-ast:thf-defined-atomic:alt-5" sort_Tptp92Ast_thf_defined_atomic [parameter "thf-let" sort_Tptp92Ast_thf_let],
    constructor "tptp92-ast:thf-defined-infix:alt-1" sort_Tptp92Ast_thf_defined_infix [parameter "thf-unitary-term-1" sort_Tptp92Ast_thf_unitary_term, parameter "defined-infix-pred" sort_Tptp92Ast_defined_infix_pred, parameter "thf-unitary-term-2" sort_Tptp92Ast_thf_unitary_term],
    constructor "tptp92-ast:thf-defined-term:alt-1" sort_Tptp92Ast_thf_defined_term [parameter "defined-term" sort_Tptp92Ast_defined_term],
    constructor "tptp92-ast:thf-defined-term:alt-2" sort_Tptp92Ast_thf_defined_term [parameter "th1-defined-term" sort_Tptp92Ast_th1_defined_term],
    constructor "tptp92-ast:thf-definition:alt-1" sort_Tptp92Ast_thf_definition [parameter "thf-atomic-formula" sort_Tptp92Ast_thf_atomic_formula, parameter "identical" sort_Tptp92Ast_identical, parameter "thf-logic-formula" sort_Tptp92Ast_thf_logic_formula],
    constructor "tptp92-ast:thf-fof-function:alt-1" sort_Tptp92Ast_thf_fof_function [parameter "functor" sort_Tptp92Ast_functor, parameter "thf-arguments" sort_Tptp92Ast_thf_arguments],
    constructor "tptp92-ast:thf-fof-function:alt-2" sort_Tptp92Ast_thf_fof_function [parameter "defined-functor" sort_Tptp92Ast_defined_functor, parameter "thf-arguments" sort_Tptp92Ast_thf_arguments],
    constructor "tptp92-ast:thf-fof-function:alt-3" sort_Tptp92Ast_thf_fof_function [parameter "system-functor" sort_Tptp92Ast_system_functor, parameter "thf-arguments" sort_Tptp92Ast_thf_arguments],
    constructor "tptp92-ast:thf-formula-list:alt-1" sort_Tptp92Ast_thf_formula_list [parameter "thf-logic-formula" sort_Tptp92Ast_thf_logic_formula, parameter "comma-thf-logic-formula" sort_Tptp92AstList_tptp92ast_comma_thf_logic_formula],
    constructor "tptp92-ast:thf-formula:alt-1" sort_Tptp92Ast_thf_formula [parameter "thf-logic-formula" sort_Tptp92Ast_thf_logic_formula],
    constructor "tptp92-ast:thf-formula:alt-2" sort_Tptp92Ast_thf_formula [parameter "thf-atom-typing" sort_Tptp92Ast_thf_atom_typing],
    constructor "tptp92-ast:thf-formula:alt-3" sort_Tptp92Ast_thf_formula [parameter "thf-subtype" sort_Tptp92Ast_thf_subtype]
  ]

private def constructorsPrefix22 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix21 ++ constructorsChunk22

private def constructorsChunk23 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:thf-infix-unary:alt-1" sort_Tptp92Ast_thf_infix_unary [parameter "thf-unitary-term-1" sort_Tptp92Ast_thf_unitary_term, parameter "infix-inequality" sort_Tptp92Ast_infix_inequality, parameter "thf-unitary-term-2" sort_Tptp92Ast_thf_unitary_term],
    constructor "tptp92-ast:thf-let-defn-list:alt-1" sort_Tptp92Ast_thf_let_defn_list [parameter "thf-let-defn" sort_Tptp92Ast_thf_let_defn],
    constructor "tptp92-ast:thf-let-defn-list:alt-2" sort_Tptp92Ast_thf_let_defn_list [parameter "thf-let-defn" sort_Tptp92Ast_thf_let_defn, parameter "thf-let-defn-list" sort_Tptp92Ast_thf_let_defn_list],
    constructor "tptp92-ast:thf-let-defn:alt-1" sort_Tptp92Ast_thf_let_defn [parameter "thf-logic-formula-1" sort_Tptp92Ast_thf_logic_formula, parameter "assignment" sort_Tptp92Ast_assignment, parameter "thf-logic-formula-2" sort_Tptp92Ast_thf_logic_formula],
    constructor "tptp92-ast:thf-let-defns:alt-1" sort_Tptp92Ast_thf_let_defns [parameter "thf-let-defn" sort_Tptp92Ast_thf_let_defn],
    constructor "tptp92-ast:thf-let-defns:alt-2" sort_Tptp92Ast_thf_let_defns [parameter "thf-let-defn-list" sort_Tptp92Ast_thf_let_defn_list],
    constructor "tptp92-ast:thf-let-types:alt-1" sort_Tptp92Ast_thf_let_types [parameter "thf-atom-typing" sort_Tptp92Ast_thf_atom_typing],
    constructor "tptp92-ast:thf-let-types:alt-2" sort_Tptp92Ast_thf_let_types [parameter "thf-atom-typing-list" sort_Tptp92Ast_thf_atom_typing_list],
    constructor "tptp92-ast:thf-let:alt-1" sort_Tptp92Ast_thf_let [parameter "thf-let-types" sort_Tptp92Ast_thf_let_types, parameter "thf-let-defns" sort_Tptp92Ast_thf_let_defns, parameter "thf-logic-formula" sort_Tptp92Ast_thf_logic_formula],
    constructor "tptp92-ast:thf-logic-formula:alt-1" sort_Tptp92Ast_thf_logic_formula [parameter "thf-unitary-formula" sort_Tptp92Ast_thf_unitary_formula],
    constructor "tptp92-ast:thf-logic-formula:alt-2" sort_Tptp92Ast_thf_logic_formula [parameter "thf-unary-formula" sort_Tptp92Ast_thf_unary_formula],
    constructor "tptp92-ast:thf-logic-formula:alt-3" sort_Tptp92Ast_thf_logic_formula [parameter "thf-binary-formula" sort_Tptp92Ast_thf_binary_formula],
    constructor "tptp92-ast:thf-logic-formula:alt-4" sort_Tptp92Ast_thf_logic_formula [parameter "thf-defined-infix" sort_Tptp92Ast_thf_defined_infix],
    constructor "tptp92-ast:thf-logic-formula:alt-5" sort_Tptp92Ast_thf_logic_formula [parameter "thf-definition" sort_Tptp92Ast_thf_definition],
    constructor "tptp92-ast:thf-logic-formula:alt-6" sort_Tptp92Ast_thf_logic_formula [parameter "thf-sequent" sort_Tptp92Ast_thf_sequent],
    constructor "tptp92-ast:thf-mapping-type:alt-1" sort_Tptp92Ast_thf_mapping_type [parameter "thf-unitary-type-1" sort_Tptp92Ast_thf_unitary_type, parameter "thf-unitary-type-2" sort_Tptp92Ast_thf_unitary_type]
  ]

private def constructorsPrefix23 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix22 ++ constructorsChunk23

private def constructorsChunk24 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:thf-mapping-type:alt-2" sort_Tptp92Ast_thf_mapping_type [parameter "thf-unitary-type" sort_Tptp92Ast_thf_unitary_type, parameter "thf-mapping-type" sort_Tptp92Ast_thf_mapping_type],
    constructor "tptp92-ast:thf-or-formula:alt-1" sort_Tptp92Ast_thf_or_formula [parameter "thf-unit-formula-1" sort_Tptp92Ast_thf_unit_formula, parameter "thf-unit-formula-2" sort_Tptp92Ast_thf_unit_formula],
    constructor "tptp92-ast:thf-or-formula:alt-2" sort_Tptp92Ast_thf_or_formula [parameter "thf-or-formula" sort_Tptp92Ast_thf_or_formula, parameter "thf-unit-formula" sort_Tptp92Ast_thf_unit_formula],
    constructor "tptp92-ast:thf-plain-atomic:alt-1" sort_Tptp92Ast_thf_plain_atomic [parameter "constant" sort_Tptp92Ast_constant],
    constructor "tptp92-ast:thf-plain-atomic:alt-2" sort_Tptp92Ast_thf_plain_atomic [parameter "thf-tuple" sort_Tptp92Ast_thf_tuple],
    constructor "tptp92-ast:thf-prefix-unary:alt-1" sort_Tptp92Ast_thf_prefix_unary [parameter "thf-unary-connective" sort_Tptp92Ast_thf_unary_connective, parameter "thf-preunit-formula" sort_Tptp92Ast_thf_preunit_formula],
    constructor "tptp92-ast:thf-preunit-formula:alt-1" sort_Tptp92Ast_thf_preunit_formula [parameter "thf-unitary-formula" sort_Tptp92Ast_thf_unitary_formula],
    constructor "tptp92-ast:thf-preunit-formula:alt-2" sort_Tptp92Ast_thf_preunit_formula [parameter "thf-prefix-unary" sort_Tptp92Ast_thf_prefix_unary],
    constructor "tptp92-ast:thf-quantification:alt-1" sort_Tptp92Ast_thf_quantification [parameter "thf-quantifier" sort_Tptp92Ast_thf_quantifier, parameter "thf-variable-list" sort_Tptp92Ast_thf_variable_list],
    constructor "tptp92-ast:thf-quantified-formula:alt-1" sort_Tptp92Ast_thf_quantified_formula [parameter "thf-quantification" sort_Tptp92Ast_thf_quantification, parameter "thf-unit-formula" sort_Tptp92Ast_thf_unit_formula],
    constructor "tptp92-ast:thf-quantifier:alt-1" sort_Tptp92Ast_thf_quantifier [parameter "tff-quantifier" sort_Tptp92Ast_tff_quantifier],
    constructor "tptp92-ast:thf-quantifier:alt-2" sort_Tptp92Ast_thf_quantifier [parameter "th0-quantifier" sort_Tptp92Ast_th0_quantifier],
    constructor "tptp92-ast:thf-quantifier:alt-3" sort_Tptp92Ast_thf_quantifier [parameter "type-quantifier" sort_Tptp92Ast_type_quantifier],
    constructor "tptp92-ast:thf-sequent:alt-1" sort_Tptp92Ast_thf_sequent [parameter "thf-tuple-1" sort_Tptp92Ast_thf_tuple, parameter "gentzen-arrow" sort_Tptp92Ast_gentzen_arrow, parameter "thf-tuple-2" sort_Tptp92Ast_thf_tuple],
    constructor "tptp92-ast:thf-subtype:alt-1" sort_Tptp92Ast_thf_subtype [parameter "untyped-atom" sort_Tptp92Ast_untyped_atom, parameter "subtype-sign" sort_Tptp92Ast_subtype_sign, parameter "atom" sort_Tptp92Ast_atom],
    constructor "tptp92-ast:thf-system-atomic:alt-1" sort_Tptp92Ast_thf_system_atomic [parameter "system-constant" sort_Tptp92Ast_system_constant]
  ]

private def constructorsPrefix24 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix23 ++ constructorsChunk24

private def constructorsChunk25 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:thf-top-level-type:alt-1" sort_Tptp92Ast_thf_top_level_type [parameter "thf-unitary-type" sort_Tptp92Ast_thf_unitary_type],
    constructor "tptp92-ast:thf-top-level-type:alt-2" sort_Tptp92Ast_thf_top_level_type [parameter "thf-mapping-type" sort_Tptp92Ast_thf_mapping_type],
    constructor "tptp92-ast:thf-top-level-type:alt-3" sort_Tptp92Ast_thf_top_level_type [parameter "thf-apply-type" sort_Tptp92Ast_thf_apply_type],
    constructor "tptp92-ast:thf-tuple:alt-1" sort_Tptp92Ast_thf_tuple [],
    constructor "tptp92-ast:thf-tuple:alt-2" sort_Tptp92Ast_thf_tuple [parameter "thf-formula-list" sort_Tptp92Ast_thf_formula_list],
    constructor "tptp92-ast:thf-typed-variable:alt-1" sort_Tptp92Ast_thf_typed_variable [parameter "variable" sort_Tptp92Ast_variable, parameter "thf-top-level-type" sort_Tptp92Ast_thf_top_level_type],
    constructor "tptp92-ast:thf-unary-connective:alt-1" sort_Tptp92Ast_thf_unary_connective [parameter "unary-connective" sort_Tptp92Ast_unary_connective],
    constructor "tptp92-ast:thf-unary-connective:alt-2" sort_Tptp92Ast_thf_unary_connective [parameter "ntf-short-connective" sort_Tptp92Ast_ntf_short_connective],
    constructor "tptp92-ast:thf-unary-formula:alt-1" sort_Tptp92Ast_thf_unary_formula [parameter "thf-prefix-unary" sort_Tptp92Ast_thf_prefix_unary],
    constructor "tptp92-ast:thf-unary-formula:alt-2" sort_Tptp92Ast_thf_unary_formula [parameter "thf-infix-unary" sort_Tptp92Ast_thf_infix_unary],
    constructor "tptp92-ast:thf-union-type:alt-1" sort_Tptp92Ast_thf_union_type [parameter "thf-unitary-type-1" sort_Tptp92Ast_thf_unitary_type, parameter "thf-unitary-type-2" sort_Tptp92Ast_thf_unitary_type],
    constructor "tptp92-ast:thf-union-type:alt-2" sort_Tptp92Ast_thf_union_type [parameter "thf-union-type" sort_Tptp92Ast_thf_union_type, parameter "thf-unitary-type" sort_Tptp92Ast_thf_unitary_type],
    constructor "tptp92-ast:thf-unit-formula:alt-1" sort_Tptp92Ast_thf_unit_formula [parameter "thf-unitary-formula" sort_Tptp92Ast_thf_unitary_formula],
    constructor "tptp92-ast:thf-unit-formula:alt-2" sort_Tptp92Ast_thf_unit_formula [parameter "thf-unary-formula" sort_Tptp92Ast_thf_unary_formula],
    constructor "tptp92-ast:thf-unit-formula:alt-3" sort_Tptp92Ast_thf_unit_formula [parameter "thf-defined-infix" sort_Tptp92Ast_thf_defined_infix],
    constructor "tptp92-ast:thf-unitary-formula:alt-1" sort_Tptp92Ast_thf_unitary_formula [parameter "thf-quantified-formula" sort_Tptp92Ast_thf_quantified_formula]
  ]

private def constructorsPrefix25 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix24 ++ constructorsChunk25

private def constructorsChunk26 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:thf-unitary-formula:alt-2" sort_Tptp92Ast_thf_unitary_formula [parameter "thf-atomic-formula" sort_Tptp92Ast_thf_atomic_formula],
    constructor "tptp92-ast:thf-unitary-formula:alt-3" sort_Tptp92Ast_thf_unitary_formula [parameter "variable" sort_Tptp92Ast_variable],
    constructor "tptp92-ast:thf-unitary-formula:alt-4" sort_Tptp92Ast_thf_unitary_formula [parameter "thf-logic-formula" sort_Tptp92Ast_thf_logic_formula],
    constructor "tptp92-ast:thf-unitary-term:alt-1" sort_Tptp92Ast_thf_unitary_term [parameter "thf-atomic-formula" sort_Tptp92Ast_thf_atomic_formula],
    constructor "tptp92-ast:thf-unitary-term:alt-2" sort_Tptp92Ast_thf_unitary_term [parameter "variable" sort_Tptp92Ast_variable],
    constructor "tptp92-ast:thf-unitary-term:alt-3" sort_Tptp92Ast_thf_unitary_term [parameter "thf-logic-formula" sort_Tptp92Ast_thf_logic_formula],
    constructor "tptp92-ast:thf-unitary-type:alt-1" sort_Tptp92Ast_thf_unitary_type [parameter "thf-unitary-formula" sort_Tptp92Ast_thf_unitary_formula],
    constructor "tptp92-ast:thf-variable-list:alt-1" sort_Tptp92Ast_thf_variable_list [parameter "thf-typed-variable" sort_Tptp92Ast_thf_typed_variable],
    constructor "tptp92-ast:thf-variable-list:alt-2" sort_Tptp92Ast_thf_variable_list [parameter "thf-typed-variable" sort_Tptp92Ast_thf_typed_variable, parameter "thf-variable-list" sort_Tptp92Ast_thf_variable_list],
    constructor "tptp92-ast:thf-xprod-type:alt-1" sort_Tptp92Ast_thf_xprod_type [parameter "thf-unitary-type-1" sort_Tptp92Ast_thf_unitary_type, parameter "thf-unitary-type-2" sort_Tptp92Ast_thf_unitary_type],
    constructor "tptp92-ast:thf-xprod-type:alt-2" sort_Tptp92Ast_thf_xprod_type [parameter "thf-xprod-type" sort_Tptp92Ast_thf_xprod_type, parameter "thf-unitary-type" sort_Tptp92Ast_thf_unitary_type],
    constructor "tptp92-ast:token:back-quoted" sort_Tptp92AstToken_back_quoted [parameter "lexeme" sort_String],
    constructor "tptp92-ast:token:distinct-object" sort_Tptp92AstToken_distinct_object [parameter "lexeme" sort_String],
    constructor "tptp92-ast:token:dollar-dollar-word" sort_Tptp92AstToken_dollar_dollar_word [parameter "lexeme" sort_String],
    constructor "tptp92-ast:token:dollar-word" sort_Tptp92AstToken_dollar_word [parameter "lexeme" sort_String],
    constructor "tptp92-ast:token:integer" sort_Tptp92AstToken_integer [parameter "lexeme" sort_String]
  ]

private def constructorsPrefix26 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix25 ++ constructorsChunk26

private def constructorsChunk27 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:token:lower-word" sort_Tptp92AstToken_lower_word [parameter "lexeme" sort_String],
    constructor "tptp92-ast:token:rational" sort_Tptp92AstToken_rational [parameter "lexeme" sort_String],
    constructor "tptp92-ast:token:real" sort_Tptp92AstToken_real [parameter "lexeme" sort_String],
    constructor "tptp92-ast:token:single-quoted" sort_Tptp92AstToken_single_quoted [parameter "lexeme" sort_String],
    constructor "tptp92-ast:token:upper-word" sort_Tptp92AstToken_upper_word [parameter "lexeme" sort_String],
    constructor "tptp92-ast:tpi-annotated:alt-1" sort_Tptp92Ast_tpi_annotated [parameter "name" sort_Tptp92Ast_name, parameter "formula-role" sort_Tptp92Ast_formula_role, parameter "tpi-formula" sort_Tptp92Ast_tpi_formula, parameter "annotations" sort_Tptp92Ast_annotations],
    constructor "tptp92-ast:tpi-formula:alt-1" sort_Tptp92Ast_tpi_formula [parameter "fof-formula" sort_Tptp92Ast_fof_formula],
    constructor "tptp92-ast:tptp-file:alt-1" sort_Tptp92Ast_tptp_file [parameter "tptp-input" sort_Tptp92AstList_tptp92ast_tptp_input],
    constructor "tptp92-ast:tptp-input:alt-1" sort_Tptp92Ast_tptp_input [parameter "annotated-formula" sort_Tptp92Ast_annotated_formula, parameter "span" sort_Tptp92Ast_source_span],
    constructor "tptp92-ast:tptp-input:alt-2" sort_Tptp92Ast_tptp_input [parameter "include" sort_Tptp92Ast_include, parameter "span" sort_Tptp92Ast_source_span],
    constructor "tptp92-ast:txf-definition:alt-1" sort_Tptp92Ast_txf_definition [parameter "tff-atomic-formula" sort_Tptp92Ast_tff_atomic_formula, parameter "identical" sort_Tptp92Ast_identical, parameter "tff-term" sort_Tptp92Ast_tff_term],
    constructor "tptp92-ast:txf-let-defn-list:alt-1" sort_Tptp92Ast_txf_let_defn_list [parameter "txf-let-defn" sort_Tptp92Ast_txf_let_defn],
    constructor "tptp92-ast:txf-let-defn-list:alt-2" sort_Tptp92Ast_txf_let_defn_list [parameter "txf-let-defn" sort_Tptp92Ast_txf_let_defn, parameter "txf-let-defn-list" sort_Tptp92Ast_txf_let_defn_list],
    constructor "tptp92-ast:txf-let-defn:alt-1" sort_Tptp92Ast_txf_let_defn [parameter "txf-let-lhs" sort_Tptp92Ast_txf_let_lhs, parameter "assignment" sort_Tptp92Ast_assignment, parameter "tff-term" sort_Tptp92Ast_tff_term],
    constructor "tptp92-ast:txf-let-defns:alt-1" sort_Tptp92Ast_txf_let_defns [parameter "txf-let-defn" sort_Tptp92Ast_txf_let_defn],
    constructor "tptp92-ast:txf-let-defns:alt-2" sort_Tptp92Ast_txf_let_defns [parameter "txf-let-defn-list" sort_Tptp92Ast_txf_let_defn_list]
  ]

private def constructorsPrefix27 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix26 ++ constructorsChunk27

private def constructorsChunk28 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:txf-let-lhs:alt-1" sort_Tptp92Ast_txf_let_lhs [parameter "tff-plain-atomic" sort_Tptp92Ast_tff_plain_atomic],
    constructor "tptp92-ast:txf-let-lhs:alt-2" sort_Tptp92Ast_txf_let_lhs [parameter "txf-tuple" sort_Tptp92Ast_txf_tuple],
    constructor "tptp92-ast:txf-let-types:alt-1" sort_Tptp92Ast_txf_let_types [parameter "tff-atom-typing" sort_Tptp92Ast_tff_atom_typing],
    constructor "tptp92-ast:txf-let-types:alt-2" sort_Tptp92Ast_txf_let_types [parameter "tff-atom-typing-list" sort_Tptp92Ast_tff_atom_typing_list],
    constructor "tptp92-ast:txf-let:alt-1" sort_Tptp92Ast_txf_let [parameter "txf-let-types" sort_Tptp92Ast_txf_let_types, parameter "txf-let-defns" sort_Tptp92Ast_txf_let_defns, parameter "tff-term" sort_Tptp92Ast_tff_term],
    constructor "tptp92-ast:txf-sequent:alt-1" sort_Tptp92Ast_txf_sequent [parameter "txf-tuple-1" sort_Tptp92Ast_txf_tuple, parameter "gentzen-arrow" sort_Tptp92Ast_gentzen_arrow, parameter "txf-tuple-2" sort_Tptp92Ast_txf_tuple],
    constructor "tptp92-ast:txf-tuple-type:alt-1" sort_Tptp92Ast_txf_tuple_type [parameter "tff-type-list" sort_Tptp92Ast_tff_type_list],
    constructor "tptp92-ast:txf-tuple:alt-1" sort_Tptp92Ast_txf_tuple [],
    constructor "tptp92-ast:txf-tuple:alt-2" sort_Tptp92Ast_txf_tuple [parameter "tff-arguments" sort_Tptp92Ast_tff_arguments],
    constructor "tptp92-ast:txf-unitary-formula:alt-1" sort_Tptp92Ast_txf_unitary_formula [parameter "variable" sort_Tptp92Ast_variable],
    constructor "tptp92-ast:type-constant:alt-1" sort_Tptp92Ast_type_constant [parameter "type-functor" sort_Tptp92Ast_type_functor],
    constructor "tptp92-ast:type-functor:alt-1" sort_Tptp92Ast_type_functor [parameter "atomic-word" sort_Tptp92Ast_atomic_word],
    constructor "tptp92-ast:type-quantifier:alt-1" sort_Tptp92Ast_type_quantifier [],
    constructor "tptp92-ast:type-quantifier:alt-2" sort_Tptp92Ast_type_quantifier [],
    constructor "tptp92-ast:unary-connective:alt-1" sort_Tptp92Ast_unary_connective [],
    constructor "tptp92-ast:untyped-atom:alt-1" sort_Tptp92Ast_untyped_atom [parameter "constant" sort_Tptp92Ast_constant]
  ]

private def constructorsPrefix28 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix27 ++ constructorsChunk28

private def constructorsChunk29 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp92-ast:untyped-atom:alt-2" sort_Tptp92Ast_untyped_atom [parameter "system-constant" sort_Tptp92Ast_system_constant],
    constructor "tptp92-ast:useful-info:alt-1" sort_Tptp92Ast_useful_info [parameter "general-list" sort_Tptp92Ast_general_list],
    constructor "tptp92-ast:variable:alt-1" sort_Tptp92Ast_variable [parameter "upper-word" sort_Tptp92AstToken_upper_word]
  ]

private def constructorsPrefix29 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix28 ++ constructorsChunk29

def constructors : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix29

def language : LanguageDef :=
  IndexedConstructorSignature.language
    "TptpOfficialAbstractSyntaxV9200" types constructors

private def integerTypeIndex : Fin types.length :=
  ⟨0, by decide⟩

def integerTypeDeclaration : TypeDecl := types.get integerTypeIndex

theorem integerTypeDeclaration_shape :
    integerTypeDeclaration =
      { name := "Integer", carrier := .builtinInt } := by
  rfl

theorem integerTypeDeclaration_mem_language :
    List.Mem integerTypeDeclaration language.types := by
  exact List.get_mem types integerTypeIndex

private def sourceSpanConstructorIndex : Fin constructors.length :=
  ⟨201, by decide⟩

def sourceSpanConstructor :
    IndexedConstructorSignature.Constructor types :=
  constructors.get sourceSpanConstructorIndex

theorem sourceSpanConstructor_shape :
    sourceSpanConstructor =
      constructor "tptp92-ast:source-span" sort_Tptp92Ast_source_span [parameter "start" sort_Integer, parameter "stop" sort_Integer] := by
  rfl

def sourceSpanRule : GrammarRule :=
  sourceSpanConstructor.toGrammarRule

theorem sourceSpanRule_shape :
    sourceSpanRule = {
      label := "tptp92-ast:source-span"
      category := "Tptp92Ast:source-span"
      params := [
        .simple "start" (.base "Integer"),
        .simple "stop" (.base "Integer")]
      syntaxPattern := []
      evalPolicy? := none
    } := by
  simp [sourceSpanRule, sourceSpanConstructor_shape, constructor, parameter,
    IndexedConstructorSignature.Constructor.toGrammarRule,
    IndexedConstructorSignature.Parameter.toTermParam]
  exact ⟨rfl, rfl⟩

theorem sourceSpanRule_mem_language :
    List.Mem sourceSpanRule language.terms := by
  exact List.mem_map_of_mem
    (List.get_mem constructors sourceSpanConstructorIndex)

private def annotatedInputConstructorIndex : Fin constructors.length :=
  ⟨440, by decide⟩

def annotatedInputConstructor :
    IndexedConstructorSignature.Constructor types :=
  constructors.get annotatedInputConstructorIndex

theorem annotatedInputConstructor_shape :
    annotatedInputConstructor =
      constructor "tptp92-ast:tptp-input:alt-1" sort_Tptp92Ast_tptp_input [parameter "annotated-formula" sort_Tptp92Ast_annotated_formula, parameter "span" sort_Tptp92Ast_source_span] := by
  rfl

def annotatedInputRule : GrammarRule :=
  annotatedInputConstructor.toGrammarRule

theorem annotatedInputRule_shape :
    annotatedInputRule = {
      label := "tptp92-ast:tptp-input:alt-1"
      category := "Tptp92Ast:tptp-input"
      params := [
        .simple "annotated-formula"
          (.base "Tptp92Ast:annotated-formula"),
        .simple "span" (.base "Tptp92Ast:source-span")]
      syntaxPattern := []
      evalPolicy? := none
    } := by
  simp [annotatedInputRule, annotatedInputConstructor_shape, constructor,
    parameter, IndexedConstructorSignature.Constructor.toGrammarRule,
    IndexedConstructorSignature.Parameter.toTermParam]
  exact ⟨rfl, rfl, rfl⟩

theorem annotatedInputRule_mem_language :
    List.Mem annotatedInputRule language.terms := by
  exact List.mem_map_of_mem
    (List.get_mem constructors annotatedInputConstructorIndex)

private def includeInputConstructorIndex : Fin constructors.length :=
  ⟨441, by decide⟩

def includeInputConstructor :
    IndexedConstructorSignature.Constructor types :=
  constructors.get includeInputConstructorIndex

theorem includeInputConstructor_shape :
    includeInputConstructor =
      constructor "tptp92-ast:tptp-input:alt-2" sort_Tptp92Ast_tptp_input [parameter "include" sort_Tptp92Ast_include, parameter "span" sort_Tptp92Ast_source_span] := by
  rfl

def includeInputRule : GrammarRule :=
  includeInputConstructor.toGrammarRule

theorem includeInputRule_shape :
    includeInputRule = {
      label := "tptp92-ast:tptp-input:alt-2"
      category := "Tptp92Ast:tptp-input"
      params := [
        .simple "include" (.base "Tptp92Ast:include"),
        .simple "span" (.base "Tptp92Ast:source-span")]
      syntaxPattern := []
      evalPolicy? := none
    } := by
  simp [includeInputRule, includeInputConstructor_shape, constructor,
    parameter, IndexedConstructorSignature.Constructor.toGrammarRule,
    IndexedConstructorSignature.Parameter.toTermParam]
  exact ⟨rfl, rfl, rfl⟩

theorem includeInputRule_mem_language :
    List.Mem includeInputRule language.terms := by
  exact List.mem_map_of_mem
    (List.get_mem constructors includeInputConstructorIndex)

private theorem typesNamesIncreasing :
    List.IsChain (fun first second : String => first < second)
      (types.map (·.name)) := by
  decide +kernel

private theorem typesNodup :
    (types.map (·.name)).Nodup := by
  exact typesNamesIncreasing.pairwise.imp
    (fun {first second} lt equal => by
      subst second
      exact String.lt_irrefl first lt)

private theorem constructorsNamesIncreasing :
    List.IsChain (fun first second : String => first < second)
      (constructors.map (·.label)) := by
  decide +kernel

private theorem constructorsNodup :
    (constructors.map (·.label)).Nodup := by
  exact constructorsNamesIncreasing.pairwise.imp
    (fun {first second} lt equal => by
      subst second
      exact String.lt_irrefl first lt)

theorem language_validate : language.validate = [] := by
  exact IndexedConstructorSignature.language_validate
    "TptpOfficialAbstractSyntaxV9200" types constructors
    typesNodup constructorsNodup

theorem language_inventory :
    language.types.length = 251 ∧
      language.terms.length = 467 ∧
      language.rewrites.length = 0 := by
  decide

def emptyFile : Pattern :=
  a "tptp92-ast:tptp-file:alt-1"
    [a "tptp92-ast:list:tptp92ast-tptp-input:nil"]

def fofAnnotatedExample : Pattern :=
  a "tptp92-ast:fof-annotated:alt-1" [a "tptp92-ast:name:alt-2" [a "tptp92-ast:token:integer" [a "sample"]], a "tptp92-ast:formula-role:alt-1" [a "tptp92-ast:token:lower-word" [a "sample"]], a "tptp92-ast:fof-formula:alt-2" [a "tptp92-ast:fof-sequent:alt-1" [a "tptp92-ast:fof-formula-tuple:alt-1", a "tptp92-ast:gentzen-arrow:alt-1", a "tptp92-ast:fof-formula-tuple:alt-1"]], a "tptp92-ast:annotations:alt-2"]

def cnfAnnotatedExample : Pattern :=
  a "tptp92-ast:cnf-annotated:alt-1" [a "tptp92-ast:name:alt-2" [a "tptp92-ast:token:integer" [a "sample"]], a "tptp92-ast:formula-role:alt-1" [a "tptp92-ast:token:lower-word" [a "sample"]], a "tptp92-ast:cnf-formula:alt-1" [a "tptp92-ast:cnf-disjunction:alt-1" [a "tptp92-ast:cnf-literal:alt-4" [a "tptp92-ast:fof-infix-unary:alt-1" [a "tptp92-ast:fof-term:alt-2" [a "tptp92-ast:variable:alt-1" [a "tptp92-ast:token:upper-word" [a "sample"]]], a "tptp92-ast:infix-inequality:alt-1", a "tptp92-ast:fof-term:alt-2" [a "tptp92-ast:variable:alt-1" [a "tptp92-ast:token:upper-word" [a "sample"]]]]]]], a "tptp92-ast:annotations:alt-2"]

def tffAnnotatedExample : Pattern :=
  a "tptp92-ast:tff-annotated:alt-1" [a "tptp92-ast:name:alt-2" [a "tptp92-ast:token:integer" [a "sample"]], a "tptp92-ast:formula-role:alt-1" [a "tptp92-ast:token:lower-word" [a "sample"]], a "tptp92-ast:tff-formula:alt-1" [a "tptp92-ast:tff-logic-formula:alt-6" [a "tptp92-ast:txf-sequent:alt-1" [a "tptp92-ast:txf-tuple:alt-1", a "tptp92-ast:gentzen-arrow:alt-1", a "tptp92-ast:txf-tuple:alt-1"]]], a "tptp92-ast:annotations:alt-2"]

def tcfAnnotatedExample : Pattern :=
  a "tptp92-ast:tcf-annotated:alt-1" [a "tptp92-ast:name:alt-2" [a "tptp92-ast:token:integer" [a "sample"]], a "tptp92-ast:formula-role:alt-1" [a "tptp92-ast:token:lower-word" [a "sample"]], a "tptp92-ast:tcf-formula:alt-2" [a "tptp92-ast:tff-atom-typing:alt-1" [a "tptp92-ast:untyped-atom:alt-1" [a "tptp92-ast:constant:alt-1" [a "tptp92-ast:functor:alt-1" [a "tptp92-ast:atomic-word:alt-1" [a "tptp92-ast:token:lower-word" [a "sample"]]]]], a "tptp92-ast:tff-top-level-type:alt-1" [a "tptp92-ast:tff-atomic-type:alt-3" [a "tptp92-ast:variable:alt-1" [a "tptp92-ast:token:upper-word" [a "sample"]]]]]], a "tptp92-ast:annotations:alt-2"]

def thfAnnotatedExample : Pattern :=
  a "tptp92-ast:thf-annotated:alt-1" [a "tptp92-ast:name:alt-2" [a "tptp92-ast:token:integer" [a "sample"]], a "tptp92-ast:formula-role:alt-1" [a "tptp92-ast:token:lower-word" [a "sample"]], a "tptp92-ast:thf-formula:alt-1" [a "tptp92-ast:thf-logic-formula:alt-1" [a "tptp92-ast:thf-unitary-formula:alt-3" [a "tptp92-ast:variable:alt-1" [a "tptp92-ast:token:upper-word" [a "sample"]]]]], a "tptp92-ast:annotations:alt-2"]

def tpiAnnotatedExample : Pattern :=
  a "tptp92-ast:tpi-annotated:alt-1" [a "tptp92-ast:name:alt-2" [a "tptp92-ast:token:integer" [a "sample"]], a "tptp92-ast:formula-role:alt-1" [a "tptp92-ast:token:lower-word" [a "sample"]], a "tptp92-ast:tpi-formula:alt-1" [a "tptp92-ast:fof-formula:alt-2" [a "tptp92-ast:fof-sequent:alt-1" [a "tptp92-ast:fof-formula-tuple:alt-1", a "tptp92-ast:gentzen-arrow:alt-1", a "tptp92-ast:fof-formula-tuple:alt-1"]]], a "tptp92-ast:annotations:alt-2"]

def nhfLongConnectiveExample : Pattern :=
  a "tptp92-ast:nhf-long-connective:alt-1" [a "tptp92-ast:ntf-connective-name:alt-1" [a "tptp92-ast:def-or-sys-constant:alt-1" [a "tptp92-ast:defined-constant:alt-1" [a "tptp92-ast:defined-functor:alt-1" [a "tptp92-ast:atomic-defined-word:alt-1" [a "tptp92-ast:token:dollar-word" [a "sample"]]]]]]]

theorem empty_file_inhabits_root :
    checkHasType language WellSorted.FreeTypeContext.empty [] emptyFile
      (.base "Tptp92Ast:tptp-file") = true := by
  decide +kernel

theorem empty_file_not_fof_formula :
    checkHasType language WellSorted.FreeTypeContext.empty [] emptyFile
      (.base "Tptp92Ast:fof-formula") = false := by
  decide +kernel

theorem root_list_sort_is_present :
    "Tptp92AstList:tptp92ast-tptp-input" ∈ language.types.map TypeDecl.name := by
  decide +kernel

def theory : Mettapedia.GSLT.GSLT :=
  languageGSLT language
    (ReductionRespectsEquations.of_no_equations rfl)

theorem theory_no_step (source target : Pattern) :
    ¬ theory.Step source target := by
  intro reduction
  change langReducesUsing RelationEnv.empty language source target at reduction
  unfold langReducesUsing at reduction
  rcases reduction with ⟨_, step⟩
  cases step with
  | rule ruleMember =>
      change _ ∈ ([] : List RewriteRule) at ruleMember
      simp at ruleMember

def stepDecision : EffectiveStructure.StepDecision theory where
  decideStep _ _ := false
  correct := by
    intro source target
    simp only [Bool.false_eq_true, false_iff]
    exact theory_no_step source target

def oslf := langOSLF language "Tptp92Ast:tptp-file"

theorem galois :
    GaloisConnection (langDiamond language) (langBox language) :=
  langGalois language

theorem wire_isSome :
    (CanonicalWire.renderLanguage? language).isSome := by
  decide +kernel

def wire : String :=
  (CanonicalWire.renderLanguage? language).getD ""

theorem wire_nonempty : wire ≠ "" := by
  decide +kernel

def writeWire (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path wire

#print axioms language_validate
#print axioms integerTypeDeclaration_mem_language
#print axioms sourceSpanRule_shape
#print axioms sourceSpanRule_mem_language
#print axioms annotatedInputRule_shape
#print axioms annotatedInputRule_mem_language
#print axioms includeInputRule_shape
#print axioms includeInputRule_mem_language
#print axioms empty_file_inhabits_root
#print axioms empty_file_not_fof_formula
#print axioms root_list_sort_is_present
#print axioms theory_no_step
#print axioms galois
#print axioms wire_isSome

end Mettapedia.GSLT.LanguageDef.TptpOfficialAbstractSyntax
