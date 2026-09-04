import Mettapedia.GSLT.LanguageDef.IndexedConstructorSignature
import Mettapedia.GSLT.LanguageDef.CarrierWellSorted
import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
import Mettapedia.GSLT.LanguageDef.CanonicalWire

/-!
# Static concrete-syntax migration snapshot for TPTP v9.2.0.0

This inert carrier records a table previously generated from the regular
productions of the TPTP `SyntaxBNF`.  No theorem in this module establishes
that external-source correspondence.  The declarations and validation proofs
below are therefore conditional facts about this static table, not evidence
for a native TPTP parser-generation pipeline.
-/

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialSyntaxTree

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
    "NodeLabel",
    "SyntaxTree"
  ]

private def typesPrefix0 : List TypeDecl := typesChunk0

def types : List TypeDecl := typesPrefix0

set_option maxRecDepth 10000

private def sort_Integer : Fin types.length := ⟨0, by decide⟩
private def sort_NodeLabel : Fin types.length := ⟨1, by decide⟩
private def sort_SyntaxTree : Fin types.length := ⟨2, by decide⟩

private def parameter (name : String) (typeIndex : Fin types.length) :
    IndexedConstructorSignature.Parameter types :=
  { name, typeIndex }

private def constructor (label : String) (categoryIndex : Fin types.length)
    (params : List (IndexedConstructorSignature.Parameter types)) :
    IndexedConstructorSignature.Constructor types :=
  { label, categoryIndex, params }

private def constructorsChunk0 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:codepoint" sort_SyntaxTree [parameter "value" sort_Integer],
    constructor "tptp-cst:cons" sort_SyntaxTree [parameter "first" sort_SyntaxTree, parameter "rest" sort_SyntaxTree],
    constructor "tptp-cst:label-back-quoted" sort_NodeLabel [],
    constructor "tptp-cst:label-defined-word" sort_NodeLabel [],
    constructor "tptp-cst:label-distinct-object" sort_NodeLabel [],
    constructor "tptp-cst:label-integer" sort_NodeLabel [],
    constructor "tptp-cst:label-lower-word" sort_NodeLabel [],
    constructor "tptp-cst:label-rational" sort_NodeLabel [],
    constructor "tptp-cst:label-real" sort_NodeLabel [],
    constructor "tptp-cst:label-single-quoted" sort_NodeLabel [],
    constructor "tptp-cst:label-system-word" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-annotated-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-annotated-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-annotated-formula-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-annotated-formula-4" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-annotated-formula-5" sort_NodeLabel []
  ]

private def constructorsPrefix0 : List (IndexedConstructorSignature.Constructor types) := constructorsChunk0

private def constructorsChunk1 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-annotated-formula-6" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-annotations-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-annotations-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-assignment-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-assoc-connective-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-assoc-connective-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-atom-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-atom-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-atomic-defined-word-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-atomic-system-word-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-atomic-word-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-atomic-word-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-atomic-word-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-cnf-annotated-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-cnf-disjunction-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-cnf-disjunction-2" sort_NodeLabel []
  ]

private def constructorsPrefix1 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix0 ++ constructorsChunk1

private def constructorsChunk2 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-cnf-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-cnf-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-cnf-literal-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-cnf-literal-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-cnf-literal-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-cnf-literal-4" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-cnf-literal-corpus-parenthesized" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-comma-fof-logic-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-comma-general-term-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-comma-parent-info-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-comma-tff-term-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-comma-thf-logic-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-constant-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-creator-name-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-creator-source-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-dag-source-1" sort_NodeLabel []
  ]

private def constructorsPrefix2 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix1 ++ constructorsChunk2

private def constructorsChunk3 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-dag-source-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-def-or-sys-constant-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-def-or-sys-constant-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-defined-constant-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-defined-functor-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-defined-infix-pred-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-defined-term-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-defined-term-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-defined-type-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-external-source-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-external-source-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-external-source-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-file-info-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-file-info-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-file-name-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-file-source-1" sort_NodeLabel []
  ]

private def constructorsPrefix3 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix2 ++ constructorsChunk3

private def constructorsChunk4 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-fof-and-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-and-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-annotated-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-arguments-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-arguments-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-atomic-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-atomic-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-atomic-formula-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-binary-assoc-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-binary-assoc-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-binary-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-binary-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-binary-nonassoc-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-defined-atomic-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-defined-atomic-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-defined-atomic-term-1" sort_NodeLabel []
  ]

private def constructorsPrefix4 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix3 ++ constructorsChunk4

private def constructorsChunk5 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-fof-defined-infix-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-defined-plain-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-defined-plain-term-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-defined-plain-term-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-defined-term-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-defined-term-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-formula-tuple-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-formula-tuple-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-formula-tuple-list-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-function-term-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-function-term-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-function-term-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-infix-unary-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-logic-formula-1" sort_NodeLabel []
  ]

private def constructorsPrefix5 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix4 ++ constructorsChunk5

private def constructorsChunk6 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-fof-logic-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-logic-formula-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-or-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-or-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-plain-atomic-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-plain-term-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-plain-term-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-quantified-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-quantifier-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-quantifier-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-sequent-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-sequent-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-system-atomic-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-system-term-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-system-term-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-term-1" sort_NodeLabel []
  ]

private def constructorsPrefix6 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix5 ++ constructorsChunk6

private def constructorsChunk7 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-fof-term-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-unary-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-unary-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-unit-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-unit-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-unitary-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-unitary-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-unitary-formula-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-variable-list-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-fof-variable-list-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-formula-data-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-formula-data-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-formula-data-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-formula-data-4" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-formula-data-5" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-formula-role-1" sort_NodeLabel []
  ]

private def constructorsPrefix7 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix6 ++ constructorsChunk7

private def constructorsChunk8 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-formula-role-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-formula-selection-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-formula-selection-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-functor-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-general-data-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-general-data-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-general-data-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-general-data-4" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-general-data-5" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-general-data-6" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-general-function-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-general-list-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-general-list-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-general-term-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-general-term-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-general-term-3" sort_NodeLabel []
  ]

private def constructorsPrefix8 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix7 ++ constructorsChunk8

private def constructorsChunk9 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-general-terms-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-gentzen-arrow-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-identical-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-include-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-include-optionals-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-include-optionals-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-include-optionals-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-inference-record-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-inference-rule-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-infix-equality-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-infix-inequality-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-internal-source-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-intro-type-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-name-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-name-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-name-list-1" sort_NodeLabel []
  ]

private def constructorsPrefix9 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix8 ++ constructorsChunk9

private def constructorsChunk10 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-name-list-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-nhf-key-pair-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-nhf-long-connective-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-nhf-long-connective-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-nhf-parameter-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-nhf-parameter-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-nhf-parameter-list-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-nhf-parameter-list-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-nonassoc-connective-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-nonassoc-connective-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-nonassoc-connective-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-nonassoc-connective-4" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-nonassoc-connective-5" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-nonassoc-connective-6" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-nothing-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-ntf-connective-name-1" sort_NodeLabel []
  ]

private def constructorsPrefix10 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix9 ++ constructorsChunk10

private def constructorsChunk11 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-ntf-index-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-ntf-short-connective-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-ntf-short-connective-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-ntf-short-connective-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-ntf-short-connective-4" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-number-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-number-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-number-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-nxf-atom-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-nxf-key-pair-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-nxf-long-connective-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-nxf-long-connective-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-nxf-parameter-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-nxf-parameter-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-nxf-parameter-list-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-nxf-parameter-list-2" sort_NodeLabel []
  ]

private def constructorsPrefix11 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix10 ++ constructorsChunk11

private def constructorsChunk12 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-optional-info-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-optional-info-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-parent-details-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-parent-details-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-parent-info-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-parent-list-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-parents-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-parents-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-source-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-source-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-source-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-source-4" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-source-5" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-sources-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-sources-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-space-name-1" sort_NodeLabel []
  ]

private def constructorsPrefix12 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix11 ++ constructorsChunk12

private def constructorsChunk13 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-subtype-sign-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-system-constant-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-system-functor-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tcf-annotated-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tcf-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tcf-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tcf-logic-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tcf-logic-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tcf-quantified-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tf1-quantified-type-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-and-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-and-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-annotated-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-arguments-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-atom-typing-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-atom-typing-2" sort_NodeLabel []
  ]

private def constructorsPrefix13 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix12 ++ constructorsChunk13

private def constructorsChunk14 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-tff-atom-typing-list-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-atom-typing-list-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-atomic-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-atomic-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-atomic-formula-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-atomic-type-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-atomic-type-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-atomic-type-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-atomic-type-4" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-atomic-type-5" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-atomic-type-6" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-binary-assoc-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-binary-assoc-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-binary-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-binary-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-binary-nonassoc-1" sort_NodeLabel []
  ]

private def constructorsPrefix14 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix13 ++ constructorsChunk14

private def constructorsChunk15 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-tff-defined-atomic-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-defined-infix-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-defined-plain-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-defined-plain-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-defined-plain-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-defined-plain-4" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-formula-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-infix-unary-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-logic-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-logic-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-logic-formula-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-logic-formula-4" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-logic-formula-5" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-logic-formula-6" sort_NodeLabel []
  ]

private def constructorsPrefix15 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix14 ++ constructorsChunk15

private def constructorsChunk16 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-tff-mapping-type-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-monotype-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-monotype-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-monotype-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-non-atomic-type-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-non-atomic-type-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-non-atomic-type-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-or-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-or-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-plain-atomic-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-plain-atomic-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-prefix-unary-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-preunit-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-preunit-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-quantified-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-quantifier-1" sort_NodeLabel []
  ]

private def constructorsPrefix16 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix15 ++ constructorsChunk16

private def constructorsChunk17 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-tff-quantifier-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-subtype-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-system-atomic-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-system-atomic-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-term-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-term-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-term-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-top-level-type-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-top-level-type-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-type-arguments-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-type-arguments-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-type-list-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-type-list-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-typed-variable-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-unary-connective-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-unary-connective-2" sort_NodeLabel []
  ]

private def constructorsPrefix17 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix16 ++ constructorsChunk17

private def constructorsChunk18 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-tff-unary-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-unary-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-unit-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-unit-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-unit-formula-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-unitary-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-unitary-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-unitary-formula-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-unitary-formula-4" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-unitary-term-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-unitary-term-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-unitary-term-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-unitary-term-4" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-unitary-term-5" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-unitary-type-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-unitary-type-2" sort_NodeLabel []
  ]

private def constructorsPrefix18 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix17 ++ constructorsChunk18

private def constructorsChunk19 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-tff-variable-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-variable-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-variable-list-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-variable-list-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-xprod-type-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tff-xprod-type-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-th0-quantifier-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-th0-quantifier-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-th0-quantifier-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-th1-defined-term-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-th1-defined-term-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-th1-defined-term-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-th1-defined-term-4" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-th1-defined-term-5" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-theory-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-theory-name-1" sort_NodeLabel []
  ]

private def constructorsPrefix19 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix18 ++ constructorsChunk19

private def constructorsChunk20 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-thf-and-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-and-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-annotated-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-apply-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-apply-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-apply-type-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-arguments-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-atom-typing-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-atom-typing-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-atom-typing-list-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-atom-typing-list-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-atomic-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-atomic-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-atomic-formula-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-atomic-formula-4" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-binary-assoc-1" sort_NodeLabel []
  ]

private def constructorsPrefix20 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix19 ++ constructorsChunk20

private def constructorsChunk21 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-thf-binary-assoc-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-binary-assoc-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-binary-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-binary-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-binary-formula-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-binary-nonassoc-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-binary-type-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-binary-type-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-binary-type-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-conn-term-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-conn-term-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-conn-term-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-conn-term-4" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-conn-term-5" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-defined-atomic-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-defined-atomic-2" sort_NodeLabel []
  ]

private def constructorsPrefix21 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix20 ++ constructorsChunk21

private def constructorsChunk22 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-thf-defined-atomic-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-defined-atomic-4" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-defined-atomic-5" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-defined-infix-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-defined-term-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-defined-term-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-definition-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-fof-function-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-fof-function-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-fof-function-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-formula-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-formula-list-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-infix-unary-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-let-1" sort_NodeLabel []
  ]

private def constructorsPrefix22 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix21 ++ constructorsChunk22

private def constructorsChunk23 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-thf-let-defn-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-let-defn-list-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-let-defn-list-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-let-defns-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-let-defns-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-let-types-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-let-types-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-logic-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-logic-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-logic-formula-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-logic-formula-4" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-logic-formula-5" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-logic-formula-6" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-mapping-type-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-mapping-type-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-or-formula-1" sort_NodeLabel []
  ]

private def constructorsPrefix23 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix22 ++ constructorsChunk23

private def constructorsChunk24 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-thf-or-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-plain-atomic-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-plain-atomic-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-prefix-unary-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-preunit-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-preunit-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-quantification-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-quantified-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-quantifier-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-quantifier-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-quantifier-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-sequent-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-subtype-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-system-atomic-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-top-level-type-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-top-level-type-2" sort_NodeLabel []
  ]

private def constructorsPrefix24 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix23 ++ constructorsChunk24

private def constructorsChunk25 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-thf-top-level-type-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-tuple-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-tuple-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-typed-variable-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-unary-connective-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-unary-connective-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-unary-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-unary-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-union-type-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-union-type-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-unit-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-unit-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-unit-formula-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-unitary-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-unitary-formula-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-unitary-formula-3" sort_NodeLabel []
  ]

private def constructorsPrefix25 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix24 ++ constructorsChunk25

private def constructorsChunk26 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-thf-unitary-formula-4" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-unitary-term-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-unitary-term-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-unitary-term-3" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-unitary-type-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-variable-list-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-variable-list-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-xprod-type-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-thf-xprod-type-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tpi-annotated-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tpi-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tptp-file-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tptp-input-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-tptp-input-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-txf-definition-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-txf-let-1" sort_NodeLabel []
  ]

private def constructorsPrefix26 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix25 ++ constructorsChunk26

private def constructorsChunk27 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-txf-let-defn-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-txf-let-defn-list-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-txf-let-defn-list-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-txf-let-defns-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-txf-let-defns-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-txf-let-lhs-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-txf-let-lhs-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-txf-let-types-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-txf-let-types-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-txf-sequent-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-txf-tuple-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-txf-tuple-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-txf-tuple-type-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-txf-unitary-formula-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-type-constant-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-type-functor-1" sort_NodeLabel []
  ]

private def constructorsPrefix27 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix26 ++ constructorsChunk27

private def constructorsChunk28 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-alt-type-quantifier-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-type-quantifier-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-unary-connective-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-untyped-atom-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-untyped-atom-2" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-useful-info-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-alt-variable-1" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-annotated-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-annotations" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-assignment" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-assoc-connective" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-atom" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-atomic-defined-word" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-atomic-system-word" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-atomic-word" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-cnf-annotated" sort_NodeLabel []
  ]

private def constructorsPrefix28 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix27 ++ constructorsChunk28

private def constructorsChunk29 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-cnf-disjunction" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-cnf-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-cnf-literal" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-comma-fof-logic-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-comma-general-term" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-comma-parent-info" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-comma-tff-term" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-comma-thf-logic-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-constant" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-creator-name" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-creator-source" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-dag-source" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-def-or-sys-constant" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-defined-constant" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-defined-functor" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-defined-infix-pred" sort_NodeLabel []
  ]

private def constructorsPrefix29 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix28 ++ constructorsChunk29

private def constructorsChunk30 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-defined-term" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-defined-type" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-external-source" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-file-info" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-file-name" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-file-source" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-and-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-annotated" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-arguments" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-atomic-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-binary-assoc" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-binary-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-binary-nonassoc" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-defined-atomic-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-defined-atomic-term" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-defined-infix-formula" sort_NodeLabel []
  ]

private def constructorsPrefix30 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix29 ++ constructorsChunk30

private def constructorsChunk31 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-fof-defined-plain-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-defined-plain-term" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-defined-term" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-formula-tuple" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-formula-tuple-list" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-function-term" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-infix-unary" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-logic-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-or-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-plain-atomic-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-plain-term" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-quantified-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-quantifier" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-sequent" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-system-atomic-formula" sort_NodeLabel []
  ]

private def constructorsPrefix31 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix30 ++ constructorsChunk31

private def constructorsChunk32 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-fof-system-term" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-term" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-unary-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-unit-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-unitary-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-fof-variable-list" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-formula-data" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-formula-role" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-formula-selection" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-functor" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-general-data" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-general-function" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-general-list" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-general-term" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-general-terms" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-gentzen-arrow" sort_NodeLabel []
  ]

private def constructorsPrefix32 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix31 ++ constructorsChunk32

private def constructorsChunk33 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-identical" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-include" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-include-optionals" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-inference-record" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-inference-rule" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-infix-equality" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-infix-inequality" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-internal-source" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-intro-type" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-name" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-name-list" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-nhf-key-pair" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-nhf-long-connective" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-nhf-parameter" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-nhf-parameter-list" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-nonassoc-connective" sort_NodeLabel []
  ]

private def constructorsPrefix33 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix32 ++ constructorsChunk33

private def constructorsChunk34 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-nothing" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-ntf-connective-name" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-ntf-index" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-ntf-short-connective" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-number" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-nxf-atom" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-nxf-key-pair" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-nxf-long-connective" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-nxf-parameter" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-nxf-parameter-list" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-optional-info" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-parent-details" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-parent-info" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-parent-list" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-parents" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-source" sort_NodeLabel []
  ]

private def constructorsPrefix34 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix33 ++ constructorsChunk34

private def constructorsChunk35 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-sources" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-space-name" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-subtype-sign" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-system-constant" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-system-functor" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tcf-annotated" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tcf-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tcf-logic-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tcf-quantified-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tf1-quantified-type" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-and-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-annotated" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-arguments" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-atom-typing" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-atom-typing-list" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-atomic-formula" sort_NodeLabel []
  ]

private def constructorsPrefix35 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix34 ++ constructorsChunk35

private def constructorsChunk36 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-tff-atomic-type" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-binary-assoc" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-binary-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-binary-nonassoc" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-defined-atomic" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-defined-infix" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-defined-plain" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-infix-unary" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-logic-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-mapping-type" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-monotype" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-non-atomic-type" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-or-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-plain-atomic" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-prefix-unary" sort_NodeLabel []
  ]

private def constructorsPrefix36 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix35 ++ constructorsChunk36

private def constructorsChunk37 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-tff-preunit-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-quantified-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-quantifier" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-subtype" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-system-atomic" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-term" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-top-level-type" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-type-arguments" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-type-list" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-typed-variable" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-unary-connective" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-unary-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-unit-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-unitary-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-unitary-term" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-unitary-type" sort_NodeLabel []
  ]

private def constructorsPrefix37 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix36 ++ constructorsChunk37

private def constructorsChunk38 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-tff-variable" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-variable-list" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tff-xprod-type" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-th0-quantifier" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-th1-defined-term" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-theory" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-theory-name" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-and-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-annotated" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-apply-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-apply-type" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-arguments" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-atom-typing" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-atom-typing-list" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-atomic-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-binary-assoc" sort_NodeLabel []
  ]

private def constructorsPrefix38 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix37 ++ constructorsChunk38

private def constructorsChunk39 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-thf-binary-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-binary-nonassoc" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-binary-type" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-conn-term" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-defined-atomic" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-defined-infix" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-defined-term" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-definition" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-fof-function" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-formula-list" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-infix-unary" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-let" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-let-defn" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-let-defn-list" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-let-defns" sort_NodeLabel []
  ]

private def constructorsPrefix39 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix38 ++ constructorsChunk39

private def constructorsChunk40 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-thf-let-types" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-logic-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-mapping-type" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-or-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-plain-atomic" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-prefix-unary" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-preunit-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-quantification" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-quantified-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-quantifier" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-sequent" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-subtype" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-system-atomic" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-top-level-type" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-tuple" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-typed-variable" sort_NodeLabel []
  ]

private def constructorsPrefix40 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix39 ++ constructorsChunk40

private def constructorsChunk41 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-thf-unary-connective" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-unary-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-union-type" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-unit-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-unitary-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-unitary-term" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-unitary-type" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-variable-list" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-thf-xprod-type" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tpi-annotated" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tpi-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tptp-file" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-tptp-input" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-txf-definition" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-txf-let" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-txf-let-defn" sort_NodeLabel []
  ]

private def constructorsPrefix41 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix40 ++ constructorsChunk41

private def constructorsChunk42 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:label-tptp92-txf-let-defn-list" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-txf-let-defns" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-txf-let-lhs" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-txf-let-types" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-txf-sequent" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-txf-tuple" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-txf-tuple-type" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-txf-unitary-formula" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-type-constant" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-type-functor" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-type-quantifier" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-unary-connective" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-untyped-atom" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-useful-info" sort_NodeLabel [],
    constructor "tptp-cst:label-tptp92-variable" sort_NodeLabel [],
    constructor "tptp-cst:label-upper-word" sort_NodeLabel []
  ]

private def constructorsPrefix42 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix41 ++ constructorsChunk42

private def constructorsChunk43 : List (IndexedConstructorSignature.Constructor types) := [
    constructor "tptp-cst:nil" sort_SyntaxTree [],
    constructor "tptp-cst:node" sort_SyntaxTree [parameter "label" sort_NodeLabel, parameter "payload" sort_SyntaxTree],
    constructor "tptp-cst:none" sort_SyntaxTree [],
    constructor "tptp-cst:pair" sort_SyntaxTree [parameter "left" sort_SyntaxTree, parameter "right" sort_SyntaxTree],
    constructor "tptp-cst:some" sort_SyntaxTree [parameter "value" sort_SyntaxTree],
    constructor "tptp-cst:spanned-node" sort_SyntaxTree [parameter "label" sort_NodeLabel, parameter "start" sort_Integer, parameter "stop" sort_Integer, parameter "payload" sort_SyntaxTree]
  ]

private def constructorsPrefix43 : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix42 ++ constructorsChunk43

def constructors : List (IndexedConstructorSignature.Constructor types) := constructorsPrefix43

def language : LanguageDef :=
  IndexedConstructorSignature.language
    "TptpOfficialSyntaxTreeV9200" types constructors

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
    "TptpOfficialSyntaxTreeV9200" types constructors
    typesNodup constructorsNodup

theorem language_inventory :
    language.types.length = 3 ∧
      language.terms.length = 694 ∧
      language.rewrites.length = 0 := by
  decide

def emptyFile : Pattern :=
  a "tptp-cst:node" [
    a "tptp-cst:label-tptp92-tptp-file",
    a "tptp-cst:node" [
      a "tptp-cst:label-tptp92-alt-tptp-file-1",
      a "tptp-cst:nil"]]

theorem empty_file_inhabits_syntax_tree :
    checkHasType language WellSorted.FreeTypeContext.empty [] emptyFile
      (.base "SyntaxTree") = true := by
  decide +kernel

def unknownAlternative : Pattern :=
  a "tptp-cst:node" [
    a "tptp-cst:label-tptp92-alt-unknown-1",
    a "tptp-cst:nil"]

theorem unknown_alternative_is_rejected :
    checkHasType language WellSorted.FreeTypeContext.empty [] unknownAlternative
      (.base "SyntaxTree") = false := by
  decide +kernel

def theory : Mettapedia.GSLT.GSLT :=
  languageGSLT language
    (ReductionRespectsEquations.of_equation_free rfl)

theorem theory_no_step (source target : Pattern) :
    ¬ theory.Step source target := by
  intro reduction
  unfold theory at reduction
  rw [languageGSLT_step] at reduction
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

def oslf := langOSLF language "SyntaxTree"

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
#print axioms empty_file_inhabits_syntax_tree
#print axioms unknown_alternative_is_rejected
#print axioms theory_no_step
#print axioms galois
#print axioms wire_isSome

end Mettapedia.GSLT.LanguageDef.TptpOfficialSyntaxTree
