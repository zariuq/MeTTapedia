import Mettapedia.GSLT.Parsing.TptpOfficialCompositionSource
import Mathlib.Tactic

/-!
# Source-connected official TPTP record projection

Compact `tptp-rec:*` values are the public source-shaped result of the official
reader.  This module defines the seven top-level input forms and their exact
physical S-expression codec.  The codec is total in the forward direction and
fail-closed in the reverse direction, so family tags, field order, duplicate
inputs, annotations, include metadata, and spans are reflected rather than
identified by an informal convention.

The final section quotes the live authored CST projection.  It checks the
ordered input fold, all six annotated-formula builders, the include builder,
and representative connective and quantifier clauses.  The native projector
is tested separately against this authored presentation; no C behavior is
assumed by the theorems here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.TptpOfficialRecordProjectionSource

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.Parsing.TptpOfficialCompositionSource (app equation?)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

inductive FormulaFamily where
  | fof
  | cnf
  | tff
  | thf
  | tcf
  | tpi
  deriving DecidableEq, Repr

def FormulaFamily.constructor : FormulaFamily → String
  | .fof => "tptp-rec:fof"
  | .cnf => "tptp-rec:cnf"
  | .tff => "tptp-rec:tff"
  | .thf => "tptp-rec:thf"
  | .tcf => "tptp-rec:tcf"
  | .tpi => "tptp-rec:tpi"

inductive Input where
  | annotated (family : FormulaFamily) (name role formula annotation span : SExpr)
  | includeRecord (path selection qualifier span : SExpr)
  deriving DecidableEq, Repr

structure File where
  inputs : List Input
  span : SExpr
  deriving DecidableEq, Repr

def encodeInput : Input → SExpr
  | .annotated family name role formula annotation span =>
      app family.constructor [name, role, formula, annotation, span]
  | .includeRecord path selection qualifier span =>
      app "tptp-rec:include" [path, selection, qualifier, span]

def decodeInput : SExpr → Option Input
  | .list [.atom "tptp-rec:fof", name, role, formula, annotation, span] =>
      some (.annotated .fof name role formula annotation span)
  | .list [.atom "tptp-rec:cnf", name, role, formula, annotation, span] =>
      some (.annotated .cnf name role formula annotation span)
  | .list [.atom "tptp-rec:tff", name, role, formula, annotation, span] =>
      some (.annotated .tff name role formula annotation span)
  | .list [.atom "tptp-rec:thf", name, role, formula, annotation, span] =>
      some (.annotated .thf name role formula annotation span)
  | .list [.atom "tptp-rec:tcf", name, role, formula, annotation, span] =>
      some (.annotated .tcf name role formula annotation span)
  | .list [.atom "tptp-rec:tpi", name, role, formula, annotation, span] =>
      some (.annotated .tpi name role formula annotation span)
  | .list [.atom "tptp-rec:include", path, selection, qualifier, span] =>
      some (.includeRecord path selection qualifier span)
  | _ => none

def encodeInputs : List Input → SExpr
  | [] => app "tptp-rec:inputs-nil" []
  | input :: tail =>
      app "tptp-rec:inputs-cons" [encodeInput input, encodeInputs tail]

def decodeInputs : SExpr → Option (List Input)
  | .list [.atom "tptp-rec:inputs-nil"] => some []
  | .list [.atom "tptp-rec:inputs-cons", input, tail] => do
      let decodedInput ← decodeInput input
      let decodedTail ← decodeInputs tail
      some (decodedInput :: decodedTail)
  | _ => none
termination_by value => sizeOf value

def encodeFile (file : File) : SExpr :=
  app "tptp-rec:file" [encodeInputs file.inputs, file.span]

def decodeFile : SExpr → Option File
  | .list [.atom "tptp-rec:file", inputs, span] => do
      let decodedInputs ← decodeInputs inputs
      some { inputs := decodedInputs, span }
  | _ => none

@[simp] theorem decodeInput_encodeInput (input : Input) :
    decodeInput (encodeInput input) = some input := by
  cases input with
  | annotated family name role formula annotation span =>
      cases family <;> rfl
  | includeRecord path selection qualifier span => rfl

@[simp] theorem decodeInputs_encodeInputs (inputs : List Input) :
    decodeInputs (encodeInputs inputs) = some inputs := by
  induction inputs with
  | nil => simp [encodeInputs, app, decodeInputs]
  | cons input tail ih =>
      simp [encodeInputs, app, decodeInputs, ih]

@[simp] theorem decodeFile_encodeFile (file : File) :
    decodeFile (encodeFile file) = some file := by
  cases file
  simp [encodeFile, app, decodeFile]

theorem encodeInput_injective : Function.Injective encodeInput := by
  intro first second equal
  have decoded := congrArg decodeInput equal
  simpa using decoded

theorem encodeInputs_injective : Function.Injective encodeInputs := by
  intro first second equal
  have decoded := congrArg decodeInputs equal
  simpa using decoded

theorem encodeFile_injective : Function.Injective encodeFile := by
  intro first second equal
  have decoded := congrArg decodeFile equal
  simpa using decoded

theorem encodeInputs_append (first second : List Input) :
    decodeInputs (encodeInputs (first ++ second)) = some (first ++ second) := by
  simp

theorem duplicate_inputs_preserved (input : Input) :
    decodeInputs (encodeInputs [input, input]) = some [input, input] := by
  simp

theorem wrong_family_arity_rejected (name role formula annotation : SExpr) :
    decodeInput (app "tptp-rec:fof" [name, role, formula, annotation]) = none := rfl

/-! ## Exact authored-source qualification contract -/

def annotatedBuilderLeft (production : String) : SExpr :=
  app "tptp-rec-v1:build"
    [.atom ("\"" ++ production ++ "\""), .atom "?alt", .atom "?start",
     .atom "?stop", .atom "?kids"]

def childNode (name : String) : SExpr :=
  app "tptp-rec-v1:node"
    [app "tptp-rec-v1:child"
      [.atom ("\"" ++ name ++ "\""),
       app "tptp-rec-v1:nodes" [.atom "?kids"]]]

def annotatedBuilderRight (constructor formulaChild : String) : SExpr :=
  app constructor
    [childNode "name", childNode "formula_role", childNode formulaChild,
     childNode "annotations", app "tptp-rec:span" [.atom "?start", .atom "?stop"]]

def AuthoredRecordProjectionSourceExact (recordsSyntax : SExpr) : Prop :=
    equation? recordsSyntax 68 =
      some (app "tptp-rec-v1:inputs" [.atom "LNil"],
        app "tptp-rec:inputs-nil" []) ∧
    equation? recordsSyntax 69 =
      some
        (app "tptp-rec-v1:inputs"
          [app "LCons" [.atom "?head", .atom "?rest"]],
         app "tptp-rec:inputs-cons"
          [app "tptp-rec-v1:node" [.atom "?head"],
           app "tptp-rec-v1:inputs" [.atom "?rest"]]) ∧
    equation? recordsSyntax 84 = some
    (annotatedBuilderLeft "fof_annotated",
     annotatedBuilderRight "tptp-rec:fof" "fof_formula") ∧
    equation? recordsSyntax 85 = some
    (annotatedBuilderLeft "cnf_annotated",
     annotatedBuilderRight "tptp-rec:cnf" "cnf_formula") ∧
    equation? recordsSyntax 86 = some
    (annotatedBuilderLeft "tff_annotated",
     annotatedBuilderRight "tptp-rec:tff" "tff_formula") ∧
    equation? recordsSyntax 87 = some
    (annotatedBuilderLeft "thf_annotated",
     annotatedBuilderRight "tptp-rec:thf" "thf_formula") ∧
    equation? recordsSyntax 88 = some
    (annotatedBuilderLeft "tcf_annotated",
     annotatedBuilderRight "tptp-rec:tcf" "tcf_formula") ∧
    equation? recordsSyntax 89 = some
    (annotatedBuilderLeft "tpi_annotated",
     annotatedBuilderRight "tptp-rec:tpi" "tpi_formula") ∧
    equation? recordsSyntax 83 =
    some
      (app "tptp-rec-v1:build"
        [.atom "\"TPTP_file\"", .atom "?alt", .atom "?start",
         .atom "?stop", .atom "?kids"],
       app "tptp-rec:file"
        [app "tptp-rec-v1:inputs"
          [app "tptp-rec-v1:nodes" [.atom "?kids"]],
         app "tptp-rec:span" [.atom "?start", .atom "?stop"]]) ∧
    equation? recordsSyntax 91 =
    some
      (app "tptp-rec-v1:include-result"
        [.atom "?file",
         app "tptp-rec-v1:include-options-value"
          [.atom "?selection", .atom "?qualification"], .atom "?span"],
       app "tptp-rec:include"
        [.atom "?file", .atom "?selection", .atom "?qualification",
         .atom "?span"]) ∧
    equation? recordsSyntax 49 = some
      (app "tptp-rec-v1:binary"
        [.atom "\"|\"", .atom "?left", .atom "?right"],
       app "tptp-rec:or" [.atom "?left", .atom "?right"]) ∧
    equation? recordsSyntax 58 = some
      (app "tptp-rec-v1:binary"
        [.atom "\"=\"", .atom "?left", .atom "?right"],
       app "tptp-rec:equals" [.atom "?left", .atom "?right"]) ∧
    equation? recordsSyntax 60 = some
      (app "tptp-rec-v1:binary"
        [.atom "\"!=\"", .atom "?left", .atom "?right"],
       app "tptp-rec:not-equals" [.atom "?left", .atom "?right"]) ∧
    equation? recordsSyntax 61 = some
      (app "tptp-rec-v1:quant"
        [.atom "\"!\"", .atom "?vars", .atom "?body"],
       app "tptp-rec:forall" [.atom "?vars", .atom "?body"])

#print axioms decodeInput_encodeInput
#print axioms decodeInputs_encodeInputs
#print axioms decodeFile_encodeFile
#print axioms encodeInput_injective
#print axioms encodeInputs_injective
#print axioms encodeFile_injective
#print axioms duplicate_inputs_preserved
#print axioms wrong_family_arity_rejected

end Mettapedia.GSLT.Parsing.TptpOfficialRecordProjectionSource
