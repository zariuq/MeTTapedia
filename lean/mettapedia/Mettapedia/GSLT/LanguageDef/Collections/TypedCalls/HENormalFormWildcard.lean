import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HENormalFormInnerRow

/-!
# Nested wildcard boundary of normal-form admission

The source HE matcher and the scoped model's ordinary matcher reject nested
Undefined mismatches in either direction, while the top-level Undefined
case remains accepted. The native normal-form probes accept the two nested
cases, so this records a native matcher/admission gap rather than certifying
that consumer from the model's correct behaviour.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HENormalFormWildcard

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open HETypedRuleControls (answersWith arrowAtom)

def box (type : Atom) : Atom := .expression [.symbol "CompletionBox", type]
def number : Atom := .symbol "Number"
def operand : Atom := .symbol "CompletionOperand"
def call : Atom := .expression [.symbol "CompletionStrict", operand]
def resultType : Atom := .symbol "CompletionResult"

def space (actual formal : Atom) : Space := Space.ofList
  [.expression [.symbol ":", operand, actual],
   .expression [.symbol ":", .symbol "CompletionStrict", arrowAtom [formal, resultType]]]

def error (actual formal : Atom) : Atom := .expression [.symbol "Error", call,
  .expression [.symbol "BadArgType", .grounded (.int 1), formal, actual]]

def structural (actual formal : Atom) : Option (List Atom) :=
  NativeTypeRecursiveDriver.publishTypes
    (NativeTypeScopedReads.evaluate HEDemandedCurrentReads.ops
      (HEDemandedConstructorEdge.packet (space actual formal)) HEDemandedConstructorInferred.world 8
      (.infer false call) ⟨[], 0⟩).1

theorem source_rejects_nested_actual :
    answersWith (space (box Atom.undefinedType) (box number)) call 24 =
      [error (box Atom.undefinedType) (box number)] := by decide +kernel

theorem source_rejects_nested_formal :
    answersWith (space (box number) (box Atom.undefinedType)) call 24 =
      [error (box number) (box Atom.undefinedType)] := by decide +kernel

theorem source_accepts_top_undefined :
    answersWith (space Atom.undefinedType (box number)) call 24 = [call] := by decide +kernel

set_option maxHeartbeats 1600000 in
theorem scoped_model_rejects_nested_actual :
    structural (box Atom.undefinedType) (box number) = some [] := by cbv

set_option maxHeartbeats 1600000 in
theorem scoped_model_rejects_nested_formal :
    structural (box number) (box Atom.undefinedType) = some [] := by cbv

set_option maxHeartbeats 1600000 in
theorem scoped_model_accepts_top_undefined :
    structural Atom.undefinedType (box number) = some [resultType] := by cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HENormalFormWildcard
