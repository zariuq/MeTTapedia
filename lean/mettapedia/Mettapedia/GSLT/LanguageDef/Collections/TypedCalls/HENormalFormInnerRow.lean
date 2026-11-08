import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedCurrentReads
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ValueRows

/-!
# Per-node structural acceptance is not source normality

Both constructor nodes pass structural inference separately. The parent's
first argument typing nevertheless fixes the inner expression at its explicit
CompletionFoo annotation; evaluating that expression at the retained instance
rejects its constructor's CompletionW result. The source interpreter and the
current occurrence-scoped structural reader are used directly.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HENormalFormInnerRow

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open HETypedRuleControls (answersWith arrowAtom)
open NativeTypeCallGraph

def listType (type : Atom) : Atom := .expression [.symbol "CompletionList", type]
def child : Atom := .expression [.symbol "CompletionWrap", .grounded (.int 1)]
def parent : Atom := .expression [.symbol "CompletionCons", child, .symbol "CompletionNil"]

def space (annotated : Bool) : Space := Space.ofList
  ([.expression [.symbol ":", .symbol "CompletionNil", listType (.var "a")],
    .expression [.symbol ":", .symbol "CompletionWrap", arrowAtom [.symbol "Number", .symbol "CompletionW"]]] ++
   (if annotated then [.expression [.symbol ":", child, .symbol "CompletionFoo"]] else []) ++
   [.expression [.symbol ":", .symbol "CompletionCons", arrowAtom [.var "a", listType (.var "a"), listType (.var "a")]]])

def sourceError : Atom := .expression [.symbol "Error", child,
  .expression [.symbol "BadType", .symbol "CompletionFoo", .symbol "CompletionW"]]

def structural (annotated : Bool) (value : Atom) : Option (List Atom) :=
  NativeTypeRecursiveDriver.publishTypes
    (NativeTypeScopedReads.evaluate HEDemandedCurrentReads.ops (HEDemandedConstructorEdge.packet (space annotated))
      HEDemandedConstructorInferred.world 8 (.infer false value) ⟨[], 0⟩).1

set_option maxHeartbeats 1600000 in
theorem child_structural_accepts : structural true child = some [.symbol "CompletionW"] := by cbv

set_option maxHeartbeats 1600000 in
theorem parent_structural_accepts : structural true parent = some [listType (.symbol "CompletionFoo")] := by cbv

theorem heads_have_no_equations :
    HEConstructorAdmission.headAbsent (space true) "CompletionWrap" = true ∧
    HEConstructorAdmission.headAbsent (space true) "CompletionCons" = true := by decide +kernel

theorem independent_child_execution_succeeds : answersWith (space true) child 24 = [child] := by decide +kernel

theorem parent_source_rejects :
    answersWith (space true) parent 24 = [sourceError] ∧
    answersWith (space true) parent 40 = [sourceError] := by
  constructor <;> decide +kernel

theorem without_annotation_succeeds : answersWith (space false) parent 24 = [parent] := by decide +kernel

theorem independent_checks_do_not_certify_source_normality :
    structural true child = some [.symbol "CompletionW"] ∧
    structural true parent = some [listType (.symbol "CompletionFoo")] ∧
    answersWith (space true) parent 24 ≠ [parent] := by
  refine ⟨child_structural_accepts, parent_structural_accepts, ?_⟩
  rw [parent_source_rejects.1]
  decide +kernel

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HENormalFormInnerRow
