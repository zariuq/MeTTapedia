import Mettapedia.GSLT.LanguageDef.TypedRootPremiseAssignment
import Mettapedia.GSLT.Examples.TypedPremiseOutput
import Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution

/-!
# An open authored premise output through the typed assignment fold

The equality premise of the authored rule produces `Y` from the ambient
variable held by `X`. The executable fold retains that variable in both
contextual values. This instance exercises the general typed fold theorem.
-/

namespace Mettapedia.GSLT.Examples.TypedRootPremiseAssignment

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)
open Mettapedia.GSLT.LanguageDef.RestAwareTyping
open Mettapedia.GSLT.Examples.TypedPremiseOutput
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.Engine

set_option autoImplicit false

private abbrev term : TypeExpr := .base "Term"
private abbrev free : FreeTypeContext :=
  FreeTypeContext.ofList sortedPremiseRule.typeContext
private def spec : RuleBindingSpec :=
  { dependencies := [("X", []), ("Y", [])] }
private def initial : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment :=
  [("X", { dependencies := [], ambient := 1, body := .bvar 0 })]
private def raw : Mettapedia.OSLF.MeTTaIL.Match.Bindings :=
  [("Y", .bvar 0), ("X", .bvar 0)]
private def completed : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment :=
  [("Y", { dependencies := [], ambient := 1, body := .bvar 0 }),
   ("X", { dependencies := [], ambient := 1, body := .bvar 0 })]

private theorem variable_typed :
    HasType sortedPremiseLanguage free [term] (.bvar 0) term :=
  checkSchemaHasType_sound (by decide +kernel)

theorem initial_typed :
    AssignmentHasTypes sortedPremiseLanguage free spec [term] initial := by
  intro name value member
  simp only [initial, List.mem_singleton] at member
  cases member
  exact ⟨[], term, by decide +kernel, by decide +kernel,
    ⟨rfl, rfl, variable_typed⟩⟩

theorem raw_typed :
    RootOutputsHaveTypes sortedPremiseLanguage free [term] raw := by
  intro name result member
  simp [raw] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  ·
    exact ⟨term, by decide +kernel, variable_typed⟩
  ·
    exact ⟨term, by decide +kernel, variable_typed⟩

theorem actual_fold : extendRoot? spec 1 initial raw = some completed := by
  decide +kernel

theorem completed_typed :
    AssignmentHasTypes sortedPremiseLanguage free spec [term] completed :=
  extendRoot?_preserves_types sortedPremiseLanguage free spec [term]
    initial completed raw initial_typed raw_typed actual_fold

theorem output_keeps_ambient_variable :
    lookup completed "Y" =
      some { dependencies := [], ambient := 1, body := Pattern.bvar 0 } := by
  decide +kernel

/-- The raw output is selected by the actual authored equality premise,
starting with the root projection of the captured `X` value. -/
theorem raw_is_premise_result :
    raw ∈ premiseStepWithEnv RelationEnv.empty sortedPremiseLanguage
      [("X", .bvar 0)]
      (.relationQuery "eq" [.fvar "X", .fvar "Y"]) := by
  decide +kernel

private theorem projected_initial :
    projectRoot? 1 initial = some [("X", Pattern.bvar 0)] := by
  decide +kernel

private theorem only_raw_result :
    premiseStepWithEnv RelationEnv.empty sortedPremiseLanguage
      [("X", Pattern.bvar 0)]
      (.relationQuery "eq" [.fvar "X", .fvar "Y"]) = [raw] := by
  decide +kernel

/-- The ordered root premise interpreter retains the actual result ordinal
and the scoped assignment that the general typing theorem admits. -/
theorem actual_root_event :
    ((PremiseEvent.root 0 0 : PremiseEvent Unit), completed) ∈
      rootResults RelationEnv.empty sortedPremiseLanguage spec 1 0
        (.relationQuery "eq" [.fvar "X", .fvar "Y"]) initial := by
  decide +kernel

/-- This proof uses the selected root event and the premise machine's exact
output list, so the generic event theorem applies to the authored rule. -/
theorem actual_root_event_preserves_types :
    AssignmentHasTypes sortedPremiseLanguage free spec [term] completed := by
  apply rootResults_preserves_types sortedPremiseLanguage free spec [term]
    RelationEnv.empty 0
    (.relationQuery "eq" [.fvar "X", .fvar "Y"])
    initial completed (PremiseEvent.root 0 0 : PremiseEvent Unit)
    initial_typed ?_ actual_root_event
  intro root result projected selected
  change projectRoot? 1 initial = some root at projected
  rw [projected_initial] at projected
  cases Option.some.inj projected
  rw [only_raw_result] at selected
  have resultEq : result = raw := by simpa using selected
  subst result
  exact raw_typed

theorem actual_root_event_has_typed_output :
    ∃ completedAssignment,
      ((PremiseEvent.root 0 0 : PremiseEvent Unit), completedAssignment) ∈
        rootResults RelationEnv.empty sortedPremiseLanguage spec 1 0
          (.relationQuery "eq" [.fvar "X", .fvar "Y"]) initial ∧
      AssignmentHasTypes sortedPremiseLanguage free spec [term]
        completedAssignment ∧
      lookup completedAssignment "Y" =
        some { dependencies := [], ambient := 1, body := Pattern.bvar 0 } := by
  exact ⟨completed, actual_root_event, actual_root_event_preserves_types,
    output_keeps_ambient_variable⟩

private def dependentSpec : RuleBindingSpec :=
  { dependencies := [("X", []), ("Y", [term])] }

/-- A root premise cannot supply a value that requires a local binder it
does not have. Such a value requires a scoped premise occurrence. -/
theorem missing_local_dependency_rejected :
    extendRoot? dependentSpec 1 initial raw = none := by
  decide +kernel

/-- An output referring past the caller's sole ambient variable is rejected
before it can be stored as a contextual value. -/
theorem escaping_output_rejected :
    extendRoot? spec 1 initial [("Y", .bvar 1)] = none := by
  decide +kernel

end Mettapedia.GSLT.Examples.TypedRootPremiseAssignment
