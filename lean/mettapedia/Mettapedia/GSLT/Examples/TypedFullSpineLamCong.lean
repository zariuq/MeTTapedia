import Mettapedia.GSLT.LanguageDef.TypedFullSpineStepResults
import Mettapedia.GSLT.Examples.TypedScopedLamCongOccurrence

/-!
# Typed capture at the authored LamCong premise

The actual local-step target occurrence supplies its own binder to `C`.
The executable matcher recovers an open bound variable without treating it as
an unbound ambient variable. The declaration, sorted judgment and runtime
capture are checked against the same occurrence site.
-/

namespace Mettapedia.GSLT.Examples.TypedFullSpineLamCong

open Mettapedia.GSLT.Examples.ScopedLamCongExecution
open Mettapedia.GSLT.LanguageDef.RestAwareTyping
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution

set_option autoImplicit false

private def term : TypeExpr := localStep.resultType
private def free : FreeTypeContext :=
  FreeTypeContext.ofList lamCongRule.typeContext
private def spec : RuleBindingSpec :=
  lamCongRule.bindings.getD { dependencies := [] }
private def captured : ContextualValue :=
  { dependencies := [term], ambient := 0, body := .bvar 0 }
private def capturedB : ContextualValue :=
  { dependencies := [term], ambient := 0, body := openRedex }
private def initialB : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment :=
  [("B", capturedB)]
private def completed : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment :=
  [("C", captured), ("B", capturedB)]

private theorem open_target_typed :
    HasType language free [term] (.bvar 0) term := by
  exact .bvar (by decide +kernel)

/-- The premise target row is the full local-binder spine selected by the
authored rule; its depth and dependency sort are both one `Term`. -/
theorem authored_target_full_spine :
    dependencies? spec "C" = some [term] ∧
    arguments? lamCongRule spec "C" (.premise 0 0 1) [] =
      some (fullSpine 1) ∧
    occurrenceDepthAtSite? lamCongRule (.premise 0 0 1) [] = some 1 := by
  decide +kernel

/-- The typed full-spine theorem applies to the open output of the actual
local step, retaining the premise binder as a dependency of `C`. -/
theorem open_target_recovered_and_typed :
    recoverValue? [term] 0 1 [.bvar 0] (.bvar 0) = some captured ∧
    ContextualValueHasType language free [term] [] term captured := by
  obtain ⟨value, recovered, typed⟩ :=
    recoverValue?_fullSpine_typed language free [term] [] (.bvar 0)
      term open_target_typed
  have exactValue : value = captured := by
    have computed : recoverValue? [term] 0 1 [.bvar 0] (.bvar 0) =
        some captured := by
      simpa [fullSpine, captured] using
        (recoverValue?_fullSpine [term] [] (.bvar 0)
          (by decide +kernel))
    exact Option.some.inj (recovered.symm.trans computed)
  subst value
  simpa [fullSpine] using And.intro recovered typed

/-- Runtime `capture?` selects the same typed contextual value. The
assignment stores its declared dependency and result sort rather than an
inferred first-occurrence depth. -/
theorem authored_target_capture_typed :
    capture? lamCongRule spec 0 1 (.premise 0 0 1) [] [] "C" (.bvar 0) =
      some [("C", captured)] ∧
    AssignmentHasTypes language free spec [] [("C", captured)] := by
  obtain ⟨declared, spine, _⟩ := authored_target_full_spine
  obtain ⟨executed, typed⟩ :=
    capture?_fullSpine_fresh language free lamCongRule spec [] [term]
      (.premise 0 0 1) [] [] "C" (.bvar 0) term declared spine rfl
      open_target_typed
  constructor
  · simpa [captured] using executed
  · unfold AssignmentHasTypes
    intro capturedName capturedValue membership
    have pairEq : (capturedName, capturedValue) = ("C", captured) := by
      simpa using membership
    obtain ⟨nameEq, valueEq⟩ := Prod.mk.inj pairEq
    subst capturedName
    subst capturedValue
    exact ⟨[term], term, declared, by decide +kernel,
      by simpa [captured] using typed⟩

/-- A local result referring to a second, undeclared binder is rejected by
the same capture path. It cannot acquire a typing witness for this rule. -/
theorem escaping_target_capture_rejected :
    capture? lamCongRule spec 0 1 (.premise 0 0 1) [] [] "C" (.bvar 1) =
      none := by
  decide +kernel

/-- The left occurrence of `B` and the source of the scoped premise pass
the same complete binder spine. -/
theorem authored_source_full_spine :
    dependencies? spec "B" = some [term] ∧
    arguments? lamCongRule spec "B" (.premise 0 0 0) [] =
      some (fullSpine 1) ∧
    occurrenceDepthAtSite? lamCongRule (.premise 0 0 0) [] = some 1 := by
  decide +kernel

/-- The first value really comes from matching the authored LamCong left
side against the running open beta redex. -/
theorem authored_left_match :
    matchRuleAt lamCongRule spec 0 wrappedRedex = [initialB] := by
  decide +kernel

private theorem open_source_typed :
    HasType language free [term] openRedex term :=
  checkSchemaHasType_sound (by decide +kernel)

theorem initial_B_assignment_typed :
    AssignmentHasTypes language free spec [] initialB := by
  unfold AssignmentHasTypes
  intro capturedName capturedValue membership
  have pairEq : (capturedName, capturedValue) = ("B", capturedB) := by
    simpa [initialB] using membership
  obtain ⟨nameEq, valueEq⟩ := Prod.mk.inj pairEq
  subst capturedName
  subst capturedValue
  exact ⟨[term], term, by decide +kernel, by decide +kernel,
    ⟨rfl, rfl, open_source_typed⟩⟩

/-- Checking `B` again inside the scoped premise leaves the original typed
assignment in place. No new capture is added for the repeated occurrence. -/
theorem authored_repeated_source_preserves_typed :
    capture? lamCongRule spec 0 1 (.premise 0 0 0) [] initialB
      "B" openRedex = some initialB ∧
    AssignmentHasTypes language free spec [] initialB := by
  obtain ⟨declared, spine, _⟩ := authored_source_full_spine
  constructor
  · apply capture?_fullSpine_repeat lamCongRule spec [] [term]
      (.premise 0 0 0) [] initialB "B" openRedex declared spine
    · simpa using open_source_typed.forget.isWellScopedAt
    · decide +kernel
  · exact initial_B_assignment_typed

/-- A different, still locally scoped source cannot overwrite the value
captured from the left side. -/
theorem authored_repeated_source_conflict :
    capture? lamCongRule spec 0 1 (.premise 0 0 0) [] initialB
      "B" (.bvar 0) = none := by
  obtain ⟨declared, spine, _⟩ := authored_source_full_spine
  apply capture?_fullSpine_conflict lamCongRule spec [] [term]
    (.premise 0 0 0) [] initialB "B" (.bvar 0) capturedB
    declared spine
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- The actual ordered premise executor consumes the left-side `B` capture,
selects beta at oracle ordinal zero, and appends the scoped `C` output. -/
theorem authored_scoped_step_exact :
    stepResults betaOracle lamCongRule spec 0 0 1
      localStep.source localStep.target initialB =
      [(.step 0 0 (), completed)] := by
  decide +kernel

/-- Every selected event of the authored step, not only its computed first
entry, satisfies the general binder-local assignment theorem. -/
theorem authored_any_selected_step_typed
    (event : PremiseEvent Unit)
    (final : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (selected : (event, final) ∈ stepResults betaOracle lamCongRule spec
      0 0 1 localStep.source localStep.target initialB) :
    AssignmentHasTypes language free spec [] final := by
  obtain ⟨declared, arguments, _⟩ := authored_target_full_spine
  have sourceResult : instantiateAt? lamCongRule spec 0
      (.premise 0 0 0) [] 1 initialB localStep.source =
        some openRedex := by
    decide +kernel
  have outputs : ∀ evidence candidate,
      (evidence, candidate) ∈ betaOracle 1 openRedex →
      HasType language free [term] candidate term := by
    intro evidence candidate membership
    rw [inner_beta_open] at membership
    have pairEq : (evidence, candidate) = ((), .bvar 0) :=
      List.mem_singleton.mp membership
    obtain ⟨_, candidateEq⟩ := Prod.mk.inj pairEq
    subst candidate
    exact open_target_typed
  exact stepResults_fvar_fullSpine_preserves_types language free
    lamCongRule spec [] [term] 0 localStep.source "C" term betaOracle
    initialB final event openRedex initial_B_assignment_typed declared
    arguments (by decide +kernel) sourceResult outputs
    (by simpa [localStep] using selected)

theorem completed_assignment_typed :
    AssignmentHasTypes language free spec [] completed := by
  unfold AssignmentHasTypes
  intro capturedName capturedValue membership
  have split : (capturedName, capturedValue) = ("C", captured) ∨
      (capturedName, capturedValue) = ("B", capturedB) := by
    simpa [completed] using membership
  rcases split with isC | isB
  · obtain ⟨nameEq, valueEq⟩ := Prod.mk.inj isC
    subst capturedName
    subst capturedValue
    exact ⟨[term], term, by decide +kernel, by decide +kernel,
      open_target_recovered_and_typed.2⟩
  · obtain ⟨nameEq, valueEq⟩ := Prod.mk.inj isB
    subst capturedName
    subst capturedValue
    exact initial_B_assignment_typed "B" capturedB (by simp [initialB])

/-- The selected premise event has a typed completed assignment while
retaining its actual ordinal and the original `B` value. -/
theorem actual_scoped_event_has_typed_assignment :
    ((.step 0 0 (), completed) : PremiseEvent Unit ×
      Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment) ∈
        stepResults betaOracle lamCongRule spec 0 0 1
          localStep.source localStep.target initialB ∧
    AssignmentHasTypes language free spec [] completed ∧
    lookup completed "B" = some capturedB ∧
    lookup completed "C" = some captured := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [authored_scoped_step_exact]
    simp
  · exact authored_any_selected_step_typed (.step 0 0 ()) completed (by
      rw [authored_scoped_step_exact]
      simp)
  · decide +kernel
  · decide +kernel

/-- An oracle result outside the premise binder cannot enter the selected
typed event list. -/
theorem escaping_scoped_event_rejected :
    stepResults escapingOracle lamCongRule spec 0 0 1
      localStep.source localStep.target initialB = [] := by
  decide +kernel

/-- Equal oracle endpoints remain two separately located, typed events.
Typing the completed assignment does not quotient firing multiplicity. -/
theorem duplicate_scoped_events_retained_and_typed :
    stepResults duplicateOracle lamCongRule spec 0 0 1
      localStep.source localStep.target initialB =
        [(.step 0 0 (), completed), (.step 0 1 (), completed)] ∧
    AssignmentHasTypes language free spec [] completed ∧
    (PremiseEvent.step 0 0 () : PremiseEvent Unit) ≠ .step 0 1 () := by
  exact ⟨by decide +kernel, completed_assignment_typed, by decide⟩

end Mettapedia.GSLT.Examples.TypedFullSpineLamCong
