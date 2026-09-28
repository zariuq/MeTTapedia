import Mettapedia.GSLT.LanguageDef.TypedScopedPremiseOccurrence
import Mettapedia.GSLT.Examples.ScopedLamCongExecution

/-!
# Typed occurrence substitution in the executable LamCong premise

The authored premise carries its own lambda binder. Its target occurrence
uses that binder as an argument to the captured contextual value. The sorted
site theorem below checks the same depth and instantiator as execution.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Examples.TypedScopedLamCongOccurrence

open Mettapedia.GSLT.Examples.ScopedLamCongExecution
open Mettapedia.GSLT.LanguageDef.RestAwareTyping
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding

private def term : TypeExpr := localStep.resultType
private def free : FreeTypeContext :=
  FreeTypeContext.ofList lamCongRule.typeContext

private def spec : RuleBindingSpec :=
  lamCongRule.bindings.getD { dependencies := [] }

private def targetRow : MetavariableOccurrence :=
  { «name» := "C", site := .premise 0 0 1,
    path := [], arguments := [.bvar 0] }

private def captured : ContextualValue :=
  { dependencies := [term], ambient := 0, body := .bvar 0 }

theorem authored_step_typed :
    ScopedStepHasType language free [] localStep :=
  checkScopedStep_sound (by decide +kernel)

/-- The premise target occurrence has no inner binders; its complete runtime
depth is one because the authored premise itself supplies the binder. -/
theorem target_occurrence_typed :
    TypedOccurrenceAt language free [term] localStep.target term
      [] targetRow.path targetRow.name := by
  have typed := authored_step_typed.2
  have observed : occurrenceAt? localStep.target targetRow.path =
      some targetRow.name := by decide +kernel
  obtain ⟨locals, address⟩ := typed.occurrenceAt_typed observed
  have depth : 0 = locals.length := by
    have runtime := address.runtimeDepth
    simpa [localStep, targetRow] using Option.some.inj runtime
  have nil : locals = [] := by
    cases locals with
    | nil => rfl
    | cons _ _ => simp at depth
  simpa [localStep, term] using (nil ▸ address)

/-- Admitted authored rows and sorted contextual captures instantiate at the
same site depth used by the conditional executor. -/
theorem authored_target_row_instantiates :
    ∃ result,
      occurrenceDepthAtSite? lamCongRule targetRow.site targetRow.path =
        some 1 ∧
      instantiateValue? captured 0 1 targetRow.arguments = some result ∧
      HasType language free [term] result term := by
  have selected : sitePattern? lamCongRule targetRow.site =
      some localStep.target := by decide +kernel
  have sitePrefix : siteBinderDepth? lamCongRule targetRow.site =
      some localStep.binders.length := by decide +kernel
  have admitted : admittedFor lamCongRule spec = true := by
    decide +kernel
  have member : targetRow ∈ spec.occurrences := by decide +kernel
  have checked : checkStoredRowArguments language free
      ([] ++ localStep.binders) [] spec targetRow = true := by
    decide +kernel
  have declared : dependencies? spec targetRow.name = some [term] := by
    decide +kernel
  have valueTyped : ContextualValueHasType language free [term] []
      term captured := by
    refine ⟨rfl, rfl, ?_⟩
    exact checkSchemaHasType_sound (by decide +kernel)
  simpa [captured, localStep, term] using
    (instantiateTypedScopedRow selected sitePrefix admitted member
      [] target_occurrence_typed checked declared valueTyped)

/-- In this instance the open captured value keeps the lambda variable. -/
theorem target_variable_survives :
    instantiateValue? captured 0 1 targetRow.arguments = some (.bvar 0) ∧
      HasType language free [term] (.bvar 0) term := by
  obtain ⟨result, _, executed, typed⟩ := authored_target_row_instantiates
  have computed : instantiateValue? captured 0 1 targetRow.arguments =
      some (.bvar 0) := by decide +kernel
  have same : result = .bvar 0 :=
    Option.some.inj (executed.symm.trans computed)
  exact ⟨computed, same ▸ typed⟩

/-- A local variable outside the premise's declared binder is not typed. -/
theorem escaping_target_rejected :
    checkScopedStep language free []
      { localStep with target := .bvar 1 } = false := by
  decide +kernel

end Mettapedia.GSLT.Examples.TypedScopedLamCongOccurrence
