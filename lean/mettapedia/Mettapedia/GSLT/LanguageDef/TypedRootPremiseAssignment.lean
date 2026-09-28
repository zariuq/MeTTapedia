import Mettapedia.GSLT.LanguageDef.TypedScopedPremiseOccurrence
import Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
import Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution

/-!
# Typed assignments after root premise outputs

The root premise adapter may add a value only when it has no local
dependencies. Its body then lives in the caller's ambient context, even when
the premise returns an open pattern. The invariant below records the declared
dependency context and sort of every retained runtime value, including values
captured before the root premise.
-/

namespace Mettapedia.GSLT.LanguageDef.RestAwareTyping

open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.Engine

set_option autoImplicit false

/-- Every stored value carries its authored dependency context, its caller
ambient context, and a typing derivation at the declared result sort. -/
def AssignmentHasTypes (language : LanguageDef) (free : FreeTypeContext)
    (spec : RuleBindingSpec) (ambient : List TypeExpr)
    (assignment : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment) : Prop :=
  ∀ name value, (name, value) ∈ assignment →
    ∃ dependencies resultType,
      dependencies? spec name = some dependencies ∧
      free name = some resultType ∧
      ContextualValueHasType language free dependencies ambient
        resultType value

private theorem rootRecoveryAssignment (ambient : Nat) :
    recoveryAssignment 0 0 ambient [] = Pattern.bvar := by
  funext index
  simp [recoveryAssignment]

private theorem rootOccurrenceAssignment :
    occurrenceAssignment 0 0 [] = Pattern.bvar := by
  funext index
  simp [occurrenceAssignment]

/-- At the root an empty dependency context recovers the exact supplied open
pattern, with its ambient context retained as metadata. -/
theorem recoverValue?_root_empty (ambient : Nat) (target : Pattern)
    (hscoped : target.isWellScopedAt ambient = true) :
    recoverValue? [] ambient 0 [] target =
      some { dependencies := [], ambient := ambient, body := target } := by
  simp [recoverValue?, hscoped, variableSpine?, rootRecoveryAssignment,
    rootOccurrenceAssignment, instantiateValue?, substitute_id]

/-- A successful root capture cannot invent local dependencies from an empty
occurrence spine. Its body is the supplied result, not a depth-shifted copy. -/
theorem recoverValue?_root_exact (dependencies : List TypeExpr)
    (ambient : Nat) (target : Pattern) (value : ContextualValue)
    (recovered : recoverValue? dependencies ambient 0 [] target = some value) :
    dependencies = [] ∧
      value = { dependencies := [], ambient := ambient, body := target } := by
  by_cases hscoped : target.isWellScopedAt ambient = true
  · by_cases hdeps : dependencies = []
    · subst dependencies
      rw [recoverValue?_root_empty ambient target hscoped] at recovered
      exact ⟨rfl, Option.some.inj recovered |>.symm⟩
    · have hne : dependencies.length ≠ 0 := by
        simpa using hdeps
      simp [recoverValue?, hscoped, variableSpine?] at recovered
      exact False.elim (hne recovered.1.symm)
  · simp [recoverValue?, hscoped] at recovered

/-- The raw premise machine's output contract. It may produce repeated names,
but every supplied pattern must have the declared sort in the caller context. -/
def RootOutputsHaveTypes (language : LanguageDef) (free : FreeTypeContext)
    (ambient : List TypeExpr)
    (raw : Mettapedia.OSLF.MeTTaIL.Match.Bindings) : Prop :=
  ∀ name result, (name, result) ∈ raw →
    ∃ resultType, free name = some resultType ∧
      HasType language free ambient result resultType

private theorem rootStep_preserves_types
    (language : LanguageDef) (free : FreeTypeContext)
    (spec : RuleBindingSpec) (ambient : List TypeExpr)
    (assignment updated : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (name : String) (result : Pattern)
    (before : AssignmentHasTypes language free spec ambient assignment)
    (resultType : TypeExpr) (declaredType : free name = some resultType)
    (typedResult : HasType language free ambient result resultType)
    (step : reconcileRootResult? spec ambient.length assignment
      (name, result) = some updated) :
    AssignmentHasTypes language free spec ambient updated := by
  cases hlookup : lookup assignment name with
  | some existing =>
      simp only [reconcileRootResult?, hlookup] at step
      cases hproject : instantiateValue? existing ambient.length 0 [] with
      | none => simp [hproject] at step
      | some projected =>
          by_cases heq : projected = result
          · simp [hproject, heq] at step
            subst updated
            exact before
          · simp [hproject, heq] at step
  | none =>
      simp only [reconcileRootResult?, hlookup] at step
      cases hdeps : dependencies? spec name with
      | none => simp [hdeps] at step
      | some dependencies =>
          cases hrecover : recoverValue? dependencies ambient.length 0 [] result with
          | none => simp [hdeps, hrecover] at step
          | some value =>
              obtain ⟨empty, exactValue⟩ :=
                recoverValue?_root_exact dependencies ambient.length
                  result value hrecover
              simp [hdeps, hrecover, assign, hlookup] at step
              subst updated
              subst dependencies
              subst value
              intro otherName otherValue member
              rcases List.mem_cons.mp member with eq | oldMember
              · cases eq
                exact ⟨[], resultType, hdeps, declaredType,
                  ⟨rfl, rfl, by simpa using typedResult⟩⟩
              · exact before otherName otherValue oldMember

/-- The executable ordered root-premise reconciler preserves every stored
value's sort and both contexts when its raw outputs satisfy their typing
contract. Repeated outputs are checked by the runtime and retain the existing
typed value. -/
theorem extendRoot?_preserves_types
    (language : LanguageDef) (free : FreeTypeContext)
    (spec : RuleBindingSpec) (ambient : List TypeExpr)
    (initial final : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (raw : Mettapedia.OSLF.MeTTaIL.Match.Bindings)
    (before : AssignmentHasTypes language free spec ambient initial)
    (outputs : RootOutputsHaveTypes language free ambient raw)
    (executed : extendRoot? spec ambient.length initial raw = some final) :
    AssignmentHasTypes language free spec ambient final := by
  unfold extendRoot? at executed
  induction raw generalizing initial with
  | nil =>
      have equal : initial = final := by
        simpa [List.foldlM_nil] using executed
      subst final
      exact before
  | cons pair rest inductionHypothesis =>
      rcases pair with ⟨name, result⟩
      rw [List.foldlM_cons] at executed
      obtain ⟨resultType, declaredType, typedResult⟩ :=
        outputs name result (by simp)
      cases hstep : reconcileRootResult? spec ambient.length initial
          (name, result) with
      | none => simp only [hstep] at executed; cases executed
      | some updated =>
          simp only [hstep] at executed
          exact inductionHypothesis updated
            (rootStep_preserves_types language free spec ambient initial
              updated name result before resultType declaredType typedResult hstep)
            (by
              intro nextName nextResult member
              exact outputs nextName nextResult (by simp [member]))
            executed

/-- Every selected root event from the actual premise interpreter retains
the typed scoped assignment. The only external typing hypothesis concerns
raw patterns supplied by the premise machine; the event ordinal and selected
assignment are the executable outputs. -/
theorem rootResults_preserves_types {Evidence : Type}
    (language : LanguageDef) (free : FreeTypeContext)
    (spec : RuleBindingSpec) (ambient : List TypeExpr)
    (relEnv : RelationEnv) (index : Nat) (premise : Premise)
    (initial final : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (event : PremiseEvent Evidence)
    (before : AssignmentHasTypes language free spec ambient initial)
    (rawSound : ∀ root raw,
      projectRoot? ambient.length initial = some root →
      raw ∈ premiseStepWithEnv relEnv language root premise →
      RootOutputsHaveTypes language free ambient raw)
    (selected : (event, final) ∈
      rootResults relEnv language spec ambient.length index premise initial) :
    AssignmentHasTypes language free spec ambient final := by
  by_cases hocc : hasOccurrenceAt spec index = true
  · simp [rootResults, hocc] at selected
  · cases hroot : projectRoot? ambient.length initial with
    | none => simp [rootResults, hocc, hroot] at selected
    | some root =>
        simp only [rootResults, hocc, Bool.false_eq_true, if_false,
          hroot, List.mem_filterMap] at selected
        obtain ⟨⟨raw, ordinal⟩, rawSelected, completedSelected⟩ := selected
        cases hcompleted : extendRoot? spec ambient.length initial raw with
        | none => simp [hcompleted] at completedSelected
        | some completed =>
            simp [hcompleted] at completedSelected
            rcases completedSelected with ⟨_, finalEq⟩
            subst final
            exact extendRoot?_preserves_types language free spec ambient
              initial completed raw before
              (rawSound root raw hroot
                (List.fst_mem_of_mem_zipIdx rawSelected)) hcompleted

end Mettapedia.GSLT.LanguageDef.RestAwareTyping
