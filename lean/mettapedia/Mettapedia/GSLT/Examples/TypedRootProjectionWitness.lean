import Mettapedia.GSLT.LanguageDef.TypedRootProjection
import Mettapedia.GSLT.Examples.TypedPremiseOutput

/-!
# An authored open capture passes through a typed root projection

The sorted premise-output language has an open `X` captured in one ambient
variable. Its projection to the root premise interpreter preserves both the
variable and its sort. An unrelated local dependency prevents projection.
The freshness premise supplies a nonempty executed positive case and a
rejected negative case.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Examples.TypedRootProjectionWitness

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)
open Mettapedia.GSLT.LanguageDef.RestAwareTyping
open Mettapedia.GSLT.Examples.TypedPremiseOutput
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.Engine

private abbrev term : TypeExpr := .base "Term"
private abbrev free : FreeTypeContext :=
  FreeTypeContext.ofList sortedPremiseRule.typeContext
private def spec : RuleBindingSpec :=
  { dependencies := [("X", []), ("Y", [])] }
private def captured : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment :=
  [("X", { dependencies := [], ambient := 1, body := .bvar 0 })]
private def root : Mettapedia.OSLF.MeTTaIL.Match.Bindings :=
  [("X", .bvar 0)]

private theorem captured_typed :
    AssignmentHasTypes sortedPremiseLanguage free spec [term] captured := by
  intro name value member
  simp only [captured, List.mem_singleton] at member
  cases member
  refine ⟨[], term, by decide +kernel, by decide +kernel,
    rfl, rfl, ?_⟩
  exact checkSchemaHasType_sound (by decide +kernel)

private theorem projects : projectRoot? 1 captured = some root := by
  decide +kernel

/-- The actual open variable remains typed after the root adapter's
projection; the result is derived from the captured contextual value. -/
theorem open_capture_projects_with_type :
    RootOutputsHaveTypes sortedPremiseLanguage free [term] root :=
  projectRoot?_has_types sortedPremiseLanguage free spec [term]
    captured root captured_typed projects

private def fresh : FreshnessCondition :=
  { varName := "Z", term := .bvar 0 }

theorem fresh_premise_returns_typed_root :
    root ∈ premiseStepWithEnv RelationEnv.empty sortedPremiseLanguage
      root (.freshness fresh) ∧
    RootOutputsHaveTypes sortedPremiseLanguage free [term] root := by
  constructor
  · decide +kernel
  · exact open_capture_projects_with_type

private def noSteps : StepOracle Unit := fun _ _ => []

/-- The authored freshness premise fires through the ordered premise
executor, retaining its exact root event and contextual assignment. -/
theorem fresh_event_selected :
    ((PremiseEvent.root 0 0 : PremiseEvent Unit), captured) ∈
      premiseResults noSteps RelationEnv.empty sortedPremiseLanguage
        sortedPremiseRule spec 1 0 (.freshness fresh) captured := by
  decide +kernel

theorem fresh_event_retains_types :
    AssignmentHasTypes sortedPremiseLanguage free spec [term] captured :=
  freshness_preserves_assignment_types sortedPremiseLanguage free
    sortedPremiseRule spec [term] noSteps RelationEnv.empty 0 fresh
    captured captured (PremiseEvent.root 0 0) captured_typed
    fresh_event_selected

private def notFresh : FreshnessCondition :=
  { varName := "X", term := .fvar "X" }

theorem nonfresh_premise_rejects :
    premiseStepWithEnv RelationEnv.empty sortedPremiseLanguage
      root (.freshness notFresh) = [] := by
  decide +kernel

/-- A capture with one local dependency cannot be projected to a root
binding, independently of the form of its body. -/
private def dependent : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment :=
  [("X", { dependencies := [term], ambient := 1, body := Pattern.bvar 0 })]

theorem local_dependency_rejects_root_projection :
    projectRoot? 1 dependent = none := by
  decide +kernel

#print axioms open_capture_projects_with_type
#print axioms fresh_premise_returns_typed_root
#print axioms fresh_event_retains_types
#print axioms local_dependency_rejects_root_projection

end Mettapedia.GSLT.Examples.TypedRootProjectionWitness
