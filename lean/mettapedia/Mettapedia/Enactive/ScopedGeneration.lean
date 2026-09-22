import Mettapedia.Enactive.Basic
import Mettapedia.TypeTheory.Authority

/-!
# Scoped task generations and scoped authority growth

Michael Timothy Bennett's child relation orders tasks by generational
specialization.  It does not by itself choose a type-theoretic fragment or an
authority.  This file supplies the deliberately narrower bridge needed by
scoped authorities: a correspondence is evidence consisting of

* a Bennett task-generation chain;
* inclusion of the judgment classes recognized by two named profiles;
* an authority-axis refinement between two existing four-arm outcomes.

No converse or canonical assignment is claimed.  The four-arm outcome
(established, refuted, outside-fragment, incomplete) is an authority
extension of Bennett's theory, not a definition attributed to Bennett.
Operational faults remain outside that semantic sum.
-/


set_option autoImplicit false

namespace Mettapedia.Enactive.ScopedGeneration

open Mettapedia.Enactive
open Mettapedia.TypeTheory.AuthorityTheory

universe uProfile uJudgment uEstablished uRefuted uBoundary uIncomplete uWorld

/-! ## Coverage for an arbitrary recognition relation -/

variable {Profile : Type uProfile} {Judgment : Type uJudgment}
variable (recognizes : Profile → Judgment → Prop)


/-- Every judgment class recognized by `smaller` is also recognized by
`larger`.  The recognition relation is supplied by the instance; no particular
calculus or profile inventory is imposed. -/
def ScopeIncluded (smaller larger : Profile) : Prop :=
  ∀ judgmentClass, recognizes smaller judgmentClass →
    recognizes larger judgmentClass

theorem ScopeIncluded.refl (profile : Profile) :
    ScopeIncluded recognizes profile profile := by
  intro judgmentClass recognized
  exact recognized

theorem ScopeIncluded.trans {first second third : Profile}
    (firstSecond : ScopeIncluded recognizes first second)
    (secondThird : ScopeIncluded recognizes second third) :
    ScopeIncluded recognizes first third := by
  intro judgmentClass recognized
  exact secondThird judgmentClass (firstSecond judgmentClass recognized)

/-! ## The scoped correspondence -/

/-- Evidence that one particular Bennett generation is accompanied by one
particular scoped authority growth.  All three components are explicit; the
task order is never silently identified with the authority order. -/
structure ScopedAuthorityGeneration
    {World : Type uWorld} {layer : AbstractionLayer World}
    (steps : Nat) (child ancestor : Task layer)
    (smallerProfile largerProfile : Profile)
    {Established : Sort uEstablished} {Refuted : Sort uRefuted}
    {Boundary : Type uBoundary} {Incomplete : Type uIncomplete}
    (before after : Outcome Established Refuted Boundary Incomplete) : Prop where
  taskGrowth : Task.Generation steps child ancestor
  scopeGrowth : ScopeIncluded recognizes smallerProfile largerProfile
  outcomeGrowth : Outcome.AuthorityRefines before after

/-- Scoped correspondences compose when their task, profile, and outcome
boundaries meet. -/
theorem ScopedAuthorityGeneration.append
    {World : Type uWorld} {layer : AbstractionLayer World}
    {firstSteps secondSteps : Nat} {first middle last : Task layer}
    {firstProfile middleProfile lastProfile : Profile}
    {Established : Sort uEstablished} {Refuted : Sort uRefuted}
    {Boundary : Type uBoundary} {Incomplete : Type uIncomplete}
    {firstOutcome middleOutcome lastOutcome :
      Outcome Established Refuted Boundary Incomplete}
    (left : ScopedAuthorityGeneration recognizes firstSteps first middle
      firstProfile middleProfile firstOutcome middleOutcome)
    (right : ScopedAuthorityGeneration recognizes secondSteps middle last
      middleProfile lastProfile middleOutcome lastOutcome) :
    ScopedAuthorityGeneration recognizes (firstSteps + secondSteps) first last
      firstProfile lastProfile firstOutcome lastOutcome where
  taskGrowth := left.taskGrowth.append right.taskGrowth
  scopeGrowth := ScopeIncluded.trans recognizes left.scopeGrowth right.scopeGrowth
  outcomeGrowth := left.outcomeGrowth.trans right.outcomeGrowth

/-! ## A nontrivial task-and-authority witness -/

namespace Canary

open Mettapedia.Enactive.NoAbstraction

def childTask : Task (AbstractionLayer.full Bool) where
  inputs := {trueAspect}
  correctOutputs := {trueAspect}
  correctOutputs_subset := by
    intro output member
    rw [Set.mem_singleton_iff.mp member,
      Mettapedia.Enactive.Completion.mem_extensionSet]
    exact ⟨trueAspect, Set.mem_singleton _, le_rfl⟩

def parentTask : Task (AbstractionLayer.full Bool) where
  inputs := {trueAspect, redundantTrueAspect}
  correctOutputs := {trueAspect}
  correctOutputs_subset := by
    intro output member
    rw [Set.mem_singleton_iff.mp member,
      Mettapedia.Enactive.Completion.mem_extensionSet]
    exact ⟨trueAspect, Set.mem_insert _ _, le_rfl⟩

theorem trueAspect_ne_redundantTrueAspect :
    trueAspect ≠ redundantTrueAspect := by
  intro equal
  apply trueAspect_extension_ne_redundant
  rw [equal]

theorem child_isChild_parent : childTask.IsChild parentTask := by
  constructor
  · rw [Set.ssubset_iff_subset_ne]
    constructor
    · simp [childTask, parentTask]
    · intro equalInputs
      have redundantMember :
          redundantTrueAspect ∈ childTask.inputs := by
        rw [equalInputs]
        simp [parentTask]
      have aspectsEqual : redundantTrueAspect = trueAspect := by
        simpa [childTask] using redundantMember
      exact trueAspect_ne_redundantTrueAspect aspectsEqual.symm
  · simp [childTask, parentTask]

theorem oneStepGeneration : Task.Generation 1 childTask parentTask := by
  simpa using Task.Generation.step child_isChild_parent
    (Task.Generation.refl parentTask)

abbrev TestOutcome := Outcome Unit Unit Unit Unit

def before : TestOutcome := .outsideFragment ()
def after : TestOutcome := .established ()

/-- Authority abstention is retained and non-Boolean.  This is our competence-
boundary extension, not a theorem attributed to Bennett. -/
theorem outsideFragment_is_retained_not_refuted :
    before.asBool = none ∧ before.safeRetain = true := by
  exact ⟨rfl, rfl⟩

/-- A larger resource budget cannot resolve a stable fragment boundary; the
same transition is legal only on the authority axis. -/
theorem outside_to_established_not_budgetRefinement :
    ¬ Outcome.BudgetRefines before after := by
  intro refinement
  have stable := Outcome.budget_does_not_resolve_outside () after refinement
  cases stable

end Canary

#print axioms ScopedAuthorityGeneration.append
#print axioms Canary.child_isChild_parent
#print axioms Canary.outsideFragment_is_retained_not_refuted
#print axioms Canary.outside_to_established_not_budgetRefinement

end Mettapedia.Enactive.ScopedGeneration
