import Mettapedia.Logic.ProofSearch.PlanExpansion
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLProofObligations

/-!
# Branching HOL controls for composite-method expansion

The selected inventory contains actual HOL conjunction introduction. A composed
method has four dependent-pair child occurrences and expands to three existing
two-child methods. The translation retains the exact HOL proof tree, and one
missing occurrence blocks reconstruction despite all four queries being equal.
-/

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PolynomialHOLExpansionControls

open Mettapedia.Logic
open ProofSearch ProofObligations
open Mettapedia.TypeTheory.IndexedPolynomial

abbrev Const (_ : Logic.HOL.Ty Unit) := Empty
abbrev Goal := HOLAdapter.Goal Unit Const
abbrev Solution := @HOLAdapter.Solution Unit Const

/-- An explicit small inventory of an existing HOL inference, not a new
refinement record or an automatic search policy. -/
inductive ConjunctionMethod : Goal → Type
  | intro {context : Logic.HOL.Ctx Unit}
      {hypotheses : List (Logic.HOL.Formula Const context)}
      (first second : Logic.HOL.Formula Const context) :
      ConjunctionMethod ⟨context, hypotheses, .and first second⟩

def methods : ∀ goal, ConjunctionMethod goal → Refinement Solution goal
  | _, .intro first second => ProofObligations.HOL.andI first second

abbrev leaf : Goal := ⟨[], [], .top⟩
abbrev pairGoal : Goal := ⟨[], [], .and .top .top⟩
abbrev root : Goal := ⟨[], [], .and (.and .top .top) (.and .top .top)⟩

def outer : ConjunctionMethod root := .intro (.and .top .top) (.and .top .top)

def composed : PolynomialPlans.CompositeRoutes methods root := by
  refine ⟨outer, ?_⟩
  intro occurrence
  rcases occurrence with ⟨occurrence⟩
  refine Fin.cases ?_ (fun index => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) index)
    occurrence <;> exact .intro .top .top

abbrev route := PolynomialPlans.compositeMethods methods root composed

def answers (proof : Solution leaf) : ∀ occurrence, Solution (route.query occurrence) := by
  intro occurrence
  rcases occurrence with ⟨⟨outerIndex⟩, innerIndex⟩
  revert innerIndex
  refine Fin.cases ?_ (fun index => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) index)
    outerIndex
  all_goals
    intro innerIndex
    rcases innerIndex with ⟨innerIndex⟩
    refine Fin.cases ?_ (fun index => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) index)
      innerIndex <;> exact proof

def sourcePlan (proof : Solution leaf) :
    PolynomialPlans.Plan (PolynomialPlans.compositeMethods methods) Solution root :=
  PolynomialPlans.applyMethod (PolynomialPlans.compositeMethods methods) composed
    (fun occurrence => PolynomialPlans.hole (PolynomialPlans.compositeMethods methods)
      (answers proof occurrence))

noncomputable def targetPlan (proof : Solution leaf) : PolynomialPlans.Plan methods Solution root :=
  (PolynomialPlans.expansion methods).run () root (sourcePlan proof)

def expected (proof : Solution leaf) : Solution root :=
  .andI (.andI proof proof) (.andI proof proof)

theorem source_reconstructs (proof : Solution leaf) :
    PolynomialPlans.reconstruct (PolynomialPlans.compositeMethods methods) (sourcePlan proof) =
      expected proof := rfl

/-- The general interpretation theorem compares the exact retained HOL tree. -/
theorem target_reconstructs (proof : Solution leaf) :
    PolynomialPlans.reconstruct methods (targetPlan proof) = expected proof :=
  (PolynomialPlans.reconstruct_expansion methods (fun _ _ proof => proof)
    (sourcePlan proof)).trans (source_reconstructs proof)

theorem two_children_per_primitive :
    Fintype.card (methods root outer).Premise = 2 := by decide

theorem four_composed_occurrences : Fintype.card route.Premise = 4 := by decide

def direct : Solution leaf := .topI
def detour : Solution leaf := .andEL (.andI .topI .topI)

theorem actual_proofs_not_identified :
    PolynomialPlans.reconstruct methods (targetPlan direct) ≠
      PolynomialPlans.reconstruct methods (targetPlan detour) := by
  rw [target_reconstructs, target_reconstructs]
  intro same
  cases same

/-- The missing occurrence is (first outer child, second inner child). -/
def partialAnswers : ∀ occurrence, Option (Solution (route.query occurrence)) := by
  intro occurrence
  rcases occurrence with ⟨⟨outerIndex⟩, innerIndex⟩
  revert innerIndex
  refine Fin.cases ?_ (fun index => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) index)
    outerIndex
  · intro innerIndex
    rcases innerIndex with ⟨innerIndex⟩
    refine Fin.cases ?_ (fun index => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) index)
      innerIndex
    · exact some .topI
    · exact none
  · intro innerIndex
    rcases innerIndex with ⟨innerIndex⟩
    refine Fin.cases ?_ (fun index => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) index)
      innerIndex <;> exact some .topI

def partialSource : PolynomialPlans.Plan (PolynomialPlans.compositeMethods methods)
    (fun goal => Option (Solution goal)) root :=
  PolynomialPlans.applyMethod (PolynomialPlans.compositeMethods methods) composed
    (fun occurrence => PolynomialPlans.hole (PolynomialPlans.compositeMethods methods)
      (partialAnswers occurrence))

noncomputable def partialTarget : PolynomialPlans.Plan methods
    (fun goal => Option (Solution goal)) root :=
  (PolynomialPlans.expansion methods).run () root partialSource

theorem source_stays_open :
    PolynomialPlans.reconstruct? (PolynomialPlans.compositeMethods methods) partialSource = none := by
  change route.tryRebuild partialAnswers = none
  apply (Refinement.tryRebuild_eq_none_iff _ _).2
  exact ⟨⟨⟨0⟩, ⟨1⟩⟩, rfl⟩

theorem expanded_stays_open : PolynomialPlans.reconstruct? methods partialTarget = none :=
  (PolynomialPlans.partial_reconstruct_expansion methods (fun _ _ proof => proof)
    partialSource).trans source_stays_open

/-- No method in this selected inventory introduces falsity. This is an
inventory limitation, not a claim that no other HOL inference can apply. -/
theorem unsupported_goal_has_no_selected_method :
    ¬ Nonempty (ConjunctionMethod (⟨[], [], .bot⟩ : Goal)) := by
  rintro ⟨method⟩
  nomatch method

theorem unsupported_hole_stays_open :
    PolynomialPlans.reconstruct? methods
      (PolynomialPlans.hole methods (goal := (⟨[], [], .bot⟩ : Goal)) none) = none := rfl

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PolynomialHOLExpansionControls
