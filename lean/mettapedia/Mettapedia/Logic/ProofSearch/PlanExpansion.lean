import Mettapedia.Logic.ProofSearch.PolynomialPlans
import Mettapedia.TypeTheory.IndexedPolynomialPlanCategory

/-!
# Expanding composed proof refinements into retained primitive plans

Finite refinements already have a polynomial instance. Here their existing
dependent-pair composition is interpreted as two retained method layers.
The translation is a morphism in the existing plan category and commutes with
hole filling and both total and partial proof reconstruction. All child
positions are conjunctive obligations; selecting an alternative method is
separate and is not performed by this construction.

This interface specializes the shared interpretation's uniform universe to
small goals, solutions, and route inventories. It does not introduce another
refinement structure, free syntax, or proof authority.
-/


set_option autoImplicit false

namespace Mettapedia.Logic.ProofSearch
namespace ProofObligations.PolynomialPlans

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial

variable {Goal : Type} {Solution : Goal → Type} {Routes : Goal → Type}

/-- One outer selected route, with one selected inner route at every child. -/
abbrev CompositeRoutes (methods : ∀ goal, Routes goal → Refinement Solution goal)
    (goal : Goal) :=
  Σ outer : Routes goal, ∀ premise, Routes ((methods goal outer).query premise)

def compositeMethods (methods : ∀ goal, Routes goal → Refinement Solution goal)
    (goal : Goal) (route : CompositeRoutes methods goal) : Refinement Solution goal :=
  (methods goal route.1).comp (fun premise => methods _ (route.2 premise))

/-- The template keeps both method layers and names every original Sigma-indexed
child at exactly its own goal. -/
def expansionTemplates (methods : ∀ goal, Routes goal → Refinement Solution goal) :
    MethodTemplates (polynomial (compositeMethods methods)) (polynomial methods) := by
  intro base goal route
  exact Free.node (polynomial methods) route.1 (fun premise =>
    Free.node (polynomial methods) (route.2 premise) (fun leaf =>
      Free.pure (polynomial methods) ⟨⟨premise, leaf⟩, rfl⟩))

/-- Substitution compatibility follows from the generic template theorem. -/
noncomputable def expansion (methods : ∀ goal, Routes goal → Refinement Solution goal) :
    PlanInterpretation (polynomial (compositeMethods methods)) (polynomial methods) :=
  MethodTemplates.interpretation (expansionTemplates methods)

theorem expansion_node (methods : ∀ goal, Routes goal → Refinement Solution goal)
    {Holes : Unit → Goal → Type} {base : Unit} {goal : Goal}
    (route : CompositeRoutes methods goal)
    (children : ∀ premise,
      (polynomial (compositeMethods methods)).Free Holes base
        ((compositeMethods methods goal route).query premise)) :
    (expansion methods).run base goal
        (Free.node (polynomial (compositeMethods methods)) route children) =
      Free.node (polynomial methods) route.1 (fun premise =>
        Free.node (polynomial methods) (route.2 premise) (fun leaf =>
          (expansion methods).run base _ (children ⟨premise, leaf⟩))) := rfl

/-- Arbitrary filled trees obey the same translation, not just one macro. -/
theorem expansion_fill (methods : ∀ goal, Routes goal → Refinement Solution goal)
    {Holes NextHoles : Unit → Goal → Type}
    (replacement : ∀ base goal, Holes base goal →
      (polynomial (compositeMethods methods)).Free NextHoles base goal)
    {base : Unit} {goal : Goal}
    (plan : (polynomial (compositeMethods methods)).Free Holes base goal) :
    (expansion methods).run base goal
        (Free.bind (polynomial (compositeMethods methods)) replacement base goal plan) =
      Free.bind (polynomial methods)
        (fun base goal h => (expansion methods).run base goal (replacement base goal h))
        base goal ((expansion methods).run base goal plan) :=
  (expansion methods).run_bind replacement plan

/-- The square compares the actual returned proof trees. -/
theorem reconstruct_expansion (methods : ∀ goal, Routes goal → Refinement Solution goal)
    {Holes : Unit → Goal → Type}
    (interpret : ∀ base goal, Holes base goal → Solution goal)
    {base : Unit} {goal : Goal}
    (plan : (polynomial (compositeMethods methods)).Free Holes base goal) :
    Free.fold (polynomial methods) interpret (reconstruction methods) base goal
        ((expansion methods).run base goal plan) =
      Free.fold (polynomial (compositeMethods methods)) interpret
        (reconstruction (compositeMethods methods)) base goal plan := by
  apply (expansion methods).reconstruct _ _ (fun _ _ value => value) interpret interpret
  · intros; rfl
  · intro base goal route values plans ih
    change (methods goal route.1).rebuild
        (fun premise => (methods _ (route.2 premise)).rebuild
          (fun leaf => Free.fold (polynomial methods) interpret (reconstruction methods)
            base _ (plans ⟨premise, leaf⟩))) =
      (methods goal route.1).rebuild
        (fun premise => (methods _ (route.2 premise)).rebuild
          (fun leaf => values ⟨premise, leaf⟩))
    congr 1
    funext premise
    congr 1
    funext leaf
    exact ih ⟨premise, leaf⟩

/-- Partial reconstruction also commutes: expanding a method cannot silently
fill missing children or convert route failure into a refutation. -/
theorem partial_reconstruct_expansion
    (methods : ∀ goal, Routes goal → Refinement Solution goal)
    {Holes : Unit → Goal → Type}
    (interpret : ∀ base goal, Holes base goal → Option (Solution goal))
    {base : Unit} {goal : Goal}
    (plan : (polynomial (compositeMethods methods)).Free Holes base goal) :
    Free.fold (polynomial methods) interpret (partialReconstruction methods) base goal
        ((expansion methods).run base goal plan) =
      Free.fold (polynomial (compositeMethods methods)) interpret
        (partialReconstruction (compositeMethods methods)) base goal plan := by
  apply (expansion methods).reconstruct _ _ (fun _ _ value => value) interpret interpret
  · intros; rfl
  · intro base goal route values plans ih
    change (methods goal route.1).tryRebuild
        (fun premise => (methods _ (route.2 premise)).tryRebuild
          (fun leaf => Free.fold (polynomial methods) interpret (partialReconstruction methods)
            base _ (plans ⟨premise, leaf⟩))) =
      ((methods goal route.1).comp (fun premise => methods _ (route.2 premise))).tryRebuild values
    refine Eq.trans ?_ (Refinement.tryRebuild_comp (methods goal route.1)
      (fun premise => methods _ (route.2 premise)) values).symm
    congr 1
    funext premise
    congr 1
    funext leaf
    exact ih ⟨premise, leaf⟩

end ProofObligations.PolynomialPlans
end Mettapedia.Logic.ProofSearch
