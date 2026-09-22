import Mettapedia.TypeTheory.IndexedPolynomialCoalgebra
import Mettapedia.Logic.ProofSearch.Refinement

/-!
# Existing proof refinements as indexed polynomial algebras

An authored route inventory supplies the shapes. Its existing refinements
supply indexed premises and reconstruction, without selecting an inventory,
search policy, or proof authority. The free polynomial tree retains nested
method applications and typed holes. Partial replay uses `tryRebuild` from
the same refinements; no missing proof is inserted by the plan construction.
-/


set_option autoImplicit false

namespace Mettapedia.Logic.ProofSearch
namespace ProofObligations.PolynomialPlans

open Mettapedia.TypeTheory

universe u v w w'

variable {Goal : Type u} {Solution : Goal → Type u}
variable {Routes : Goal → Type v}

/-- The route inventory is separate from the existing reconstruction algebra. -/
def polynomial (methods : ∀ goal, Routes goal → Refinement Solution goal) :
    IndexedPolynomial.{0, u, v, u} Unit (fun _ => Goal) where
  Shape := fun _ goal => Routes goal
  Position := fun {_base} {goal} route => (methods goal route).Premise
  next := fun {_base} {goal} route premise => (methods goal route).query premise

/-- Actual typed proof reconstruction is an algebra on the selected routes. -/
def reconstruction (methods : ∀ goal, Routes goal → Refinement Solution goal) :
    (polynomial methods).Algebra (fun _ goal => Solution goal) where
  act := fun _ goal inputLayer => (methods goal inputLayer.1).rebuild inputLayer.2

/-- The exact same routes reconstruct only when every premise is supplied. -/
def partialReconstruction (methods : ∀ goal, Routes goal → Refinement Solution goal) :
    (polynomial methods).Algebra (fun _ goal => Option (Solution goal)) where
  act := fun _ goal inputLayer => (methods goal inputLayer.1).tryRebuild inputLayer.2

/-- Nested method applications with leaves in a goal-indexed hole family. -/
abbrev Plan (methods : ∀ goal, Routes goal → Refinement Solution goal)
    (Holes : Goal → Type w) (goal : Goal) :=
  (polynomial methods).Free (fun _ goal => Holes goal) () goal

/-- An unfinished obligation is a value, not a missing parent proof. -/
def hole (methods : ∀ goal, Routes goal → Refinement Solution goal)
    {Holes : Goal → Type w} {goal : Goal} (value : Holes goal) :
    Plan methods Holes goal := IndexedPolynomial.Free.pure (polynomial methods) value

/-- A method node records the selected route and every separately indexed child. -/
def applyMethod (methods : ∀ goal, Routes goal → Refinement Solution goal)
    {Holes : Goal → Type w} {goal : Goal} (route : Routes goal)
    (children : ∀ premise, Plan methods Holes ((methods goal route).query premise)) :
    Plan methods Holes goal :=
  IndexedPolynomial.Free.node (polynomial methods) route children

/-- Substitute a typed child plan for each selected hole, retaining method nodes. -/
noncomputable def fill (methods : ∀ goal, Routes goal → Refinement Solution goal)
    {Holes : Goal → Type w} {NextHoles : Goal → Type w'}
    (replacement : ∀ goal, Holes goal → Plan methods NextHoles goal)
    {goal : Goal} (plan : Plan methods Holes goal) : Plan methods NextHoles goal :=
  IndexedPolynomial.Free.bind (polynomial methods)
    (fun base goal value => by cases base; exact replacement goal value) () goal plan

@[simp] theorem fill_hole (methods : ∀ goal, Routes goal → Refinement Solution goal)
    {Holes : Goal → Type w} {NextHoles : Goal → Type w'}
    (replacement : ∀ goal, Holes goal → Plan methods NextHoles goal)
    {goal : Goal} (value : Holes goal) :
    fill methods replacement (hole methods value) = replacement goal value := rfl

@[simp] theorem fill_applyMethod
    (methods : ∀ goal, Routes goal → Refinement Solution goal)
    {Holes : Goal → Type w} {NextHoles : Goal → Type w'}
    (replacement : ∀ goal, Holes goal → Plan methods NextHoles goal)
    {goal : Goal} (route : Routes goal)
    (children : ∀ premise, Plan methods Holes ((methods goal route).query premise)) :
    fill methods replacement (applyMethod methods route children) =
      applyMethod methods route (fun premise => fill methods replacement (children premise)) := rfl

/-- Reconstruct this retained tree using its actual proof leaves. -/
noncomputable def reconstruct (methods : ∀ goal, Routes goal → Refinement Solution goal)
    {goal : Goal} (plan : Plan methods Solution goal) : Solution goal :=
  IndexedPolynomial.Free.fold (polynomial methods) (fun _ _ proof => proof)
    (reconstruction methods) () goal plan

/-- Replay a partial tree; the tree remains available even when its root is open. -/
noncomputable def reconstruct? (methods : ∀ goal, Routes goal → Refinement Solution goal)
    {goal : Goal} (plan : Plan methods (fun child => Option (Solution child)) goal) :
    Option (Solution goal) :=
  IndexedPolynomial.Free.fold (polynomial methods) (fun _ _ proof => proof)
    (partialReconstruction methods) () goal plan

@[simp] theorem reconstruct_hole
    (methods : ∀ goal, Routes goal → Refinement Solution goal)
    {goal : Goal} (proof : Solution goal) :
    reconstruct methods (hole methods proof) = proof := rfl

@[simp] theorem reconstruct_applyMethod
    (methods : ∀ goal, Routes goal → Refinement Solution goal)
    {goal : Goal} (route : Routes goal)
    (children : ∀ premise, Plan methods Solution ((methods goal route).query premise)) :
    reconstruct methods (applyMethod methods route children) =
      (methods goal route).rebuild (fun premise => reconstruct methods (children premise)) := rfl

@[simp] theorem reconstruct?_hole
    (methods : ∀ goal, Routes goal → Refinement Solution goal)
    {goal : Goal} (proof : Option (Solution goal)) :
    reconstruct? methods (hole methods proof) = proof := rfl

@[simp] theorem reconstruct?_applyMethod
    (methods : ∀ goal, Routes goal → Refinement Solution goal)
    {goal : Goal} (route : Routes goal)
    (children : ∀ premise,
      Plan methods (fun child => Option (Solution child)) ((methods goal route).query premise)) :
    reconstruct? methods (applyMethod methods route children) =
      (methods goal route).tryRebuild (fun premise => reconstruct? methods (children premise)) := rfl

/-- One layer of the free tree is the original reconstruction, not a new proof. -/
theorem reconstruct_one_layer
    (methods : ∀ goal, Routes goal → Refinement Solution goal)
    {goal : Goal} (route : Routes goal)
    (answers : ∀ premise, Solution ((methods goal route).query premise)) :
    reconstruct methods (applyMethod methods route (fun premise => hole methods (answers premise))) =
      (methods goal route).rebuild answers := rfl

/-- Nested tree reconstruction agrees with the existing finite premise composition.
The tree keeps the two method layers; the refinement keeps their Sigma-indexed leaves. -/
theorem reconstruct_two_layers
    (methods : ∀ goal, Routes goal → Refinement Solution goal)
    {goal : Goal} (outer : Routes goal)
    (inner : ∀ premise, Routes ((methods goal outer).query premise))
    (answers : ∀ premise leaf,
      Solution ((methods _ (inner premise)).query leaf)) :
    reconstruct methods (applyMethod methods outer (fun premise =>
      applyMethod methods (inner premise) (fun leaf => hole methods (answers premise leaf)))) =
      ((methods goal outer).comp (fun premise => methods _ (inner premise))).rebuild
        (fun occurrence => answers occurrence.1 occurrence.2) := rfl

/-- An unresolved indexed leaf blocks only this reconstruction route. -/
theorem open_child_keeps_root_open
    (methods : ∀ goal, Routes goal → Refinement Solution goal)
    {goal : Goal} (route : Routes goal)
    (answers : ∀ premise, Option (Solution ((methods goal route).query premise)))
    (missing : ∃ premise, answers premise = none) :
    reconstruct? methods (applyMethod methods route (fun premise => hole methods (answers premise))) =
      none :=
  (Refinement.tryRebuild_eq_none_iff _ _).2 missing

/-- A returned tree proof records every actual leaf and the reconstruction equation. -/
theorem reconstruct?_one_layer_eq_some_iff
    (methods : ∀ goal, Routes goal → Refinement Solution goal)
    {goal : Goal} (route : Routes goal)
    (answers : ∀ premise, Option (Solution ((methods goal route).query premise)))
    (proof : Solution goal) :
    reconstruct? methods (applyMethod methods route (fun premise => hole methods (answers premise))) =
        some proof ↔
      ∃ actual, (∀ premise, answers premise = some (actual premise)) ∧
        (methods goal route).rebuild actual = proof :=
  Refinement.tryRebuild_eq_some_iff _ _ _

end ProofObligations.PolynomialPlans
end Mettapedia.Logic.ProofSearch
