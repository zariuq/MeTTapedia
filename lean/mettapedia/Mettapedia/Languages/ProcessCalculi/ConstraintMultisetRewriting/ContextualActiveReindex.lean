import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActiveSupport
import Mettapedia.OSLF.Syntax.ContextualReindexSupport

/-!
# Reindexing preserves the actual finite solver roster and model potential

A declaration equivalence maps the equation roster exactly. Pulling a
candidate assignment back along its inverse preserves the sum of image sizes
on that roster. This connects named selections to finite local progress
arguments without imposing finiteness on the ambient declaration family.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActiveReindex

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualActiveSupport
open scoped BigOperators

variable {S : Signature} {V W X : Type} [DecidableEq V] [DecidableEq W]
  {source : V → MetaArity S} {target : W → MetaArity S} {next : X → MetaArity S}

theorem active_reindex_subset (forward : V → W)
    (preserves : ∀ identity, target (forward identity) = source identity) (problem : Problem source) :
    active (mapProblem (reindex forward preserves) problem) ⊆ (active problem).image forward := by
  apply map_active_subset _ problem (active problem) ((active problem).image forward) (fun _ member => member)
  intro identity present name named
  rw [support_reindex, List.mem_singleton] at named
  subst name
  exact Finset.mem_image.mpr ⟨identity, present, rfl⟩

omit [DecidableEq V] [DecidableEq W] in
theorem mapProblem_reindex_inverse (forward : V → W) (backward : W → V)
    (first : ∀ identity, target (forward identity) = source identity)
    (second : ∀ identity, source (backward identity) = target identity)
    (inverse : Function.LeftInverse backward forward) (problem : Problem source) :
    mapProblem (reindex backward second) (mapProblem (reindex forward first) problem) = problem := by
  unfold mapProblem
  rw [List.map_map]
  convert List.map_id problem using 1
  congr 1
  funext equation
  rcases equation with ⟨⟨Γ, sort, left⟩, ⟨Δ, result, right⟩⟩
  exact congrArg₂ (fun first second => (observe first, observe second))
    (instantiate_reindex_inverse forward backward first second inverse left)
    (instantiate_reindex_inverse forward backward first second inverse right)

theorem active_reindex_exact (equivalence : V ≃ W)
    (first : ∀ identity, target (equivalence identity) = source identity)
    (second : ∀ identity, source (equivalence.symm identity) = target identity)
    (problem : Problem source) :
    active (mapProblem (reindex equivalence first) problem) = (active problem).image equivalence := by
  apply Finset.Subset.antisymm (active_reindex_subset equivalence first problem)
  intro name member
  obtain ⟨identity, present, rfl⟩ := Finset.mem_image.mp member
  have backwards := active_reindex_subset equivalence.symm second
    (mapProblem (reindex equivalence first) problem)
  rw [mapProblem_reindex_inverse equivalence equivalence.symm first second equivalence.left_inv] at backwards
  obtain ⟨original, originalPresent, same⟩ := Finset.mem_image.mp (backwards present)
  have identified : equivalence identity = original := by
    rw [← same, equivalence.apply_symm_apply]
  exact identified.symm ▸ originalPresent

theorem potential_reindex_exact (equivalence : V ≃ W)
    (first : ∀ identity, target (equivalence identity) = source identity)
    (second : ∀ identity, source (equivalence.symm identity) = target identity)
    (problem : Problem source) (candidate : Assignment source next) :
    potential (Assignment.compose candidate (reindex equivalence.symm second))
      (active (mapProblem (reindex equivalence first) problem)) = potential candidate (active problem) := by
  rw [active_reindex_exact equivalence first second]
  unfold potential
  rw [Finset.sum_image (fun _ _ _ _ same => equivalence.injective same)]
  apply Finset.sum_congr rfl
  intro identity _
  rw [Assignment.compose, termSize_instantiate_reindex, equivalence.symm_apply_apply]

omit [DecidableEq V] [DecidableEq W] in
theorem models_reindex_back (equivalence : V ≃ W)
    (first : ∀ identity, target (equivalence identity) = source identity)
    (second : ∀ identity, source (equivalence.symm identity) = target identity)
    (problem : Problem source) (candidate : Assignment source next) :
    Models (Assignment.compose candidate (reindex equivalence.symm second))
      (mapProblem (reindex equivalence first) problem) ↔ Models candidate problem := by
  rw [models_mapProblem, ← Assignment.compose_associative,
    reindex_left_inverse equivalence equivalence.symm first second equivalence.left_inv,
    Assignment.compose_identity_right]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActiveReindex
