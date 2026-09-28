import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact elimination of an internal linear component

A component exposes a boundary input and a boundary response. Internal
variables satisfy an invertible linear block equation. Eliminating that block
produces the Schur response, with the internal forcing retained as an affine
term. The resulting boundary relation is exactly the original existential
relation, and therefore composes with arbitrary boundary predicates.

This is the linear algebraic core of static network reduction. It does not
prove invertibility for an arbitrary graph, a dynamic transfer-function law,
or a reduction of general nonlinear programs. A singular-block control shows
why a single response function is not always an adequate boundary object.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.LinearBoundaryReduction

universe u v w

variable {K : Type u} [Field K]
variable {Boundary : Type v} [AddCommGroup Boundary] [Module K Boundary]
variable {Interior : Type w} [AddCommGroup Interior] [Module K Interior]

/-- The four blocks of a linear relation, with an actual inverse for the
internal block. The field is arbitrary, including exact rational arithmetic. -/
structure System (K : Type u) [Field K]
    (Boundary : Type v) [AddCommGroup Boundary] [Module K Boundary]
    (Interior : Type w) [AddCommGroup Interior] [Module K Interior] where
  boundaryBlock : Boundary →ₗ[K] Boundary
  outward : Interior →ₗ[K] Boundary
  inward : Boundary →ₗ[K] Interior
  internalBlock : Interior ≃ₗ[K] Interior

namespace System

variable (system : System K Boundary Interior)

def interiorSolution (input : Boundary) (forcing : Interior) : Interior :=
  system.internalBlock.symm (forcing - system.inward input)

def schur : Boundary →ₗ[K] Boundary :=
  system.boundaryBlock - system.outward.comp
    (system.internalBlock.symm.toLinearMap.comp system.inward)

def reducedResponse (input : Boundary) (forcing : Interior) : Boundary :=
  system.schur input + system.outward (system.internalBlock.symm forcing)

def fullRelation (input response : Boundary) (forcing : Interior) : Prop :=
  ∃ internal : Interior,
    system.inward input + system.internalBlock internal = forcing ∧
    system.boundaryBlock input + system.outward internal = response

theorem interiorSolution_satisfies (input : Boundary) (forcing : Interior) :
    system.inward input +
      system.internalBlock (system.interiorSolution input forcing) = forcing := by
  simp [interiorSolution]

theorem interiorSolution_unique (input : Boundary) (forcing internal : Interior)
    (solves : system.inward input + system.internalBlock internal = forcing) :
    internal = system.interiorSolution input forcing := by
  have image : system.internalBlock internal = forcing - system.inward input := by
    exact eq_sub_of_add_eq' solves
  apply system.internalBlock.injective
  simpa [interiorSolution] using image

theorem response_eq_schur (input : Boundary) (forcing : Interior) :
    system.boundaryBlock input +
      system.outward (system.interiorSolution input forcing) =
        system.reducedResponse input forcing := by
  simp only [interiorSolution, reducedResponse, schur, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, map_sub]
  abel

/-- Elimination preserves the entire boundary relation, not merely one
selected solution. The internal witness is reconstructed explicitly. -/
theorem fullRelation_iff (input response : Boundary) (forcing : Interior) :
    system.fullRelation input response forcing ↔
      system.reducedResponse input forcing = response := by
  constructor
  · rintro ⟨internal, solves, observes⟩
    rw [system.interiorSolution_unique input forcing internal solves] at observes
    exact (system.response_eq_schur input forcing).symm.trans observes
  · intro observes
    exact ⟨system.interiorSolution input forcing,
      system.interiorSolution_satisfies input forcing,
      (system.response_eq_schur input forcing).trans observes⟩

/-- Arbitrary surrounding constraints which inspect only the declared
boundary can use the reduced component. No assumption on that predicate is
needed. -/
theorem contextual_elimination (outside : Boundary → Boundary → Prop)
    (input : Boundary) (forcing : Interior) :
    (∃ response, system.fullRelation input response forcing ∧ outside input response) ↔
      outside input (system.reducedResponse input forcing) := by
  simp only [system.fullRelation_iff]
  simp

end System

/-! ## Exact rational controls -/

def scalar (coefficient : ℚ) : ℚ →ₗ[ℚ] ℚ where
  toFun := fun value => coefficient * value
  map_add' := by intros; ring
  map_smul' := by intros; simp only [smul_eq_mul, RingHom.id_apply]; ring

/-- A coupled system: the boundary response is `2x + y` and the internal
constraint is `3x + y = j`. Eliminating `y` gives `-x + j`. -/
def exampleSystem : System ℚ ℚ ℚ where
  boundaryBlock := scalar 2
  outward := scalar 1
  inward := scalar 3
  internalBlock := LinearEquiv.refl ℚ ℚ

theorem example_reduced (input forcing : ℚ) :
    exampleSystem.reducedResponse input forcing = -input + forcing := by
  simp [System.reducedResponse, System.schur, exampleSystem, scalar]
  ring

theorem example_full_relation : exampleSystem.fullRelation 5 (-5) 0 := by
  rw [System.fullRelation_iff, example_reduced]
  norm_num

/-- Forgetting the internal forcing changes an observable boundary response. -/
theorem forcing_cannot_be_erased :
    exampleSystem.reducedResponse 5 0 ≠ exampleSystem.reducedResponse 5 2 := by
  simp only [example_reduced]
  norm_num

/-- A singular internal block can leave many observable responses. A
relation still represents it, but one response function cannot represent all
solutions. -/
def singularRelation (response : ℚ) : Prop :=
  ∃ internal : ℚ, (0 : ℚ) * internal = 0 ∧ internal = response

theorem singular_has_distinct_responses : singularRelation 0 ∧ singularRelation 1 := by
  constructor
  · exact ⟨0, by norm_num, rfl⟩
  · exact ⟨1, by norm_num, rfl⟩

theorem singular_not_single_response :
    ¬ ∃ response : ℚ, ∀ other, singularRelation other ↔ other = response := by
  rintro ⟨response, exactRelation⟩
  have zero := (exactRelation 0).mp singular_has_distinct_responses.1
  have one := (exactRelation 1).mp singular_has_distinct_responses.2
  have : (0 : ℚ) = 1 := zero.trans one.symm
  norm_num at this

end Mettapedia.GSLT.Dynamics.LinearBoundaryReduction
