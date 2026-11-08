import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Semantic
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObserverPointwise

/-!
# Controls for the ordinary step

Over the first-order profile, at C2: the rows `20 : X` and `21 : Y` under the knowledge `X = Y`,
nothing escaped, which are equivalent modulo the knowledge (`Observation.ModuloControls.c2_equivalent`).

## Raw regions break the equivalence

* `syntacticY_not_semantic`, `noY_not_semantic`: the query that asks for the label `Y` itself does
  not read through solutions, so its firing is not a firing of the ordinary step.
* `syntactic_collision`: that firing is admitted at the first C2 state, and none of its renamings is
  admitted at the second (`Observation.ModuloFiringControls.syntactic_query_collision`).

## The semantic version does not collide

The semantic version of the same query reads `Y` through the solution: its region holds the rows
whose label the solution identifies with `Y` (`semanticY`, from `Observation.classRegion`).

* `noYSemantic_agrees`: the firing whose semantic query asks for no such row is admitted at both
  states or at neither; it is its own renaming. `noYSemantic_refused`: under `X = Y` it is admitted
  at neither, since the row `20 : X` is such a row.
* `sightY_counterpart`: the firing whose semantic query sights exactly the row `20` is admitted at the
  first state (`sightY_valid`) and has an equivalent counterpart at the second.

## Pointwise equivalence is not kept by every semantic firing

`pointwise_not_preserved`: the firing of `Observation.NonPrincipalFirings.pointwise_not_congruence`
has no query, so it is semantic, and no firing of its rule admitted at the other state has a
pointwise equivalent result. Pointwise equivalence is kept when the knowledge has a principal answer
(`Observation.PointwiseEquivalent.semantic_counterpart_of_principal`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Semantic.SemanticControls

open Mettapedia.Logic.LP
open AnnotatedRuns
open Observation
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (zeros)
open ModuloControls (Tm X Y c2 knowsXY zeros_solves c2_equivalent syntacticY)
open MeTTaCalculus.OccurrenceCommits (regionOf)

/-! ## Raw regions -/

/-- **The query that asks for the label `Y` itself does not read through solutions.** -/
theorem syntacticY_not_semantic : ¬ ReadsThroughSolutions A syntacticY := fun reads =>
  ModuloControls.syntactic_not_region ⟨⟨syntacticY.region, reads⟩, fun _ _ => rfl⟩

/-- **Its firing is not a firing of the ordinary step.** -/
theorem noY_not_semantic : ¬ IsSemantic A ModuloFiringControls.noY := fun reads =>
  syntacticY_not_semantic (reads syntacticY (List.mem_singleton_self _))

/-- **A raw region breaks the congruence**: at C2, equivalent modulo the knowledge, the firing of the
raw query is admitted at the first state and none of its renamings at the second. -/
theorem syntactic_collision :
    ModuloEquivalent A ModuloControls.label ∅ (c2 20) (c2 21) ∧ ¬ IsSemantic A ModuloFiringControls.noY ∧
      ModuloFiringControls.noY.Valid A ModuloControls.label (c2 20) ∧
      ∀ ρ : ℕ ≃ ℕ, ¬ (ModuloFiringControls.noY.rename ρ).Valid A ModuloControls.label (c2 21) :=
  ⟨c2_equivalent, noY_not_semantic, ModuloFiringControls.syntactic_query_collision.1,
    ModuloFiringControls.syntactic_query_collision.2⟩

/-! ## The semantic version -/

/-- **`Y` read through the solution**: the rows whose label the solution identifies with `Y`, with a
claimed sighted set. -/
noncomputable def semanticY (seen : Finset ℕ) : SemanticQuery A ℕ :=
  ⟨⟨(classRegion A Y).test, seen⟩, (classRegion A Y).respects⟩

/-- The firing whose semantic query asks for no row identified with `Y`. -/
noncomputable def noYSemantic : SemanticFiring A ℕ :=
  SemanticFiring.ofQueries ⟨[], [], [], [], []⟩ [semanticY ∅] ⟨[], [], []⟩

/-- The firing whose semantic query sights exactly the row `20`. -/
noncomputable def sightY : SemanticFiring A ℕ :=
  SemanticFiring.ofQueries ⟨[], [], [], [], []⟩ [semanticY {20}] ⟨[], [], []⟩

theorem noYSemantic_names : noYSemantic.1.names = ∅ := by
  simp [Firing.names, noYSemantic, SemanticFiring.ofQueries, semanticY, sighted]

/-- **The semantic query does not collide**: its firing is its own renaming, and it is admitted at
both C2 states or at neither. -/
theorem noYSemantic_agrees :
    (∀ ρ : ℕ ≃ ℕ, (SemanticFiring.rename ρ noYSemantic).1 = noYSemantic.1) ∧
      (noYSemantic.1.Valid A ModuloControls.label (c2 20) ↔
        noYSemantic.1.Valid A ModuloControls.label (c2 21)) := by
  have none : ∀ o ∈ noYSemantic.1.names, False := fun o member => by
    rw [noYSemantic_names] at member
    exact Finset.notMem_empty o member
  exact ⟨fun _ => noYSemantic.1.rename_eq_self fun o member => (none o member).elim,
    (c2_equivalent.semantic_named_firing noYSemantic fun o member => (none o member).elim).1⟩

/-- **Under `X = Y` the semantic query refuses**: the row `20 : X` is identified with `Y`. -/
theorem noYSemantic_refused : ¬ noYSemantic.1.Valid A ModuloControls.label (c2 20) := by
  intro valid
  have solved : A.Models zeros
      (noYSemantic.1.selection.problem ModuloControls.label noYSemantic.1.rule (c2 20)) := by
    intro e member
    have known : e ∈ knowsXY := by
      simpa [Selection.problem, Selection.equations, noYSemantic, SemanticFiring.ofQueries, c2]
        using member
    exact zeros_solves e known
  have asked := valid.observations (semanticY ∅).1 (List.mem_singleton_self _) zeros solved
  have empty : regionOf ModuloControls.label {20} ((classRegion A Y).test zeros) = ∅ := asked
  have inside : (20 : ℕ) ∈ regionOf ModuloControls.label {20} ((classRegion A Y).test zeros) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_singleton_self 20, ?_⟩
    simp only [classRegion, decide_eq_true_eq]
    exact zeros_solves (X, Y) (List.mem_singleton_self _)
  rw [empty] at inside
  exact Finset.notMem_empty 20 inside

theorem sightY_valid : sightY.1.Valid A ModuloControls.label (c2 20) := by
  refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, ?_, ⟨zeros, ?_⟩, ?_⟩, ?_⟩
  · exact ⟨by simp [sightY, SemanticFiring.ofQueries, Selection.commit],
      by simp [sightY, SemanticFiring.ofQueries, Selection.commit],
      by simp [sightY, SemanticFiring.ofQueries, Selection.commit],
      by simp [sightY, SemanticFiring.ofQueries, Selection.commit],
      by simp [sightY, SemanticFiring.ofQueries, Selection.commit]⟩
  · intro e member
    have known : e ∈ knowsXY := by
      simpa [Selection.problem, Selection.equations, sightY, SemanticFiring.ofQueries, c2] using member
    exact zeros_solves e known
  · intro check member
    simp [sightY, SemanticFiring.ofQueries] at member
  · intro query member σ solved
    have isQuery : query = (semanticY {20}).1 := by
      simpa [sightY, SemanticFiring.ofQueries] using member
    subst isQuery
    have identified : A.Solves σ (X, Y) := solved (X, Y) (by
      simp [Selection.problem, Selection.equations, sightY, SemanticFiring.ofQueries, c2, knowsXY])
    show regionOf ModuloControls.label {20} ((classRegion A Y).test σ) = {20}
    have inside : (classRegion A Y).test σ (ModuloControls.label 20) = true := by
      simp only [classRegion, decide_eq_true_eq]
      exact identified
    simp only [regionOf, Finset.filter_singleton, inside, if_true]

/-- **The semantic sighting has an equivalent counterpart at the other C2 state.** -/
theorem sightY_counterpart :
    ∃ π : ℕ ≃ ℕ, (SemanticFiring.rename π sightY).1.Valid A ModuloControls.label (c2 21) ∧
      ModuloEquivalent A ModuloControls.label ∅ (sightY.1.result ModuloControls.label (c2 20))
        ((SemanticFiring.rename π sightY).1.result ModuloControls.label (c2 21)) :=
  c2_equivalent.semantic_admitted sightY sightY_valid fun _ member => by
    simp [sightY, SemanticFiring.ofQueries] at member

/-! ## Pointwise equivalence -/

/-- **Pointwise equivalence is not kept by every admitted semantic firing**: the firing of the
obstruction has no query. -/
theorem pointwise_not_preserved :
    IsSemantic NonPrincipal.action (NonPrincipalFirings.takeX 1) ∧
      PointwiseEquivalent NonPrincipal.action NonPrincipal.label ∅ NonPrincipal.left NonPrincipal.right ∧
      (NonPrincipalFirings.takeX 1).Valid NonPrincipal.action NonPrincipal.label NonPrincipal.left ∧
      ∀ g : Firing NonPrincipal.Atom NonPrincipal.Choice ℕ, g.rule = NonPrincipalFirings.takeRule →
        g.Valid NonPrincipal.action NonPrincipal.label NonPrincipal.right →
        ¬ PointwiseEquivalent NonPrincipal.action NonPrincipal.label ∅
          ((NonPrincipalFirings.takeX 1).result NonPrincipal.label NonPrincipal.left)
          (g.result NonPrincipal.label NonPrincipal.right) :=
  ⟨isSemantic_of_queries_nil rfl, NonPrincipalFirings.pointwise_not_congruence⟩

#print axioms syntacticY_not_semantic
#print axioms noY_not_semantic
#print axioms syntactic_collision
#print axioms noYSemantic_names
#print axioms noYSemantic_agrees
#print axioms noYSemantic_refused
#print axioms sightY_valid
#print axioms sightY_counterpart
#print axioms pointwise_not_preserved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Semantic.SemanticControls
