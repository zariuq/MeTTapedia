import Mettapedia.GSLT.GraphTheory.FactorInterpretation
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Sigma.Basic

/-!
# Indexed disjoint unions of graph-model partial pairs

Coding an output in a selected factor is defined exactly when its entire
finite support belongs to that factor. The inverse-image support is used only
after this full-support guard, so mixed inputs are never silently projected.
Each selected factor discharges the existing primitive FactorEmbedding laws;
the existing canonical-completion interpreter then yields its theory inclusion.
This proves a common lower bound, not realization of an exact intersection.
The index inhabits `Type`, matching the current bundled web carrier universe.
-/

namespace Mettapedia.GSLT.GraphTheory.PartialPair.IndexedFamily

open Mettapedia.GSLT.Core

variable {Index : Type} (models : Index → GraphModel)

abbrev Carrier := Σ index, (models index).Carrier

def embedding (index : Index) : (models index).Carrier ↪ Carrier models :=
  Function.Embedding.sigmaMk (β := fun selected => (models selected).Carrier) index

noncomputable local instance : DecidableEq (Carrier models) := Classical.decEq _

noncomputable def projection (index : Index) (support : Finset (Carrier models)) :
    Finset (models index).Carrier :=
  support.preimage (embedding models index) (embedding models index).injective.injOn

@[simp] theorem mem_projection (index : Index) (support : Finset (Carrier models))
    (value : (models index).Carrier) :
    value ∈ projection models index support ↔ embedding models index value ∈ support :=
  Finset.mem_preimage

@[simp] theorem projection_map (index : Index) (support : Finset (models index).Carrier) :
    projection models index (support.map (embedding models index)) = support := by
  ext value
  exact (mem_projection models index _ value).trans (Finset.mem_map' (embedding models index))

noncomputable def code : Finset (Carrier models) × Carrier models → Option (Carrier models)
  | (support, ⟨index, output⟩) =>
      if support = (projection models index support).map (embedding models index) then
        some (embedding models index ((models index).code (projection models index support) output))
      else none

theorem code_some_iff (index : Index) (support : Finset (Carrier models))
    (output : (models index).Carrier) (token : Carrier models) :
    code models (support, embedding models index output) = some token ↔
      support = (projection models index support).map (embedding models index) ∧
      embedding models index ((models index).code (projection models index support) output) =
        token := by
  classical
  change (if support = (projection models index support).map (embedding models index) then
    some (embedding models index ((models index).code (projection models index support) output))
    else none) = some token ↔ _
  split
  · rename_i pure
    exact ⟨fun h => ⟨pure, Option.some.inj h⟩, fun h => congrArg some h.2⟩
  · rename_i mixed
    constructor
    · intro impossible; cases impossible
    · intro supplied; exact False.elim (mixed supplied.1)

theorem code_preserves (index : Index) (support : Finset (models index).Carrier)
    (output : (models index).Carrier) :
    code models (support.map (embedding models index), embedding models index output) =
      some (embedding models index ((models index).code support output)) := by
  apply (code_some_iff models index _ _ _).mpr
  simp only [projection_map, and_self]

theorem code_injective
    {first second : Finset (Carrier models) × Carrier models} {token : Carrier models}
    (firstDefined : code models first = some token)
    (secondDefined : code models second = some token) : first = second := by
  rcases first with ⟨firstSupport, ⟨firstIndex, firstOutput⟩⟩
  rcases second with ⟨secondSupport, ⟨secondIndex, secondOutput⟩⟩
  obtain ⟨firstTwoSort, firstCode⟩ :=
    (code_some_iff models firstIndex firstSupport firstOutput token).mp firstDefined
  obtain ⟨secondTwoSort, secondCode⟩ :=
    (code_some_iff models secondIndex secondSupport secondOutput token).mp secondDefined
  have sameIndex : firstIndex = secondIndex := congrArg Sigma.fst (firstCode.trans secondCode.symm)
  subst secondIndex
  have sameInputs := (models firstIndex).coding.injective
    ((embedding models firstIndex).injective (firstCode.trans secondCode.symm))
  obtain ⟨sameSupport, sameOutput⟩ := Prod.ext_iff.mp sameInputs
  exact Prod.ext
    (firstTwoSort.trans ((congrArg (Finset.map (embedding models firstIndex)) sameSupport).trans
      secondTwoSort.symm))
    (congrArg (embedding models firstIndex) sameOutput)

/-- One inhabited index supplies an infinite factor. Empty families are not
silently supplied with a replacement web. -/
noncomputable def partialPair [Nonempty Index] : PartialPair where
  web := {
    carrier := Carrier models
    decEq := inferInstance
    infinite := Infinite.of_injective (embedding models (Classical.choice ‹Nonempty Index›))
      (embedding models (Classical.choice ‹Nonempty Index›)).injective
  }
  coding := {
    code := code models
    injective := code_injective models
  }

theorem code_reflects (index : Index) (support : Finset (Carrier models))
    (output : Carrier models) (token : (models index).Carrier) :
    code models (support, output) = some (embedding models index token) ↔
      ∃ (factorSupport : Finset (models index).Carrier) (factorOutput : (models index).Carrier),
        (models index).code factorSupport factorOutput = token ∧
        support = factorSupport.map (embedding models index) ∧
        output = embedding models index factorOutput := by
  constructor
  · intro defined
    rcases output with ⟨otherIndex, otherOutput⟩
    obtain ⟨pure, coded⟩ :=
      (code_some_iff models otherIndex support otherOutput _).mp defined
    have sameIndex : otherIndex = index := congrArg Sigma.fst coded
    subst otherIndex
    exact ⟨projection models index support, otherOutput,
      (embedding models index).injective coded, pure, rfl⟩
  · rintro ⟨factorSupport, factorOutput, rfl, rfl, rfl⟩
    exact code_preserves models index factorSupport factorOutput

def factorEmbedding [Nonempty Index] (index : Index) :
    FactorEmbedding (partialPair models) (models index) where
  embedding := embedding models index
  code_eq_factor_iff := code_reflects models index
  output_isolation support output token defined inFactor := by
    obtain ⟨value, rfl⟩ := inFactor
    obtain ⟨_, coded⟩ := (code_some_iff models index support value token).mp defined
    exact ⟨(models index).code (projection models index support) value, coded⟩

theorem code_undefined_of_other_mem (index otherIndex : Index) (different : otherIndex ≠ index)
    (support : Finset (Carrier models)) (output : (models index).Carrier)
    (other : (models otherIndex).Carrier) (present : embedding models otherIndex other ∈ support) :
    code models (support, embedding models index output) = none := by
  have notPure : support ≠ (projection models index support).map (embedding models index) := by
    intro pure
    have selected := present
    rw [pure] at selected
    obtain ⟨value, _, equal⟩ := Finset.mem_map.mp selected
    exact different (congrArg Sigma.fst equal).symm
  exact if_neg notPure

/-- The existing completion/interpreter argument applies to every selected
factor without another term induction. -/
theorem completion_theory_lower_bound [Nonempty Index] (index : Index) :
    lambdaTheoryOf (Completion.graphModel (partialPair models)) ≤ lambdaTheoryOf (models index) :=
  FactorInterpretation.theory_subset_factor (factorEmbedding models index)

end Mettapedia.GSLT.GraphTheory.PartialPair.IndexedFamily

namespace Mettapedia.GSLT.GraphTheory

open Mettapedia.GSLT.Core PartialPair

/-- Every nonempty indexed family of graph theories has a graph-theory lower
bound. The witness is the actual canonical completion of the selected model
family; this does not identify its theory with the family's intersection. -/
theorem graphTheories_lower_bound {Index : Type} [Nonempty Index]
    (theories : Index → LambdaTheory) (graph : ∀ index, IsGraphTheory (theories index)) :
    ∃ lower : LambdaTheory, IsGraphTheory lower ∧ ∀ index, lower ≤ theories index := by
  classical
  choose models presents using graph
  refine ⟨lambdaTheoryOf (Completion.graphModel (IndexedFamily.partialPair models)),
    lambdaTheoryOf_isGraphTheory _, ?_⟩
  intro index
  have lower := IndexedFamily.completion_theory_lower_bound models index
  intro equation member
  rw [presents index]
  exact lower member

end Mettapedia.GSLT.GraphTheory
