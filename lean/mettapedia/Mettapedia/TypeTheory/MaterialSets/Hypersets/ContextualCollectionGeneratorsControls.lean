import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedCollectionGenerators
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualBoundedCollectionControls
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWitnessCoverControls

/-!
# Collection receipts retain source history and advancing payloads

The generated growing material family supplies a bounded Collection square
for a genuinely non-small cover. An infinite-loop instance supplies the
full generator square constructively from bounded zero receipts, despite
the absence of compatible witness sections. Different source/terminal
factorizations with the same parameter retain different material readings.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCollectionGeneratorsControls

open _root_.CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover ContextualImageFactorization
open ContextualCoherentSmallMaps

namespace Growing

open ContextualGeneratedUniverse.Growing ContextualBoundedCollectionControls

theorem generated_wider_collection :
    Cover (ContextualCollectionGenerators.parameterMap operation wideCover) ∧
      Cover (ContextualCollectionGenerators.comparison operation wideCover) ∧
      SmallFibres (ContextualCollectionGenerators.collectedMap operation wideCover) ∧
      (ContextualCollectionGenerators.top operation wideCover).comp (wideCover.comp operation) =
        (ContextualCollectionGenerators.collectedMap operation wideCover).comp
          (ContextualCollectionGenerators.parameterMap operation wideCover) :=
  ContextualGeneratedCollectionGenerators.wider_bounded_collection input operation wideCover
    unitCandidate cyclicReading bounded_cyclic_total

end Growing

namespace Advancing

open ContextualSeparationCollectionControls.Advancing
open ContextualWitnessCoverControls.Advancing

abbrev Worlds := context.{0}.base.Elements
abbrev parameters := terminal (E := Worlds)

def operation : NaturalHom parameters parameters := ContextualSmallMapConstructions.identity parameters

def cover : NaturalHom wide.{0} parameters where
  app _ _ := PUnit.unit
  naturality _ _ := rfl

theorem cover_onto : Cover cover := by
  intro atPoint value
  exact ⟨zeroWitness atPoint, Subsingleton.elim (α := PUnit) _ _⟩

def generator (atPoint : Worlds) (value : parameters.obj atPoint) :
    ContextualCollectionGenerators.Generator operation cover where
  point := atPoint
  parameter := value
  enumerations := (identityData parameters).futureEnumerations atPoint value
  witnessCarrier _ _ := PUnit
  witness future _ _ := ⟨zeroWitness future.1, Subsingleton.elim (α := PUnit) _ _⟩
  inhabited _ _ := ⟨PUnit.unit⟩

theorem generators_exist : ∀ atPoint (value : parameters.obj atPoint),
    ∃ receipt : ContextualCollectionGenerators.Generator operation cover,
      receipt.point = atPoint ∧ HEq receipt.parameter value :=
  fun atPoint value => ⟨generator atPoint value, rfl, HEq.rfl⟩

theorem constructive_collection :
    Cover (ContextualCollectionGenerators.parameterMap operation cover) ∧
      Cover (ContextualCollectionGenerators.comparison operation cover) ∧
      SmallFibres (ContextualCollectionGenerators.collectedMap operation cover) ∧
      (ContextualCollectionGenerators.top operation cover).comp (cover.comp operation) =
        (ContextualCollectionGenerators.collectedMap operation cover).comp
          (ContextualCollectionGenerators.parameterMap operation cover) :=
  ContextualCollectionGenerators.full_diagram operation cover generators_exist

def receipt (number : Nat) : (ContextualCollectionGenerators.collected operation cover).obj point :=
  ⟨generator point PUnit.unit, ⟨point, 𝟙 point⟩, loop point number, PUnit.unit, PUnit.unit⟩

def movedReceipt (number : Nat) : (ContextualCollectionGenerators.collected operation cover).obj point :=
  ⟨generator point PUnit.unit, ⟨point, loop point number⟩, 𝟙 point, PUnit.unit, PUnit.unit⟩

theorem receipt_reading (number : Nat) :
    ((ContextualCollectionGenerators.top operation cover).app point (receipt number)).val =
      NaturalOrdinalModel.ordinal number := advance_zero_ordinal number

theorem moved_receipt_reading (number : Nat) :
    ((ContextualCollectionGenerators.top operation cover).app point (movedReceipt number)).val = ∅ := by
  change (advance 0 (zeroWitness point)).val = ∅
  rfl

theorem same_parameter_different_history (number : Nat) :
    (ContextualCollectionGenerators.collectedMap operation cover).app point (receipt number) =
      (ContextualCollectionGenerators.collectedMap operation cover).app point (movedReceipt number) :=
  congrArg (Sigma.mk (generator point PUnit.unit))
    ((Category.id_comp (loop point number)).trans (Category.comp_id (loop point number)).symm)

theorem readings_differ :
    ((ContextualCollectionGenerators.top operation cover).app point (receipt 1)).val ≠
      ((ContextualCollectionGenerators.top operation cover).app point (movedReceipt 1)).val := by
  rw [receipt_reading, moved_receipt_reading]
  intro same
  have zero := NaturalOrdinalModel.ordinal_zero
  have numbers : 1 = 0 := NaturalOrdinalModel.ordinal_injective (same.trans zero.symm)
  exact Nat.one_ne_zero numbers

theorem top_does_not_factor_through_parameter :
    ¬ ∃ reading : NaturalHom (ContextualCollectionGenerators.parameters operation cover) wide,
      (ContextualCollectionGenerators.collectedMap operation cover).comp reading =
        ContextualCollectionGenerators.top operation cover := by
  rintro ⟨reading, factors⟩
  have first := congrArg (fun map => (map.app point (receipt 1)).val) factors
  have second := congrArg (fun map => (map.app point (movedReceipt 1)).val) factors
  exact readings_differ (first.symm.trans
    ((congrArg (fun value => (reading.app point value).val) (same_parameter_different_history 1)).trans second))

theorem collected_has_no_compatible_section :
    ¬ Nonempty (ContextualCollectionGenerators.collected operation cover).sections := by
  rintro ⟨term⟩
  exact no_wide_section ⟨(ContextualCollectionGenerators.top operation cover).mapSection term⟩

theorem cover_has_no_natural_splitting :
    ¬ ∃ selected : NaturalHom parameters wide,
      selected.comp cover = ContextualSmallMapConstructions.identity parameters := by
  rintro ⟨selected, _⟩
  exact no_wide_section ⟨selected.mapSection terminalSection⟩

end Advancing

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCollectionGeneratorsControls
