import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedWitnessCollection
import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerControls

/-!
# Bounded Collection controls over a growing material family

The source is the interpreted growing observed family. The covering map
adds an arbitrary original hyperset, and therefore has genuinely wider
fibres. A retained unit witness supplies a cyclic receipt and constructs
the bounded square. A second natural reading misses the new cyclic
argument even though the same wider covering map is surjective.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualBoundedCollectionControls

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover ContextualImageFactorization
open ContextualCoherentSmallMaps ContextualGeneratedUniverse
open ContextualGeneratedUniverse.Growing

universe u v

def materialReceipts {D : Type u} [Category.{u} D] (family : D ⥤ Type v) :
    D ⥤ Type (max v (u + 1)) where
  obj point := family.obj point × HSet.{u}
  map step := TypeCat.ofHom fun receipt => (family.map step receipt.1, receipt.2)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact Prod.ext (family.map_id_apply point receipt.1) rfl
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact Prod.ext (family.map_comp_apply earlier later receipt.1) rfl

abbrev sourceFamily := (ContextualGeneratedMaterialClassification.dictionaryBare input).source

def parameters : context.base.Elements ⥤ Type where
  obj _ := PUnit
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def operation : NaturalHom sourceFamily parameters where
  app _ _ := PUnit.unit
  naturality _ _ := rfl

abbrev widerReceipts := materialReceipts sourceFamily

def wideCover : NaturalHom widerReceipts sourceFamily where
  app _ := Prod.fst
  naturality _ _ := rfl

theorem wideCover_onto : Cover wideCover := fun _ member => ⟨(member, ∅), rfl⟩

theorem wide_fibre_has_no_original_cover (point : context.base.Elements) (member : sourceFamily.obj point) :
    ¬ Nonempty (Enumeration.{0, 1} (Fibre wideCover point member)) := by
  rintro ⟨enumeration⟩
  apply CoveredFuturePowerControls.hset_has_no_small_cover (fun code => (enumeration.value code).val.2)
  intro value
  obtain ⟨code, same⟩ := enumeration.covered (⟨(member, value), rfl⟩ : Fibre wideCover point member)
  exact ⟨code, congrArg (fun receipt : Fibre wideCover point member => receipt.val.2) same⟩

abbrev unitCandidate := MaterialFamily.unit context
abbrev witnesses := ContextualGeneratedWitnessCollection.witnessFamily input unitCandidate

def cyclicReading : NaturalHom (ContextualSmallFamilyUniverse.total witnesses) widerReceipts where
  app _ witness := (witness.1, HSet.quineAtom)
  naturality _ _ := rfl

theorem bounded_cyclic_total : ContextualBoundedCollection.BoundedTotal wideCover witnesses cyclicReading :=
  fun _ _ => ⟨⟨PUnit.unit⟩, rfl⟩

def collectedModel : Data (ContextualBoundedCollection.collectedMap operation wideCover witnesses cyclicReading) :=
  ContextualGeneratedWitnessCollection.collectedData input operation wideCover unitCandidate cyclicReading

theorem cyclic_quasi_pullback : Cover
    (ContextualBoundedCollection.comparison operation wideCover witnesses cyclicReading) :=
  (ContextualBoundedCollection.comparison_cover_iff operation wideCover witnesses cyclicReading).mpr
    bounded_cyclic_total

theorem collected_map_small : SmallFibres
    (ContextualBoundedCollection.collectedMap operation wideCover witnesses cyclicReading) :=
  collectedModel.smallFibres

theorem every_top_payload_cyclic (point : context.base.Elements)
    (witness : (ContextualBoundedCollection.witnessObject wideCover witnesses cyclicReading).obj point) :
    ((ContextualBoundedCollection.top wideCover witnesses cyclicReading).app point witness).2 = HSet.quineAtom := rfl

def emptyMemberSection : sourceFamily.sections :=
  (ContextualGeneratedMaterialClassification.encode input).mapSection emptySection

def missingReading : NaturalHom (ContextualSmallFamilyUniverse.total witnesses) widerReceipts where
  app point _ := (emptyMemberSection.val point, HSet.quineAtom)
  naturality step _ := Prod.ext (emptyMemberSection.property step) rfl

def cyclicArgument : sourceFamily.obj later :=
  (ContextualGeneratedMaterialClassification.encode input).app later
    PowerClassContextualMaterialization.Growing.futureArgument

theorem cyclicArgument_value : cyclicArgument.val = HSet.quineAtom := cyclic_leaf_shape

theorem emptyMemberSection_later : (emptyMemberSection.val later).val = ∅ :=
  emptySection_value Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.laterRaw

theorem bounded_reading_misses_argument (witness : witnesses.obj ⟨later, cyclicArgument⟩) :
    ¬ ContextualBoundedCollection.WitnessPredicate wideCover witnesses missingReading
      ⟨later, cyclicArgument⟩ witness := by
  intro same
  have values := congrArg Subtype.val same
  exact HSet.empty_ne_quineAtom
    (emptyMemberSection_later.symm.trans (values.trans cyclicArgument_value))

theorem cover_does_not_make_this_bound_total :
    ¬ ContextualBoundedCollection.BoundedTotal wideCover witnesses missingReading := by
  intro total
  obtain ⟨witness, valid⟩ := total later cyclicArgument
  exact bounded_reading_misses_argument witness valid

theorem missing_comparison_not_cover :
    ¬ Cover (ContextualBoundedCollection.comparison operation wideCover witnesses missingReading) :=
  fun covered => cover_does_not_make_this_bound_total
    ((ContextualBoundedCollection.comparison_cover_iff operation wideCover witnesses missingReading).mp covered)

/-- The old/future member distinction survives in the source and in the
positive square's retained witness coordinate. -/
theorem source_genuinely_nonconstant :
    (emptyMemberSection.val old).val ≠ cyclicArgument.val := by
  have emptyOld := emptySection_value Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.oldRaw
  rw [cyclicArgument_value]
  exact emptyOld.trans_ne HSet.empty_ne_quineAtom

theorem old_members_empty (member : sourceFamily.obj old) : member.val = ∅ :=
  (ContextualGeneratedMaterialClassification.decode_value input old member).symm.trans
    ((input_value old _).trans
      (Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.currentArgument_value
        ((ContextualGeneratedMaterialClassification.decode input).app old member)))

theorem old_fibre_has_no_cyclic_argument (member : sourceFamily.obj old) : member.val ≠ HSet.quineAtom :=
  (old_members_empty member).trans_ne HSet.empty_ne_quineAtom

def widerParameterChange : NaturalHom widerReceipts parameters := wideCover.comp operation

theorem substituted_cyclic_comparison_cover : Cover
    (ContextualBoundedCollection.comparisonUnder operation wideCover witnesses cyclicReading widerParameterChange) :=
  ContextualBoundedCollection.comparisonUnder_cover operation wideCover witnesses cyclicReading
    widerParameterChange bounded_cyclic_total

theorem substitution_retains_wider_parameter (point : context.base.Elements)
    (receipt : (ContextualBoundedCollection.witnessUnder operation wideCover witnesses cyclicReading
      widerParameterChange).obj point) :
    ((ContextualBoundedCollection.comparisonUnder operation wideCover witnesses cyclicReading
      widerParameterChange).app point receipt).val.2 = receipt.val.2 := rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualBoundedCollectionControls
