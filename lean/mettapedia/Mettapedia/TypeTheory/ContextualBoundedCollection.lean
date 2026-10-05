import Mettapedia.TypeTheory.ContextualCoherentSmallMaps

/-!
# Bounded witness Collection for coherent contextual small maps

Potential witnesses form an actual small displayed family. Their natural
reading need not initially satisfy the cover equation. Filtering by that
equation constructs the witness object, its map to the given cover, and a
small composite map. Totality within this retained bound is exactly the
pointwise covering property of the quasi-pullback comparison.

The parameter cover in this square is the identity. An arbitrary wider
cover does not by itself supply the small witness family or prove bounded
totality. Pulling the constructed square along a parameter map preserves
its genuine covering comparison and constructed small fibres.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualBoundedCollection

open CategoryTheory ContextualWitnessCover ContextualImageFactorization
open ContextualCoherentSmallMaps

universe u v w z t s
variable {D : Type u} [Category.{u} D]
variable {X : D ⥤ Type v} {A : D ⥤ Type w} {Y : D ⥤ Type z}
variable (operation : NaturalHom X A) (model : Data operation)
variable (cover : NaturalHom Y X) (witnesses : X.Elements ⥤ Type u)
variable (reading : NaturalHom (ContextualSmallFamilyUniverse.total witnesses) Y)

def WitnessPredicate (point : X.Elements) (witness : witnesses.obj point) : Prop :=
  cover.app point.1 (reading.app point.1 ⟨point.2, witness⟩) = point.2

theorem witnessPredicate_closed {first second : X.Elements} (step : first ⟶ second)
    (witness : witnesses.obj first) (valid : WitnessPredicate cover witnesses reading first witness) :
    WitnessPredicate cover witnesses reading second (witnesses.map step witness) := by
  rcases first with ⟨first, argument⟩
  rcases second with ⟨second, nextArgument⟩
  rcases step with ⟨step, follows⟩
  change first ⟶ second at step
  change X.map step argument = nextArgument at follows
  subst nextArgument
  change cover.app second (reading.app second
    (ContextualSmallFamilyUniverse.totalMap witnesses step ⟨argument, witness⟩)) = X.map step argument
  exact ((congrArg (cover.app second) (reading.naturality step ⟨argument, witness⟩).symm).trans
    (cover.naturality step (reading.app first ⟨argument, witness⟩)).symm).trans
      (congrArg (X.map step) valid)

def goodWitnesses : X.Elements ⥤ Type u where
  obj point := {witness : witnesses.obj point // WitnessPredicate cover witnesses reading point witness}
  map step := TypeCat.ofHom fun witness =>
    ⟨witnesses.map step witness.val, witnessPredicate_closed cover witnesses reading step witness.val witness.property⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro witness
    exact Subtype.ext (witnesses.map_id_apply point witness.val)
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro witness
    exact Subtype.ext (witnesses.map_comp_apply earlier later witness.val)

abbrev witnessObject := ContextualSmallFamilyUniverse.total (goodWitnesses cover witnesses reading)

def inclusion : NaturalHom (witnessObject cover witnesses reading)
    (ContextualSmallFamilyUniverse.total witnesses) where
  app _ witness := ⟨witness.1, witness.2.val⟩
  naturality _ _ := rfl

def top : NaturalHom (witnessObject cover witnesses reading) Y :=
  (inclusion cover witnesses reading).comp reading

def source : NaturalHom (witnessObject cover witnesses reading) X :=
  ContextualSmallFamilyUniverse.projection (goodWitnesses cover witnesses reading)

def collectedMap : NaturalHom (witnessObject cover witnesses reading) A :=
  (source cover witnesses reading).comp operation

theorem top_cover : (top cover witnesses reading).comp cover = source cover witnesses reading := by
  apply NaturalHom.ext
  intro point witness
  exact witness.2.property

theorem collection_square : (top cover witnesses reading).comp (cover.comp operation) =
    collectedMap operation cover witnesses reading := by
  apply NaturalHom.ext
  intro point witness
  exact congrArg (operation.app point) witness.2.property

/-- The resulting small fibre is the dependent sum of a retained decoded
original argument and one valid witness over that actual argument. -/
def collectedData : Data (collectedMap operation cover witnesses reading) :=
  composeData (source cover witnesses reading) operation
    (projectionData (goodWitnesses cover witnesses reading)) model

abbrev CollectedFibre (point : A.Elements) : Type u :=
  Σ argument : model.family.obj point,
    (goodWitnesses cover witnesses reading).obj ⟨point.1, (model.decoder point argument).val⟩

theorem collectedData_fibre (point : A.Elements) :
    (collectedData operation model cover witnesses reading).family.obj point =
      CollectedFibre operation model cover witnesses reading point := rfl

theorem collectedData_value (point : A.Elements)
    (witness : CollectedFibre operation model cover witnesses reading point) :
    ((collectedData operation model cover witnesses reading).decoder point witness).val =
      ⟨(model.decoder point witness.1).val, witness.2⟩ := rfl

def comparison : NaturalHom (witnessObject cover witnesses reading)
    (pullback operation (ContextualSmallMapConstructions.identity A)) :=
  pullbackPair operation (ContextualSmallMapConstructions.identity A)
    (source cover witnesses reading) (collectedMap operation cover witnesses reading) (by
      apply NaturalHom.ext
      intro _ _
      rfl)

def BoundedTotal : Prop := ∀ point (argument : X.obj point),
  ∃ witness : witnesses.obj ⟨point, argument⟩,
    WitnessPredicate cover witnesses reading ⟨point, argument⟩ witness

theorem source_cover_iff : Cover (source cover witnesses reading) ↔ BoundedTotal cover witnesses reading := by
  constructor
  · intro covered point argument
    obtain ⟨⟨other, witness⟩, same⟩ := covered point argument
    change other = argument at same
    subst argument
    exact ⟨witness.val, witness.property⟩
  · intro total point argument
    obtain ⟨witness, valid⟩ := total point argument
    exact ⟨⟨argument, ⟨witness, valid⟩⟩, rfl⟩

theorem comparison_cover_iff : Cover (comparison operation cover witnesses reading) ↔
    BoundedTotal cover witnesses reading := by
  constructor
  · intro covered point argument
    obtain ⟨⟨other, witness⟩, same⟩ := covered point
      (⟨(argument, operation.app point argument), rfl⟩ :
        (pullback operation (ContextualSmallMapConstructions.identity A)).obj point)
    have argumentLaw := congrArg (fun value => value.val.1) same
    change other = argument at argumentLaw
    subst argument
    exact ⟨witness.val, witness.property⟩
  · intro total point receipt
    obtain ⟨witness, valid⟩ := total point receipt.val.1
    exact ⟨⟨receipt.val.1, ⟨witness, valid⟩⟩, Subtype.ext (Prod.ext rfl receipt.property)⟩

include model in
theorem bounded_collection (total : BoundedTotal cover witnesses reading) :
    Cover (ContextualSmallMapConstructions.identity A) ∧
      Cover (comparison operation cover witnesses reading) ∧
      SmallFibres (collectedMap operation cover witnesses reading) ∧
      (top cover witnesses reading).comp (cover.comp operation) =
        collectedMap operation cover witnesses reading :=
  ⟨cover_identity A, (comparison_cover_iff operation cover witnesses reading).mpr total,
    (collectedData operation model cover witnesses reading).smallFibres,
    collection_square operation cover witnesses reading⟩

theorem bounded_total_implies_cover (total : BoundedTotal cover witnesses reading) : Cover cover := by
  intro point argument
  obtain ⟨witness, valid⟩ := total point argument
  exact ⟨reading.app point ⟨argument, witness⟩, valid⟩

section ParameterSubstitution

variable {B : D ⥤ Type t} (change : NaturalHom B A)

abbrev witnessUnder := pullback (collectedMap operation cover witnesses reading) change
abbrev originalUnder := pullback operation change
abbrev coverUnder := pullback (cover.comp operation) change

def topUnder : NaturalHom (witnessUnder operation cover witnesses reading change)
    (coverUnder operation cover change) where
  app point witness := ⟨((top cover witnesses reading).app point witness.val.1, witness.val.2),
    (congrArg (fun map => map.app point witness.val.1)
      (collection_square operation cover witnesses reading)).trans witness.property⟩
  naturality step witness := Subtype.ext (Prod.ext ((top cover witnesses reading).naturality step witness.val.1) rfl)

def comparisonUnder : NaturalHom (witnessUnder operation cover witnesses reading change)
    (originalUnder operation change) where
  app _ witness := ⟨((source cover witnesses reading).app _ witness.val.1, witness.val.2), witness.property⟩
  naturality _ _ := rfl

def coverUnderMap : NaturalHom (coverUnder operation cover change) (originalUnder operation change) where
  app point witness := ⟨(cover.app point witness.val.1, witness.val.2), witness.property⟩
  naturality step witness := Subtype.ext (Prod.ext (cover.naturality step witness.val.1) rfl)

theorem substituted_top_cover : (topUnder operation cover witnesses reading change).comp
    (coverUnderMap operation cover change) = comparisonUnder operation cover witnesses reading change := by
  apply NaturalHom.ext
  intro point witness
  exact Subtype.ext (Prod.ext witness.val.1.2.property rfl)

theorem substituted_parameter_square :
    (comparisonUnder operation cover witnesses reading change).comp (pullbackSecond operation change) =
      pullbackSecond (collectedMap operation cover witnesses reading) change := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem comparisonUnder_cover (total : BoundedTotal cover witnesses reading) :
    Cover (comparisonUnder operation cover witnesses reading change) := by
  intro point receipt
  obtain ⟨witness, valid⟩ := total point receipt.val.1
  exact ⟨⟨(⟨receipt.val.1, ⟨witness, valid⟩⟩, receipt.val.2), receipt.property⟩, Subtype.ext rfl⟩

def collectedDataUnder : Data (pullbackSecond (collectedMap operation cover witnesses reading) change) :=
  pullbackData _ (collectedData operation model cover witnesses reading) change

theorem collectedDataUnder_family : (collectedDataUnder operation model cover witnesses reading change).family =
    ContextualSmallFamilyUniverse.substitutedFamily
      (collectedData operation model cover witnesses reading).family change := rfl

theorem collectedDataUnder_identity :
    (collectedDataUnder operation model cover witnesses reading (ContextualSmallMapConstructions.identity A)).family =
      (collectedData operation model cover witnesses reading).family :=
  pullbackData_identity_family _ _

theorem collectedDataUnder_composite {F : D ⥤ Type s} (earlier : NaturalHom F B) :
    (collectedDataUnder operation model cover witnesses reading (earlier.comp change)).family =
      ContextualSmallFamilyUniverse.substitutedFamily
        (collectedDataUnder operation model cover witnesses reading change).family earlier :=
  pullbackData_composite_family _ _ change earlier

end ParameterSubstitution

end Mettapedia.TypeTheory.ContextualBoundedCollection
