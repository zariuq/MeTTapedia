import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceMaterialCoalgebraFinality
import Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedSmallCoalgebraRecipient
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSliceRecipient
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Indexed final coalgebras for the optional host-Choice profile

The indexed covered-power operation is an actual endofunctor on the actual
over category of ambient argument families. Its coalgebras retain their
parameter, and every child lies over that parameter transported along the
same future arrow. The raw and material recipients are independently built
coalgebras of this endofunctor, with actual terminal universal properties.

Only the optional external host Choice operation supplies uniform branch
enumerations from covers. The original receipt bound remains `u`, while
ambient arguments and parameters have level `max (u+1) v`. No selection of
raw representatives, constructive Collection, or native foundation is inferred.
The common Mathlib over-category interface also carries host Choice in its
transitive dependency manifest, including the indexed endofunctor wrapper.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceIndexedCoalgebraFinality

open _root_.CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open Mettapedia.TypeTheory.ContextualWitnessCover

universe u v w t
variable {D : Type u} [Category.{u} D]

/-- Indexed power is constructed on actual slice objects and commuting maps. -/
def indexedPower (B : HostChoiceContextualCoalgebraFinality.Ambient.{u,v} D) :
    Over B ⥤ Over B where
  obj source := Over.mk (Y := (⟨IndexedCoveredPower.family source.hom⟩ :
    HostChoiceContextualCoalgebraFinality.Ambient.{u,v} D))
      (IndexedCoveredPower.projection source.hom)
  map {source target} operation := Over.homMk
    (IndexedCoveredPower.image source.hom target.hom operation.left operation.w)
      (IndexedCoveredPower.image_projection source.hom target.hom operation.left operation.w)
  map_id source := by
    apply Over.OverMorphism.ext
    exact IndexedCoveredPower.image_identity source.hom
  map_comp {first middle last} earlier later := by
    apply Over.OverMorphism.ext
    exact IndexedCoveredPower.image_comp first.hom middle.hom last.hom
      earlier.left later.left earlier.w later.w (earlier ≫ later).w

/-- The indexed square contains the entire ordinary future-predicate image square. -/
theorem indexed_square_original {A : D ⥤ Type w} {B : D ⥤ Type t} {F : D ⥤ Type v}
    (sourceParameter : NaturalHom A B) (targetParameter : NaturalHom F B)
    (source : NaturalHom A (IndexedCoveredPower.family sourceParameter))
    (target : NaturalHom F (IndexedCoveredPower.family targetParameter))
    (operation : NaturalHom A F) (overBase : operation.comp targetParameter = sourceParameter)
    (square : source.comp (IndexedCoveredPower.image sourceParameter targetParameter operation overBase) =
      operation.comp target) :
    (IndexedCoalgebraBisimulation.original sourceParameter source).comp (imageHom operation) =
      operation.comp (IndexedCoalgebraBisimulation.original targetParameter target) := by
  apply NaturalHom.ext
  intro point value
  exact congrArg (fun map : NaturalHom A (IndexedCoveredPower.family targetParameter) =>
    (map.app point value).val.2) square

section ArbitraryWidth

variable (B : D ⥤ Type v) {A : D ⥤ Type w} (parameter : NaturalHom A B)
variable (transition : NaturalHom A (IndexedCoveredPower.family parameter))
variable (sourceSquare : transition.comp (IndexedCoveredPower.projection parameter) = parameter)

noncomputable def rawReadout : NaturalHom A (IndexedSmallCoalgebraRecipient.family B) :=
  IndexedSmallCoalgebraRecipient.fromEnumerated B parameter transition
    (HostChoiceContextualCoalgebraFinality.enumerations
      (IndexedCoalgebraBisimulation.original parameter transition))

include sourceSquare in
theorem rawReadout_square :
    transition.comp (IndexedCoveredPower.image parameter (IndexedSmallCoalgebraRecipient.parameter B)
      (rawReadout B parameter transition)
      (IndexedSmallCoalgebraRecipient.pairReadout_parameter B parameter
        (HostChoiceContextualCoalgebraFinality.readout
          (IndexedCoalgebraBisimulation.original parameter transition)))) =
      (rawReadout B parameter transition).comp (IndexedSmallCoalgebraRecipient.indexedCoalgebra B) :=
  IndexedSmallCoalgebraRecipient.paired_indexed_square B parameter transition sourceSquare
    (HostChoiceContextualCoalgebraFinality.readout
      (IndexedCoalgebraBisimulation.original parameter transition))
    (HostChoiceContextualCoalgebraFinality.readout_square
      (IndexedCoalgebraBisimulation.original parameter transition))

theorem rawReadout_parameter : (rawReadout B parameter transition).comp
    (IndexedSmallCoalgebraRecipient.parameter B) = parameter :=
  IndexedSmallCoalgebraRecipient.pairReadout_parameter B parameter
    (HostChoiceContextualCoalgebraFinality.readout
      (IndexedCoalgebraBisimulation.original parameter transition))

include sourceSquare in
theorem unique_rawReadout : ∃! operation : NaturalHom A (IndexedSmallCoalgebraRecipient.family B),
    (IndexedCoalgebraBisimulation.original parameter transition).comp (imageHom operation) =
      operation.comp (IndexedSmallCoalgebraRecipient.coalgebra B) ∧
    operation.comp (IndexedSmallCoalgebraRecipient.parameter B) = parameter :=
  IndexedSmallCoalgebraRecipient.unique_enumerated B parameter transition sourceSquare
    (HostChoiceContextualCoalgebraFinality.enumerations
      (IndexedCoalgebraBisimulation.original parameter transition))

theorem rawReadout_kernel (point : D) (first second : A.obj point) :
    (rawReadout B parameter transition).app point first =
        (rawReadout B parameter transition).app point second ↔
      IndexedCoalgebraBisimulation.Related parameter transition point first second :=
  IndexedSmallCoalgebraRecipient.enumerated_kernel B parameter transition
    (HostChoiceContextualCoalgebraFinality.enumerations
      (IndexedCoalgebraBisimulation.original parameter transition)) point first second

theorem rawReadout_independent
    (authored : ∀ point value,
      Enumeration ((IndexedCoalgebraBisimulation.original parameter transition).app point value).val) :
    rawReadout B parameter transition =
      IndexedSmallCoalgebraRecipient.fromEnumerated B parameter transition authored :=
  congrArg (IndexedSmallCoalgebraRecipient.pairReadout B parameter)
    (HostChoiceContextualCoalgebraFinality.readout_independent
      (IndexedCoalgebraBisimulation.original parameter transition) authored)

variable (worlds : ArgumentCoding D)
variable (arrows : (first second : D) → ArgumentCoding (first ⟶ second))

noncomputable def materialReadout :
    NaturalHom A (ContextualMaterialSliceRecipient.family worlds arrows B) :=
  ContextualMaterialSliceRecipient.fromEnumerated worlds arrows B parameter transition
    (HostChoiceContextualCoalgebraFinality.enumerations
      (IndexedCoalgebraBisimulation.original parameter transition))

theorem materialReadout_parameter : (materialReadout B parameter transition worlds arrows).comp
    (ContextualMaterialSliceRecipient.parameter worlds arrows B) = parameter :=
  ContextualMaterialSliceRecipient.fromEnumerated_parameter worlds arrows B parameter transition
    (HostChoiceContextualCoalgebraFinality.enumerations
      (IndexedCoalgebraBisimulation.original parameter transition))

include sourceSquare in
theorem materialReadout_square :
    transition.comp (IndexedCoveredPower.image parameter
      (ContextualMaterialSliceRecipient.parameter worlds arrows B)
      (materialReadout B parameter transition worlds arrows)
      (materialReadout_parameter B parameter transition worlds arrows)) =
      (materialReadout B parameter transition worlds arrows).comp
        (ContextualMaterialSliceRecipient.indexedCoalgebra worlds arrows B) :=
  ContextualMaterialSliceRecipient.paired_indexed_square worlds arrows B parameter transition sourceSquare
    (HostChoiceMaterialCoalgebraFinality.readout worlds arrows
      (IndexedCoalgebraBisimulation.original parameter transition))
    (HostChoiceMaterialCoalgebraFinality.readout_square worlds arrows
      (IndexedCoalgebraBisimulation.original parameter transition))

include sourceSquare in
theorem unique_materialReadout :
    ∃! operation : NaturalHom A (ContextualMaterialSliceRecipient.family worlds arrows B),
      (IndexedCoalgebraBisimulation.original parameter transition).comp (imageHom operation) =
        operation.comp (ContextualMaterialSliceRecipient.coalgebra worlds arrows B) ∧
      operation.comp (ContextualMaterialSliceRecipient.parameter worlds arrows B) = parameter :=
  ContextualMaterialSliceRecipient.unique_enumerated worlds arrows B parameter transition sourceSquare
    (HostChoiceContextualCoalgebraFinality.enumerations
      (IndexedCoalgebraBisimulation.original parameter transition))

theorem materialReadout_kernel (point : D) (first second : A.obj point) :
    (materialReadout B parameter transition worlds arrows).app point first =
        (materialReadout B parameter transition worlds arrows).app point second ↔
      IndexedCoalgebraBisimulation.Related parameter transition point first second :=
  ContextualMaterialSliceRecipient.enumerated_kernel worlds arrows B parameter transition
    (HostChoiceContextualCoalgebraFinality.enumerations
      (IndexedCoalgebraBisimulation.original parameter transition)) point first second

theorem materialReadout_independent
    (authored : ∀ point value,
      Enumeration ((IndexedCoalgebraBisimulation.original parameter transition).app point value).val) :
    materialReadout B parameter transition worlds arrows =
      ContextualMaterialSliceRecipient.fromEnumerated worlds arrows B parameter transition authored :=
  ContextualMaterialSliceRecipient.fromEnumerated_independent worlds arrows B parameter transition
    (HostChoiceContextualCoalgebraFinality.enumerations
      (IndexedCoalgebraBisimulation.original parameter transition)) authored

end ArbitraryWidth

variable (B : HostChoiceContextualCoalgebraFinality.Ambient.{u,v} D)

def rawFinal : Endofunctor.Coalgebra (indexedPower B) where
  V := Over.mk (Y := (⟨IndexedSmallCoalgebraRecipient.family B.interpretation⟩ :
    HostChoiceContextualCoalgebraFinality.Ambient.{u,v} D))
      (IndexedSmallCoalgebraRecipient.parameter B.interpretation)
  str := Over.homMk (IndexedSmallCoalgebraRecipient.indexedCoalgebra B.interpretation)
    (IndexedSmallCoalgebraRecipient.parameter_square B.interpretation)

noncomputable def rawFinalMap (source : Endofunctor.Coalgebra (indexedPower B)) :
    source ⟶ rawFinal B where
  f := Over.homMk (rawReadout B.interpretation source.V.hom source.str.left)
    (rawReadout_parameter B.interpretation source.V.hom source.str.left)
  h := Over.OverMorphism.ext
    (rawReadout_square B.interpretation source.V.hom source.str.left source.str.w)

theorem rawFinalMap_unique (source : Endofunctor.Coalgebra (indexedPower B))
    (candidate : source ⟶ rawFinal B) : candidate = rawFinalMap B source := by
  apply Endofunctor.Coalgebra.ext
  apply Over.OverMorphism.ext
  exact IndexedSmallCoalgebraRecipient.maps_equal_over_base B.interpretation source.V.hom source.str.left
    candidate.f.left (rawFinalMap B source).f.left
    (indexed_square_original source.V.hom (IndexedSmallCoalgebraRecipient.parameter B.interpretation)
      source.str.left (IndexedSmallCoalgebraRecipient.indexedCoalgebra B.interpretation)
      candidate.f.left candidate.f.w (congrArg Over.Hom.left candidate.h))
    (indexed_square_original source.V.hom (IndexedSmallCoalgebraRecipient.parameter B.interpretation)
      source.str.left (IndexedSmallCoalgebraRecipient.indexedCoalgebra B.interpretation)
      (rawFinalMap B source).f.left (rawFinalMap B source).f.w
      (congrArg Over.Hom.left (rawFinalMap B source).h))
    candidate.f.w (rawFinalMap B source).f.w

noncomputable def rawIsTerminal : Limits.IsTerminal (rawFinal B) :=
  Limits.IsTerminal.ofUniqueHom (rawFinalMap B) (rawFinalMap_unique B)

variable (worlds : ArgumentCoding D)
variable (arrows : (first second : D) → ArgumentCoding (first ⟶ second))

def materialFinal : Endofunctor.Coalgebra (indexedPower B) where
  V := Over.mk (Y := (⟨ContextualMaterialSliceRecipient.family worlds arrows B.interpretation⟩ :
    HostChoiceContextualCoalgebraFinality.Ambient.{u,v} D))
      (ContextualMaterialSliceRecipient.parameter worlds arrows B.interpretation)
  str := Over.homMk (ContextualMaterialSliceRecipient.indexedCoalgebra worlds arrows B.interpretation)
    (ContextualMaterialSliceRecipient.parameter_square worlds arrows B.interpretation)

noncomputable def materialFinalMap (source : Endofunctor.Coalgebra (indexedPower B)) :
    source ⟶ materialFinal B worlds arrows where
  f := Over.homMk (materialReadout B.interpretation source.V.hom source.str.left worlds arrows)
    (materialReadout_parameter B.interpretation source.V.hom source.str.left worlds arrows)
  h := Over.OverMorphism.ext
    (materialReadout_square B.interpretation source.V.hom source.str.left source.str.w worlds arrows)

theorem materialFinalMap_unique (source : Endofunctor.Coalgebra (indexedPower B))
    (candidate : source ⟶ materialFinal B worlds arrows) :
    candidate = materialFinalMap B worlds arrows source := by
  apply Endofunctor.Coalgebra.ext
  apply Over.OverMorphism.ext
  exact ContextualMaterialSliceRecipient.maps_equal_over_base worlds arrows B.interpretation
    source.V.hom source.str.left candidate.f.left (materialFinalMap B worlds arrows source).f.left
    (indexed_square_original source.V.hom
      (ContextualMaterialSliceRecipient.parameter worlds arrows B.interpretation) source.str.left
      (ContextualMaterialSliceRecipient.indexedCoalgebra worlds arrows B.interpretation)
      candidate.f.left candidate.f.w (congrArg Over.Hom.left candidate.h))
    (indexed_square_original source.V.hom
      (ContextualMaterialSliceRecipient.parameter worlds arrows B.interpretation) source.str.left
      (ContextualMaterialSliceRecipient.indexedCoalgebra worlds arrows B.interpretation)
      (materialFinalMap B worlds arrows source).f.left (materialFinalMap B worlds arrows source).f.w
      (congrArg Over.Hom.left (materialFinalMap B worlds arrows source).h))
    candidate.f.w (materialFinalMap B worlds arrows source).f.w

noncomputable def materialIsTerminal : Limits.IsTerminal (materialFinal B worlds arrows) :=
  Limits.IsTerminal.ofUniqueHom (materialFinalMap B worlds arrows) (materialFinalMap_unique B worlds arrows)

noncomputable def rawMaterialIso : rawFinal B ≅ materialFinal B worlds arrows where
  hom := materialFinalMap B worlds arrows (rawFinal B)
  inv := rawFinalMap B (materialFinal B worlds arrows)
  hom_inv_id := (rawIsTerminal B).hom_ext _ _
  inv_hom_id := (materialIsTerminal B worlds arrows).hom_ext _ _

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceIndexedCoalgebraFinality
