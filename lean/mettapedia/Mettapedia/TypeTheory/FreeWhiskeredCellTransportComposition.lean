import Mettapedia.TypeTheory.FreeWhiskeredCellTransport

/-!
# Identity and composition for strict free-cell transport

A strict map of one-cell bases and a fibrewise map of authored generators
extend to a map of free whiskered cells.  This module proves the next layer:
those extensions preserve identity and composition exactly when the authored
generator maps do.

The generator law is independent evidence.  Two individually well-typed
generator maps may be followed by a direct composite map that disagrees with
their sequential action.  Thus a native host may compose complete generated
cells only after this law is supplied; base-map composition alone is not a
license.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory
namespace FreeWhiskeredCell

universe uFirstObject uFirstHom uMiddleObject uMiddleHom uLastObject uLastHom
universe uFirstGenerator uMiddleGenerator uLastGenerator

namespace GeneratorMap

/-- The identity action on an authored generator family. -/
def identity
    (base : Base.{uFirstObject, uFirstHom})
    (Generator : {left right : base.Object} →
      base.Hom left right → base.Hom left right → Type uFirstGenerator) :
    GeneratorMap (BaseMap.identity base) Generator Generator where
  onGenerator := _root_.id

/-- Sequential generator transport over the composite base map. -/
def comp
    {first : Base.{uFirstObject, uFirstHom}}
    {middle : Base.{uMiddleObject, uMiddleHom}}
    {last : Base.{uLastObject, uLastHom}}
    {earlierBase : BaseMap first middle}
    {laterBase : BaseMap middle last}
    {FirstGenerator : {left right : first.Object} →
      first.Hom left right → first.Hom left right → Type uFirstGenerator}
    {MiddleGenerator : {left right : middle.Object} →
      middle.Hom left right → middle.Hom left right → Type uMiddleGenerator}
    {LastGenerator : {left right : last.Object} →
      last.Hom left right → last.Hom left right → Type uLastGenerator}
    (earlier : GeneratorMap earlierBase FirstGenerator MiddleGenerator)
    (later : GeneratorMap laterBase MiddleGenerator LastGenerator) :
    GeneratorMap (BaseMap.comp earlierBase laterBase)
      FirstGenerator LastGenerator where
  onGenerator := fun evidence =>
    later.onGenerator (earlier.onGenerator evidence)

/-- A separately supplied direct generator map agrees with sequential
transport on every authored generator. -/
structure CompositionCoherent
    {first : Base.{uFirstObject, uFirstHom}}
    {middle : Base.{uMiddleObject, uMiddleHom}}
    {last : Base.{uLastObject, uLastHom}}
    {earlierBase : BaseMap first middle}
    {laterBase : BaseMap middle last}
    {FirstGenerator : {left right : first.Object} →
      first.Hom left right → first.Hom left right → Type uFirstGenerator}
    {MiddleGenerator : {left right : middle.Object} →
      middle.Hom left right → middle.Hom left right → Type uMiddleGenerator}
    {LastGenerator : {left right : last.Object} →
      last.Hom left right → last.Hom left right → Type uLastGenerator}
    (earlier : GeneratorMap earlierBase FirstGenerator MiddleGenerator)
    (later : GeneratorMap laterBase MiddleGenerator LastGenerator)
    (direct : GeneratorMap (BaseMap.comp earlierBase laterBase)
      FirstGenerator LastGenerator) : Prop where
  onGenerator : ∀ {left right : first.Object}
      {firstPath secondPath : first.Hom left right}
      (evidence : FirstGenerator firstPath secondPath),
    later.onGenerator (earlier.onGenerator evidence) =
      direct.onGenerator evidence

/-- The definitionally sequential generator map is composition-coherent. -/
def compCompositionCoherent
    {first : Base.{uFirstObject, uFirstHom}}
    {middle : Base.{uMiddleObject, uMiddleHom}}
    {last : Base.{uLastObject, uLastHom}}
    {earlierBase : BaseMap first middle}
    {laterBase : BaseMap middle last}
    {FirstGenerator : {left right : first.Object} →
      first.Hom left right → first.Hom left right → Type uFirstGenerator}
    {MiddleGenerator : {left right : middle.Object} →
      middle.Hom left right → middle.Hom left right → Type uMiddleGenerator}
    {LastGenerator : {left right : last.Object} →
      last.Hom left right → last.Hom left right → Type uLastGenerator}
    (earlier : GeneratorMap earlierBase FirstGenerator MiddleGenerator)
    (later : GeneratorMap laterBase MiddleGenerator LastGenerator) :
    CompositionCoherent earlier later (comp earlier later) where
  onGenerator := by intros; rfl

end GeneratorMap

/-! ## Complete-cell functoriality -/

/-- Strict transport commutes with endpoint casts. -/
theorem mapCell_cast
    {source : Base.{uFirstObject, uFirstHom}}
    {target : Base.{uMiddleObject, uMiddleHom}}
    {SourceGenerator : {left right : source.Object} →
      source.Hom left right → source.Hom left right → Type uFirstGenerator}
    {TargetGenerator : {left right : target.Object} →
      target.Hom left right → target.Hom left right → Type uMiddleGenerator}
    (baseMap : BaseMap source target)
    (generatorMap : GeneratorMap baseMap SourceGenerator TargetGenerator)
    {left right : source.Object}
    {first second first' second' : source.Hom left right}
    (firstEquality : first = first') (secondEquality : second = second')
    (cell : Cell source SourceGenerator first second) :
    mapCell baseMap generatorMap
        (Cell.cast firstEquality secondEquality cell) =
      Cell.cast (congrArg baseMap.onHom firstEquality)
        (congrArg baseMap.onHom secondEquality)
        (mapCell baseMap generatorMap cell) := by
  cases firstEquality
  cases secondEquality
  rfl

/-- Two successive endpoint transports agree with any direct transport to
the same final endpoints.  Equality proofs themselves carry no cell data. -/
theorem Cell.cast_cast
    {base : Base.{uFirstObject, uFirstHom}}
    {Generator : {left right : base.Object} →
      base.Hom left right → base.Hom left right → Type uFirstGenerator}
    {left right : base.Object}
    {first second middleFirst middleSecond lastFirst lastSecond :
      base.Hom left right}
    (firstToMiddle : first = middleFirst)
    (secondToMiddle : second = middleSecond)
    (middleToLastFirst : middleFirst = lastFirst)
    (middleToLastSecond : middleSecond = lastSecond)
    (firstToLast : first = lastFirst)
    (secondToLast : second = lastSecond)
    (cell : Cell base Generator first second) :
    Cell.cast middleToLastFirst middleToLastSecond
        (Cell.cast firstToMiddle secondToMiddle cell) =
      Cell.cast firstToLast secondToLast cell := by
  cases firstToMiddle
  cases secondToMiddle
  cases middleToLastFirst
  cases middleToLastSecond
  cases firstToLast
  cases secondToLast
  rfl

/-- Identity base and generator maps leave the complete raw cell unchanged. -/
theorem mapCell_identity
    {base : Base.{uFirstObject, uFirstHom}}
    {Generator : {left right : base.Object} →
      base.Hom left right → base.Hom left right → Type uFirstGenerator}
    {left right : base.Object} {first second : base.Hom left right}
    (cell : Cell base Generator first second) :
    mapCell (BaseMap.identity base) (GeneratorMap.identity base Generator) cell =
      cell := by
  induction cell with
  | refl => rfl
  | generator => rfl
  | vertical earlier later earlierIH laterIH =>
      simp only [mapCell]
      rw [earlierIH, laterIH]
      rfl
  | whiskerLeft prior cell cellIH =>
      simp only [mapCell]
      rw [cellIH]
      rfl
  | whiskerRight suffix cell cellIH =>
      simp only [mapCell]
      rw [cellIH]
      rfl

/-- Sequential strict transport equals transport by the canonical composite
base and generator maps. -/
theorem mapCell_comp
    {firstBase : Base.{uFirstObject, uFirstHom}}
    {middleBase : Base.{uMiddleObject, uMiddleHom}}
    {lastBase : Base.{uLastObject, uLastHom}}
    {earlierBase : BaseMap firstBase middleBase}
    {laterBase : BaseMap middleBase lastBase}
    {FirstGenerator : {left right : firstBase.Object} →
      firstBase.Hom left right → firstBase.Hom left right →
        Type uFirstGenerator}
    {MiddleGenerator : {left right : middleBase.Object} →
      middleBase.Hom left right → middleBase.Hom left right →
        Type uMiddleGenerator}
    {LastGenerator : {left right : lastBase.Object} →
      lastBase.Hom left right → lastBase.Hom left right →
        Type uLastGenerator}
    (earlier : GeneratorMap earlierBase FirstGenerator MiddleGenerator)
    (later : GeneratorMap laterBase MiddleGenerator LastGenerator)
    {left right : firstBase.Object}
    {first second : firstBase.Hom left right}
    (cell : Cell firstBase FirstGenerator first second) :
    mapCell laterBase later (mapCell earlierBase earlier cell) =
      mapCell (BaseMap.comp earlierBase laterBase)
        (GeneratorMap.comp earlier later) cell := by
  induction cell with
  | refl => rfl
  | generator evidence =>
      rfl
  | vertical firstCell secondCell firstIH secondIH =>
      simp only [mapCell]
      rw [firstIH, secondIH]
      rfl
  | whiskerLeft prior cell cellIH =>
      rw [mapCell]
      rw [mapCell_cast]
      simp only [mapCell]
      rw [cellIH]
      apply Cell.cast_cast
  | whiskerRight suffix cell cellIH =>
      rw [mapCell]
      rw [mapCell_cast]
      simp only [mapCell]
      rw [cellIH]
      apply Cell.cast_cast

/-! ## Positive and negative controls -/

namespace CompositionCanary

def base : Base where
  Object := Unit
  Hom := fun _ _ => Unit
  compose := fun _ _ => ()

abbrev Generator : {left right : base.Object} →
    base.Hom left right → base.Hom left right → Type :=
  fun _ _ => Nat

def increment : GeneratorMap (BaseMap.identity base) Generator Generator where
  onGenerator := fun value => value + 1

def preserve : GeneratorMap (BaseMap.identity base) Generator Generator where
  onGenerator := _root_.id

def marked : Cell base Generator (source := ()) (target := ()) () () :=
  .generator 0

/-- Two identity actions compose on the complete generated cell. -/
theorem identity_composition_on_marked :
    mapCell (BaseMap.identity base) (GeneratorMap.identity base Generator)
        (mapCell (BaseMap.identity base)
          (GeneratorMap.identity base Generator) marked) =
      mapCell
        (BaseMap.comp (BaseMap.identity base) (BaseMap.identity base))
        (GeneratorMap.comp (GeneratorMap.identity base Generator)
          (GeneratorMap.identity base Generator)) marked :=
  mapCell_comp _ _ marked

/-- Individually valid generator maps do not force an independently supplied
direct map to agree with their sequential action. -/
theorem increment_then_increment_not_preserve :
    ¬ GeneratorMap.CompositionCoherent increment increment preserve := by
  intro coherent
  have mismatch := coherent.onGenerator
    (left := ()) (right := ()) (firstPath := ()) (secondPath := ()) (0 : Nat)
  simp [increment, preserve] at mismatch

end CompositionCanary

/-! ## Axiom audit -/

#print axioms GeneratorMap.compCompositionCoherent
#print axioms mapCell_cast
#print axioms mapCell_identity
#print axioms mapCell_comp
#print axioms CompositionCanary.identity_composition_on_marked
#print axioms CompositionCanary.increment_then_increment_not_preserve

end FreeWhiskeredCell
end Mettapedia.TypeTheory
