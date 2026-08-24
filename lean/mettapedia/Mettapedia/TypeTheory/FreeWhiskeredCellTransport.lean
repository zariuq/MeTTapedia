import Mettapedia.TypeTheory.FreeWhiskeredCellCoherenceObservation

/-!
# Strict transport of free whiskered cells

A map of raw one-cell bases does not by itself transport generated two-cells.
It must preserve one-cell composition and it must also map every authored
two-generator in its exact parallel fibre.  Once those two capabilities are
supplied, the free syntax transports structurally.

This is the strict branch of the later coherence design.  It is intentionally
scoped: when generator naturality is unavailable, this module does not replace
the missing comparison by equality.  A pseudo or higher transport may instead
retain an explicit comparison cell.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory
namespace FreeWhiskeredCell

universe uSourceObject uSourceHom uTargetObject uTargetHom uLastObject uLastHom
universe uSourceGenerator uTargetGenerator

/-! ## Composition-preserving maps of raw bases -/

/-- A strict map of the raw one-dimensional boundary.  `Base` has no chosen
identities or laws, so composition preservation is the only structural law
available at this layer. -/
structure BaseMap
    (source : Base.{uSourceObject, uSourceHom})
    (target : Base.{uTargetObject, uTargetHom}) where
  onObject : source.Object → target.Object
  onHom : ∀ {left right : source.Object}, source.Hom left right →
    target.Hom (onObject left) (onObject right)
  map_compose : ∀ {left middle right : source.Object}
      (first : source.Hom left middle) (second : source.Hom middle right),
    onHom (source.compose first second) =
      target.compose (onHom first) (onHom second)

namespace BaseMap

def identity (base : Base.{uSourceObject, uSourceHom}) : BaseMap base base where
  onObject := _root_.id
  onHom := _root_.id
  map_compose := by intros; rfl

def comp
    {first : Base.{uSourceObject, uSourceHom}}
    {middle : Base.{uTargetObject, uTargetHom}}
    {last : Base.{uLastObject, uLastHom}}
    (earlier : BaseMap first middle) (later : BaseMap middle last) :
    BaseMap first last where
  onObject := fun object => later.onObject (earlier.onObject object)
  onHom := fun hom => later.onHom (earlier.onHom hom)
  map_compose := by
    intro left middleObject right firstHom secondHom
    rw [earlier.map_compose, later.map_compose]

end BaseMap

/-! ## Transporting generator families and cells -/

/-- A parallel-fibre map of authored generators over a fixed base map.  This
is independent evidence: composition preservation of one-cells cannot create
it. -/
structure GeneratorMap
    {source : Base.{uSourceObject, uSourceHom}}
    {target : Base.{uTargetObject, uTargetHom}}
    (baseMap : BaseMap source target)
    (SourceGenerator : {left right : source.Object} →
      source.Hom left right → source.Hom left right → Type uSourceGenerator)
    (TargetGenerator : {left right : target.Object} →
      target.Hom left right → target.Hom left right → Type uTargetGenerator) where
  onGenerator : ∀ {left right : source.Object}
      {first second : source.Hom left right},
    SourceGenerator first second →
      TargetGenerator (baseMap.onHom first) (baseMap.onHom second)

namespace Cell

/-- Reindex both parallel one-cell endpoints of a generated cell along proved
equalities. -/
def cast
    {base : Base.{uTargetObject, uTargetHom}}
    {Generator : {left right : base.Object} →
      base.Hom left right → base.Hom left right → Type uTargetGenerator}
    {left right : base.Object}
    {first second first' second' : base.Hom left right}
    (firstEquality : first = first') (secondEquality : second = second') :
    Cell base Generator first second → Cell base Generator first' second' := by
  cases firstEquality
  cases secondEquality
  exact _root_.id

@[simp] theorem cast_rfl
    {base : Base.{uTargetObject, uTargetHom}}
    {Generator : {left right : base.Object} →
      base.Hom left right → base.Hom left right → Type uTargetGenerator}
    {left right : base.Object} {first second : base.Hom left right}
    (cell : Cell base Generator first second) :
    cast rfl rfl cell = cell :=
  rfl

end Cell

/-- Strict base transport plus generator transport extends over every raw
cell.  Whiskering uses the supplied composition equations; no coherence
quotient is introduced. -/
def mapCell
    {source : Base.{uSourceObject, uSourceHom}}
    {target : Base.{uTargetObject, uTargetHom}}
    {SourceGenerator : {left right : source.Object} →
      source.Hom left right → source.Hom left right → Type uSourceGenerator}
    {TargetGenerator : {left right : target.Object} →
      target.Hom left right → target.Hom left right → Type uTargetGenerator}
    (baseMap : BaseMap source target)
    (generatorMap : GeneratorMap baseMap SourceGenerator TargetGenerator)
    {left right : source.Object} {first second : source.Hom left right}
    (cell : Cell source SourceGenerator first second) :
    Cell target TargetGenerator (baseMap.onHom first) (baseMap.onHom second) :=
  match cell with
  | .refl path => Cell.refl (baseMap.onHom path)
  | .generator evidence =>
      Cell.generator (generatorMap.onGenerator evidence)
  | .vertical earlier later =>
      Cell.vertical (mapCell baseMap generatorMap earlier)
        (mapCell baseMap generatorMap later)
  | .whiskerLeft prior cell =>
      Cell.cast
        (baseMap.map_compose prior _).symm
        (baseMap.map_compose prior _).symm
        (Cell.whiskerLeft (baseMap.onHom prior)
          (mapCell baseMap generatorMap cell))
  | .whiskerRight suffix cell =>
      Cell.cast
        (baseMap.map_compose _ suffix).symm
        (baseMap.map_compose _ suffix).symm
        (Cell.whiskerRight (baseMap.onHom suffix)
          (mapCell baseMap generatorMap cell))

/-! ## Structural observations survive strict transport -/

open CoherenceObservation

@[simp] theorem generatorCount_cast
    {base : Base.{uTargetObject, uTargetHom}}
    {Generator : {left right : base.Object} →
      base.Hom left right → base.Hom left right → Type uTargetGenerator}
    {left right : base.Object}
    {first second first' second' : base.Hom left right}
    (firstEquality : first = first') (secondEquality : second = second')
    (cell : Cell base Generator first second) :
    generatorCount (Cell.cast firstEquality secondEquality cell) =
      generatorCount cell := by
  cases firstEquality
  cases secondEquality
  rfl

@[simp] theorem constructorCount_cast
    {base : Base.{uTargetObject, uTargetHom}}
    {Generator : {left right : base.Object} →
      base.Hom left right → base.Hom left right → Type uTargetGenerator}
    {left right : base.Object}
    {first second first' second' : base.Hom left right}
    (firstEquality : first = first') (secondEquality : second = second')
    (cell : Cell base Generator first second) :
    constructorCount (Cell.cast firstEquality secondEquality cell) =
      constructorCount cell := by
  cases firstEquality
  cases secondEquality
  rfl

@[simp] theorem rawShape_cast
    {base : Base.{uTargetObject, uTargetHom}}
    {Generator : {left right : base.Object} →
      base.Hom left right → base.Hom left right → Type uTargetGenerator}
    {left right : base.Object}
    {first second first' second' : base.Hom left right}
    (firstEquality : first = first') (secondEquality : second = second')
    (cell : Cell base Generator first second) :
    rawShape (Cell.cast firstEquality secondEquality cell) = rawShape cell := by
  cases firstEquality
  cases secondEquality
  rfl

theorem generatorCount_mapCell
    {source : Base.{uSourceObject, uSourceHom}}
    {target : Base.{uTargetObject, uTargetHom}}
    {SourceGenerator : {left right : source.Object} →
      source.Hom left right → source.Hom left right → Type uSourceGenerator}
    {TargetGenerator : {left right : target.Object} →
      target.Hom left right → target.Hom left right → Type uTargetGenerator}
    (baseMap : BaseMap source target)
    (generatorMap : GeneratorMap baseMap SourceGenerator TargetGenerator)
    {left right : source.Object} {first second : source.Hom left right}
    (cell : Cell source SourceGenerator first second) :
    generatorCount (mapCell baseMap generatorMap cell) = generatorCount cell := by
  induction cell with
  | refl => rfl
  | generator => rfl
  | vertical earlier later earlierIH laterIH =>
      change generatorCount (mapCell baseMap generatorMap earlier) +
          generatorCount (mapCell baseMap generatorMap later) =
        generatorCount earlier + generatorCount later
      rw [earlierIH, laterIH]
  | whiskerLeft prior cell cellIH =>
      change generatorCount
          (Cell.cast _ _
            (Cell.whiskerLeft (baseMap.onHom prior)
              (mapCell baseMap generatorMap cell))) = generatorCount cell
      rw [generatorCount_cast, generatorCount_whiskerLeft, cellIH]
  | whiskerRight suffix cell cellIH =>
      change generatorCount
          (Cell.cast _ _
            (Cell.whiskerRight (baseMap.onHom suffix)
              (mapCell baseMap generatorMap cell))) = generatorCount cell
      rw [generatorCount_cast, generatorCount_whiskerRight, cellIH]

theorem constructorCount_mapCell
    {source : Base.{uSourceObject, uSourceHom}}
    {target : Base.{uTargetObject, uTargetHom}}
    {SourceGenerator : {left right : source.Object} →
      source.Hom left right → source.Hom left right → Type uSourceGenerator}
    {TargetGenerator : {left right : target.Object} →
      target.Hom left right → target.Hom left right → Type uTargetGenerator}
    (baseMap : BaseMap source target)
    (generatorMap : GeneratorMap baseMap SourceGenerator TargetGenerator)
    {left right : source.Object} {first second : source.Hom left right}
    (cell : Cell source SourceGenerator first second) :
    constructorCount (mapCell baseMap generatorMap cell) =
      constructorCount cell := by
  induction cell with
  | refl => rfl
  | generator => rfl
  | vertical earlier later earlierIH laterIH =>
      change constructorCount (mapCell baseMap generatorMap earlier) +
          constructorCount (mapCell baseMap generatorMap later) + 1 =
        constructorCount earlier + constructorCount later + 1
      rw [earlierIH, laterIH]
  | whiskerLeft prior cell cellIH =>
      change constructorCount
          (Cell.cast _ _
            (Cell.whiskerLeft (baseMap.onHom prior)
              (mapCell baseMap generatorMap cell))) =
        constructorCount cell + 1
      rw [constructorCount_cast, constructorCount_whiskerLeft, cellIH]
  | whiskerRight suffix cell cellIH =>
      change constructorCount
          (Cell.cast _ _
            (Cell.whiskerRight (baseMap.onHom suffix)
              (mapCell baseMap generatorMap cell))) =
        constructorCount cell + 1
      rw [constructorCount_cast, constructorCount_whiskerRight, cellIH]

theorem rawShape_mapCell
    {source : Base.{uSourceObject, uSourceHom}}
    {target : Base.{uTargetObject, uTargetHom}}
    {SourceGenerator : {left right : source.Object} →
      source.Hom left right → source.Hom left right → Type uSourceGenerator}
    {TargetGenerator : {left right : target.Object} →
      target.Hom left right → target.Hom left right → Type uTargetGenerator}
    (baseMap : BaseMap source target)
    (generatorMap : GeneratorMap baseMap SourceGenerator TargetGenerator)
    {left right : source.Object} {first second : source.Hom left right}
    (cell : Cell source SourceGenerator first second) :
    rawShape (mapCell baseMap generatorMap cell) = rawShape cell := by
  induction cell with
  | refl => rfl
  | generator => rfl
  | vertical earlier later earlierIH laterIH =>
      change RawShape.vertical
          (rawShape (mapCell baseMap generatorMap earlier))
          (rawShape (mapCell baseMap generatorMap later)) =
        RawShape.vertical (rawShape earlier) (rawShape later)
      rw [earlierIH, laterIH]
  | whiskerLeft prior cell cellIH =>
      change rawShape
          (Cell.cast _ _
            (Cell.whiskerLeft (baseMap.onHom prior)
              (mapCell baseMap generatorMap cell))) =
        RawShape.whiskerLeft (rawShape cell)
      rw [rawShape_cast, rawShape_whiskerLeft, cellIH]
  | whiskerRight suffix cell cellIH =>
      change rawShape
          (Cell.cast _ _
            (Cell.whiskerRight (baseMap.onHom suffix)
              (mapCell baseMap generatorMap cell))) =
        RawShape.whiskerRight (rawShape cell)
      rw [rawShape_cast, rawShape_whiskerRight, cellIH]

/-! ## Generator naturality is genuinely independent -/

namespace TransportCanary

def base : Base where
  Object := Unit
  Hom := fun _ _ => Unit
  compose := fun _ _ => ()

inductive SourceGenerator : {left right : base.Object} →
    base.Hom left right → base.Hom left right → Type where
  | marked : SourceGenerator (left := ()) (right := ()) () ()

abbrev EmptyGenerator : {left right : base.Object} →
    base.Hom left right → base.Hom left right → Type :=
  fun _ _ => Empty

/-- Even the identity base map cannot transport a generator into an empty
target generator fibre.  Composition preservation alone is insufficient. -/
theorem no_generatorMap_to_empty :
    IsEmpty
      (GeneratorMap (BaseMap.identity base) SourceGenerator EmptyGenerator) :=
  ⟨fun generatorMap =>
    Empty.elim (generatorMap.onGenerator SourceGenerator.marked)⟩

def retainedGeneratorMap :
    GeneratorMap (BaseMap.identity base) SourceGenerator SourceGenerator where
  onGenerator := fun evidence => evidence

def markedCell : Cell base SourceGenerator (source := ()) (target := ()) () () :=
  .generator .marked

/-- When generator naturality is supplied, the strict map preserves the full
raw constructor shape rather than merely its endpoints. -/
theorem identity_transport_retains_marked_shape :
    rawShape
        (mapCell (BaseMap.identity base) retainedGeneratorMap markedCell) =
      rawShape markedCell :=
  rawShape_mapCell (BaseMap.identity base) retainedGeneratorMap markedCell

end TransportCanary

#print axioms BaseMap.comp
#print axioms mapCell
#print axioms generatorCount_mapCell
#print axioms constructorCount_mapCell
#print axioms rawShape_mapCell
#print axioms TransportCanary.no_generatorMap_to_empty
#print axioms TransportCanary.identity_transport_retains_marked_shape

end FreeWhiskeredCell
end Mettapedia.TypeTheory
