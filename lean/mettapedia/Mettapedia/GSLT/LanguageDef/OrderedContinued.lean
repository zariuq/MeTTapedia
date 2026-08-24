import Mettapedia.GSLT.LanguageDef.ContinuedCategory
import Mettapedia.OSLF.MeTTaIL.PatternCode

/-!
# Ordered continued interactive GSLTs

Continued interactive GSLTs equipped with the collision-free structural order
on their exact canonical keys.  This category is independent of the Cost
construction; Cost layers use it as their ambient source and target category.
-/

namespace Mettapedia.GSLT.LanguageDef

open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.PatternCode

namespace CIGSLT

/-- Collision-free structural code of a canonical key.  The proof component
of the key contributes no data. -/
def canonicalKeyCode (source : CIGSLT) (key : source.CanonicalKey) : Nat :=
  patternCode key.1.1

/-- Structural coding distinguishes canonical keys exactly. -/
theorem canonicalKeyCode_injective (source : CIGSLT) :
    Function.Injective source.canonicalKeyCode := by
  intro first second equality
  apply Subtype.ext
  apply Subtype.ext
  exact patternCode_injective equality

/-- The collision-free structural order on normalized authored patterns. -/
instance canonicalKeyLinearOrder (source : CIGSLT) :
    LinearOrder source.CanonicalKey :=
  LinearOrder.lift' source.canonicalKeyCode source.canonicalKeyCode_injective

end CIGSLT

/-- Continued interactive GSLTs equipped with the fixed structural order on
their exact canonical keys.  No new syntax or semantic authority is added. -/
structure OrderedCIGSLT where
  toCIGSLT : CIGSLT

namespace OrderedCIGSLT

instance : CoeSort OrderedCIGSLT Type :=
  ⟨fun source => source.toCIGSLT.CanonicalKey⟩

/-- An ordered continued morphism is an existing continued morphism whose
canonical-key action is monotone for the collision-free structural order. -/
structure Morphism (source target : OrderedCIGSLT) where
  underlying : CIGSLT.Morphism source.toCIGSLT target.toCIGSLT
  canonicalKeyMonotone :
    Monotone (CIGSLT.Morphism.canonicalKeyMap underlying)

namespace Morphism

/-- Ordered continued morphisms are determined by their continued map. -/
@[ext]
theorem ext {source target : OrderedCIGSLT}
    {first second : Morphism source target}
    (underlying : first.underlying = second.underlying) :
    first = second := by
  cases first
  cases second
  cases underlying
  rfl

/-- Identity preserves the structural canonical-key order. -/
def id (source : OrderedCIGSLT) : Morphism source source where
  underlying := CIGSLT.Morphism.id source.toCIGSLT
  canonicalKeyMonotone := by
    intro first second lessOrEqual
    rw [CIGSLT.Morphism.canonicalKeyMap_id,
      CIGSLT.Morphism.canonicalKeyMap_id]
    exact lessOrEqual

/-- Composition preserves structural canonical-key monotonicity. -/
def comp {first second third : OrderedCIGSLT}
    (left : Morphism first second) (right : Morphism second third) :
    Morphism first third where
  underlying := CIGSLT.Morphism.comp left.underlying right.underlying
  canonicalKeyMonotone := by
    intro firstKey secondKey lessOrEqual
    have mapped :=
      right.canonicalKeyMonotone
        (left.canonicalKeyMonotone lessOrEqual)
    change
      CIGSLT.Morphism.canonicalKeyMap
          (CIGSLT.Morphism.comp left.underlying right.underlying) firstKey ≤
        CIGSLT.Morphism.canonicalKeyMap
          (CIGSLT.Morphism.comp left.underlying right.underlying) secondKey
    rw [CIGSLT.Morphism.canonicalKeyMap_comp left.underlying right.underlying,
      CIGSLT.Morphism.canonicalKeyMap_comp left.underlying right.underlying]
    exact mapped

end Morphism

instance : CategoryTheory.Category OrderedCIGSLT where
  Hom := Morphism
  id := Morphism.id
  comp := Morphism.comp
  id_comp morphism := by
    apply Morphism.ext
    apply CIGSLT.Morphism.ext
    · rfl
    · rfl
  comp_id morphism := by
    apply Morphism.ext
    apply CIGSLT.Morphism.ext
    · rfl
    · rfl
  assoc first second third := by
    apply Morphism.ext
    apply CIGSLT.Morphism.ext
    · rfl
    · rfl

/-- Forget only the canonical-order preservation proof. -/
def forget : CategoryTheory.Functor OrderedCIGSLT CIGSLT where
  obj source := source.toCIGSLT
  map morphism := morphism.underlying
  map_id _ := rfl
  map_comp _ _ := rfl

end OrderedCIGSLT

end Mettapedia.GSLT.LanguageDef
