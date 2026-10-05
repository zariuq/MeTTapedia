import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraQuotient
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraPullback

/-!
# Actual coproduct of small contextual coalgebras and its separated quotient

Codes contain actual small argument functors and actual covered-power
coalgebras. Their coproduct is constructed at the next host universe, with
its natural coalgebra, original-bound branch enumerations and every
small-coalgebra inclusion. The greatest-bisimulation quotient is therefore
a constructed target for every originally small contextual coalgebra.

Two genuine coalgebra maps from the same source into a behaviorally
separated target agree. This proves the actual unique-map property of the
constructed quotient for all originally small contextual sources.

The claim is relative to the fixed small context and argument bound. It
does not assert existence of a map from every larger covered coalgebra,
slice-indexed finality, universal small-map representability or internal
Collection. It selects neither codes nor enumerations from existence.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSmallCoalgebraGenerators

open CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open Mettapedia.TypeTheory.ContextualWitnessCover

universe u v w
variable {D : Type u} [Category.{u} D]

section SeparatedMaps

variable {A : D ⥤ Type v} {B : D ⥤ Type w}
variable (source : NaturalHom A (family A)) (target : NaturalHom B (family B))
variable (first second : NaturalHom A B)
variable (firstSquare : source.comp (imageHom first) = first.comp target)
variable (secondSquare : source.comp (imageHom second) = second.comp target)

include firstSquare secondSquare

theorem mixed_image_isBisimulation :
    ContextualCoalgebraBisimulation.IsBisimulation target
      (fun point left right => ∃ argument, first.app point argument = left ∧ second.app point argument = right) where
  stable {_ _} step {_ _} related := by
    obtain ⟨argument, leftEq, rightEq⟩ := related
    exact ⟨A.map step argument,
      (first.naturality step argument).symm.trans (congrArg (B.map step) leftEq),
      (second.naturality step argument).symm.trans (congrArg (B.map step) rightEq)⟩
  forth {point _ _} related future {_} available := by
    obtain ⟨argument, leftEq, rightEq⟩ := related
    rw [← leftEq] at available
    obtain ⟨child, same, admitted⟩ :=
      (ContextualCoalgebraBisimulation.coalgebra_map_truth source first target firstSquare
        point argument future _).mp available
    refine ⟨second.app future.1 child, ?_, child, same, rfl⟩
    rw [← rightEq]
    exact (ContextualCoalgebraBisimulation.coalgebra_map_truth source second target secondSquare
      point argument future _).mpr ⟨child, rfl, admitted⟩
  back {point _ _} related future {_} available := by
    obtain ⟨argument, leftEq, rightEq⟩ := related
    rw [← rightEq] at available
    obtain ⟨child, same, admitted⟩ :=
      (ContextualCoalgebraBisimulation.coalgebra_map_truth source second target secondSquare
        point argument future _).mp available
    refine ⟨first.app future.1 child, ?_, child, rfl, same⟩
    rw [← leftEq]
    exact (ContextualCoalgebraBisimulation.coalgebra_map_truth source first target firstSquare
      point argument future _).mpr ⟨child, rfl, admitted⟩

theorem maps_equal_into_separated (separated : ContextualCoalgebraQuotient.BehaviorallySeparated target) :
    first = second := by
  apply NaturalHom.ext
  intro point argument
  exact separated point _ _
    (ContextualCoalgebraBisimulation.greatest target
      (mixed_image_isBisimulation source target first second firstSquare secondSquare)
      ⟨argument, rfl, rfl⟩)

end SeparatedMaps

/-- The code ranges over actual small contextual coalgebras, including
all their future maps and child predicates. -/
structure Code (D : Type u) [Category.{u} D] where
  carrier : D ⥤ Type u
  coalgebra : NaturalHom carrier (family carrier)

def coproduct : D ⥤ Type (u + 1) where
  obj point := Σ code : Code D, code.carrier.obj point
  map step := TypeCat.ofHom fun argument => ⟨argument.1, argument.1.carrier.map step argument.2⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro argument
    exact congrArg (Sigma.mk argument.1) (argument.1.carrier.map_id_apply point argument.2)
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro argument
    exact congrArg (Sigma.mk argument.1)
      (argument.1.carrier.map_comp_apply earlier later argument.2)

def inclusion (code : Code D) : NaturalHom code.carrier (coproduct (D := D)) where
  app _ argument := ⟨code, argument⟩
  naturality _ _ := rfl

def coproductCoalgebra : NaturalHom (coproduct (D := D)) (family (coproduct (D := D))) where
  app point argument := imagePower (inclusion argument.1) point (argument.1.coalgebra.app point argument.2)
  naturality {first second} step argument :=
    (imagePower_restrict (inclusion argument.1) step
      (argument.1.coalgebra.app first argument.2)).trans
      (congrArg (imagePower (inclusion argument.1) second)
        (argument.1.coalgebra.naturality step argument.2))

theorem inclusion_square (code : Code D) :
    code.coalgebra.comp (imageHom (inclusion code)) = (inclusion code).comp coproductCoalgebra := by
  apply NaturalHom.ext
  intro _ _
  rfl

/-- Every branch cover is computed from the retained code's actual small
truth subtype, and then transported into the coproduct. -/
def coproductEnumeration (point : D) (argument : (coproduct (D := D)).obj point) :
    Enumeration (coproductCoalgebra.app point argument).val :=
  imageEnumeration (inclusion argument.1) point
    (smallEnumeration (argument.1.coalgebra.app point argument.2).val)

abbrev quotient := ContextualCoalgebraQuotient.family (coproductCoalgebra (D := D))
abbrev quotientCoalgebra := ContextualCoalgebraQuotient.coalgebra (coproductCoalgebra (D := D))
abbrev quotientProjection := ContextualCoalgebraQuotient.projection (coproductCoalgebra (D := D))

theorem quotient_separated : ContextualCoalgebraQuotient.BehaviorallySeparated (quotientCoalgebra (D := D)) :=
  ContextualCoalgebraQuotient.quotient_separated coproductCoalgebra

def canonical (code : Code D) : NaturalHom code.carrier (quotient (D := D)) :=
  (inclusion code).comp quotientProjection

theorem canonical_square (code : Code D) :
    code.coalgebra.comp (imageHom (canonical code)) = (canonical code).comp quotientCoalgebra := by
  apply NaturalHom.ext
  intro point argument
  change imagePower ((inclusion code).comp quotientProjection) point (code.coalgebra.app point argument) =
    quotientCoalgebra.app point (quotientProjection.app point ((inclusion code).app point argument))
  exact (imagePower_comp (inclusion code) quotientProjection point
    (code.coalgebra.app point argument)).symm.trans
      (ContextualCoalgebraQuotient.coalgebra_projection coproductCoalgebra point
        ((inclusion code).app point argument)).symm

theorem canonical_eq_iff (code : Code D) (point : D) (first second : code.carrier.obj point) :
    (canonical code).app point first = (canonical code).app point second ↔
      ContextualCoalgebraBisimulation.Bisimilar code.coalgebra point first second := by
  constructor
  · intro same
    apply ContextualCoalgebraBisimulation.bisimilar_reflected code.coalgebra (canonical code)
      quotientCoalgebra (canonical_square code)
    rw [same]
    exact ContextualCoalgebraBisimulation.bisimilar_refl quotientCoalgebra point _
  · intro related
    exact quotient_separated point _ _
      (ContextualCoalgebraBisimulation.bisimilar_preserved code.coalgebra (canonical code)
        quotientCoalgebra (canonical_square code) related)

/-- Every actual originally small source has exactly one actual coalgebra
map to the constructed separated quotient. -/
theorem unique_small_map (code : Code D) :
    ∃! operation : NaturalHom code.carrier (quotient (D := D)),
      code.coalgebra.comp (imageHom operation) = operation.comp quotientCoalgebra := by
  refine ⟨canonical code, canonical_square code, ?_⟩
  intro candidate square
  exact maps_equal_into_separated code.coalgebra quotientCoalgebra candidate (canonical code)
    square (canonical_square code) quotient_separated

/-- The map is built directly from an arbitrary small source, rather than
from a supplied code-selection or generating-object interface. -/
def fromSmall (A : D ⥤ Type u) (source : NaturalHom A (family A)) : NaturalHom A (quotient (D := D)) :=
  canonical ⟨A, source⟩

theorem fromSmall_square (A : D ⥤ Type u) (source : NaturalHom A (family A)) :
    source.comp (imageHom (fromSmall A source)) = (fromSmall A source).comp quotientCoalgebra :=
  canonical_square ⟨A, source⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSmallCoalgebraGenerators
