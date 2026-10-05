import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualEnumeratedCoalgebraReadout
import Mathlib.CategoryTheory.Endofunctor.Algebra

/-!
# A final covered-power coalgebra under external host Choice

The small context and branch-receipt bound is `u`. The constructed recipient
has fibres in `Type (u+1)`. In an ambient family category with fibre level
`max (u+1) v`, its explicit same-site lift is a final coalgebra of the actual
covered-future-power endofunctor.

External `Classical.choice` selects uniform branch enumerations from the
propositional covers. The subsequent readout and its whole coalgebra square
use the constructed generated small coalgebras. This optional host profile
does not assert constructive selection, unrestricted powerclass finality,
or a native foundation. All admitted futures retain their actual arrows.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualCoalgebraFinality

open _root_.CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open Mettapedia.TypeTheory.ContextualWitnessCover

universe u v w t
variable {D : Type u} [Category.{u} D]

/-- This is the only branch-data selection: a host Choice operation. -/
noncomputable def enumerations {A : D ⥤ Type w}
    (coalgebra : NaturalHom A (family A)) :
    ∀ point value, Enumeration (coalgebra.app point value).val :=
  fun point value => Classical.choice (coalgebra.app point value).property

noncomputable def readout {A : D ⥤ Type w} (coalgebra : NaturalHom A (family A)) :
    NaturalHom A (ContextualSmallCoalgebraGenerators.quotient (D := D)) :=
  ContextualEnumeratedCoalgebraReadout.readout A coalgebra (enumerations coalgebra)

theorem readout_square {A : D ⥤ Type w} (coalgebra : NaturalHom A (family A)) :
    coalgebra.comp (imageHom (readout coalgebra)) =
      (readout coalgebra).comp ContextualSmallCoalgebraGenerators.quotientCoalgebra :=
  ContextualEnumeratedCoalgebraReadout.readout_square A coalgebra (enumerations coalgebra)

theorem readout_kernel {A : D ⥤ Type w} (coalgebra : NaturalHom A (family A))
    (point : D) (first second : A.obj point) :
    (readout coalgebra).app point first = (readout coalgebra).app point second ↔
      ContextualCoalgebraBisimulation.Bisimilar coalgebra point first second :=
  ContextualEnumeratedCoalgebraReadout.value_eq_iff A coalgebra
    (enumerations coalgebra) point first second

theorem readout_independent {A : D ⥤ Type w} (coalgebra : NaturalHom A (family A))
    (authored : ∀ point value, Enumeration (coalgebra.app point value).val) :
    readout coalgebra = ContextualEnumeratedCoalgebraReadout.readout A coalgebra authored :=
  ContextualEnumeratedCoalgebraReadout.readout_enumeration_independent A coalgebra
    (enumerations coalgebra) authored

theorem unique_readout {A : D ⥤ Type w} (coalgebra : NaturalHom A (family A)) :
    ∃! operation : NaturalHom A (ContextualSmallCoalgebraGenerators.quotient (D := D)),
      coalgebra.comp (imageHom operation) =
        operation.comp ContextualSmallCoalgebraGenerators.quotientCoalgebra :=
  ContextualEnumeratedCoalgebraReadout.unique_readout A coalgebra (enumerations coalgebra)

/-- An actual same-site lift of fibres; context objects and arrows are unchanged. -/
def liftFamily (A : D ⥤ Type w) : D ⥤ Type (max w v) where
  obj point := ULift.{v} (A.obj point)
  map step := TypeCat.ofHom fun value => ULift.up (A.map step value.down)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro value
    exact congrArg ULift.up (congrArg (fun map => map value.down) (A.map_id point))
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro value
    exact congrArg ULift.up
      (congrArg (fun map => map value.down) (A.map_comp first second))

def raise (A : D ⥤ Type w) : NaturalHom A (liftFamily.{u,v,w} A) where
  app _ := ULift.up
  naturality _ _ := rfl

def lower (A : D ⥤ Type w) : NaturalHom (liftFamily.{u,v,w} A) A where
  app _ := ULift.down
  naturality _ _ := rfl

theorem raise_lower (A : D ⥤ Type w) :
    (raise.{u,v,w} A).comp (lower A) = identityHom A := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem lower_raise (A : D ⥤ Type w) :
    (lower.{u,v,w} A).comp (raise A) = identityHom (liftFamily A) := by
  apply NaturalHom.ext
  intro _ value
  cases value
  rfl

/-- The lifted coalgebra computes the original children and raises their actual values. -/
def liftCoalgebra {A : D ⥤ Type w} (coalgebra : NaturalHom A (family A)) :
    NaturalHom (liftFamily.{u,v,w} A) (family (liftFamily.{u,v,w} A)) :=
  ((lower A).comp coalgebra).comp (imageHom (raise A))

theorem raise_square {A : D ⥤ Type w} (coalgebra : NaturalHom A (family A)) :
    coalgebra.comp (imageHom (raise.{u,v,w} A)) =
      (raise A).comp (liftCoalgebra coalgebra) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem lower_square {A : D ⥤ Type w} (coalgebra : NaturalHom A (family A)) :
    (liftCoalgebra.{u,v,w} coalgebra).comp (imageHom (lower A)) =
      (lower A).comp coalgebra := by
  apply NaturalHom.ext
  intro point value
  change imagePower (lower A) point
    (imagePower (raise A) point (coalgebra.app point value.down)) = _
  exact (imagePower_comp (raise A) (lower A) point
    (coalgebra.app point value.down)).trans
      ((congrArg (fun operation : NaturalHom A A =>
        imagePower operation point (coalgebra.app point value.down)) (raise_lower A)).trans
          (imagePower_identity point (coalgebra.app point value.down)))

theorem maps_equal_into_lift {A : D ⥤ Type t} {B : D ⥤ Type w}
    (source : NaturalHom A (family A)) (target : NaturalHom B (family B))
    (separated : ContextualCoalgebraQuotient.BehaviorallySeparated target)
    (first second : NaturalHom A (liftFamily.{u,v,w} B))
    (firstSquare : source.comp (imageHom first) = first.comp (liftCoalgebra target))
    (secondSquare : source.comp (imageHom second) = second.comp (liftCoalgebra target)) :
    first = second := by
  have same := ContextualSmallCoalgebraGenerators.maps_equal_into_separated source target
    (first.comp (lower B)) (second.comp (lower B))
    (ContextualSmallCoalgebraComparisons.compose_square source (liftCoalgebra target) target
      first (lower B) firstSquare (lower_square target))
    (ContextualSmallCoalgebraComparisons.compose_square source (liftCoalgebra target) target
      second (lower B) secondSquare (lower_square target)) separated
  apply NaturalHom.ext
  intro point value
  apply ULift.ext
  exact congrArg (fun operation : NaturalHom A B => operation.app point value) same

abbrev Ambient (D : Type u) [Category.{u} D] := FamilyObject.{u,max (u+1) v} D

def finalCoalgebra : Endofunctor.Coalgebra (futurePower (D := D) :
    Ambient.{u,v} D ⥤ Ambient.{u,v} D) where
  V := ⟨liftFamily.{u,v,u+1} (ContextualSmallCoalgebraGenerators.quotient (D := D))⟩
  str := liftCoalgebra ContextualSmallCoalgebraGenerators.quotientCoalgebra

noncomputable def finalMap (source : Endofunctor.Coalgebra (futurePower (D := D) :
    Ambient.{u,v} D ⥤ Ambient.{u,v} D)) : source ⟶ finalCoalgebra where
  f := (readout source.str).comp (raise (ContextualSmallCoalgebraGenerators.quotient (D := D)))
  h := ContextualSmallCoalgebraComparisons.compose_square source.str
    ContextualSmallCoalgebraGenerators.quotientCoalgebra
    (liftCoalgebra ContextualSmallCoalgebraGenerators.quotientCoalgebra)
    (readout source.str) (raise _)
    (readout_square source.str) (raise_square ContextualSmallCoalgebraGenerators.quotientCoalgebra)

theorem finalMap_unique (source : Endofunctor.Coalgebra (futurePower (D := D) :
    Ambient.{u,v} D ⥤ Ambient.{u,v} D)) (candidate : source ⟶ finalCoalgebra) :
    candidate = finalMap source := by
  apply Endofunctor.Coalgebra.ext
  exact maps_equal_into_lift source.str ContextualSmallCoalgebraGenerators.quotientCoalgebra
    ContextualSmallCoalgebraGenerators.quotient_separated candidate.f (finalMap source).f
    candidate.h (finalMap source).h

/-- Actual finality in the full ambient covered-power coalgebra category. -/
noncomputable def isTerminal : Limits.IsTerminal (finalCoalgebra (D := D) :
    Endofunctor.Coalgebra (futurePower : Ambient.{u,v} D ⥤ Ambient.{u,v} D)) :=
  Limits.IsTerminal.ofUniqueHom finalMap finalMap_unique

theorem finalMap_kernel (source : Endofunctor.Coalgebra (futurePower (D := D) :
    Ambient.{u,v} D ⥤ Ambient.{u,v} D)) (point : D)
    (first second : source.V.interpretation.obj point) :
    (finalMap source).f.app point first = (finalMap source).f.app point second ↔
      ContextualCoalgebraBisimulation.Bisimilar source.str point first second := by
  change ULift.up ((readout source.str).app point first) =
    ULift.up ((readout source.str).app point second) ↔ _
  exact (Equiv.ulift.symm.injective.eq_iff).trans (readout_kernel source.str point first second)

/-- The genuine terminality proof supplies the inverse to the structure map. -/
noncomputable def structureInverse :
    (futurePower.obj finalCoalgebra.V : Ambient.{u,v} D) ⟶ finalCoalgebra.V :=
  Endofunctor.Coalgebra.Terminal.strInv isTerminal

theorem structureInverse_structure :
    structureInverse (D := D) ≫ (finalCoalgebra (D := D) :
      Endofunctor.Coalgebra (futurePower : Ambient.{u,v} D ⥤ Ambient.{u,v} D)).str = 𝟙 _ :=
  Endofunctor.Coalgebra.Terminal.left_inv isTerminal

theorem structure_structureInverse :
    (finalCoalgebra (D := D) : Endofunctor.Coalgebra
      (futurePower : Ambient.{u,v} D ⥤ Ambient.{u,v} D)).str ≫ structureInverse = 𝟙 _ :=
  Endofunctor.Coalgebra.Terminal.right_inv isTerminal

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualCoalgebraFinality
