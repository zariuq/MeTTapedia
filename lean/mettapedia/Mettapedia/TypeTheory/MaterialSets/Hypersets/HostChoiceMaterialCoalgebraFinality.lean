import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualCoalgebraFinality
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSmallCoalgebraMaterialCoalgebra

/-!
# Actual material final coalgebra under external host Choice

The behavior carrier is the constructed occurrence-class presentation of
the collected material graphs, with its explicit member decoder. Faithful
world and actual-arrow dictionaries are encoding data. External host Choice
supplies uniform branch enumerations for arbitrary covered sources.

The class carrier lies in `Type (u+1)`; its actual material members lie in
`Type (u+2)` and its collecting graph has bound `u+1`. A same-site lift places
the class coalgebra in the ambient fibre level `max (u+1) v`. The finality
proof neither selects a raw quotient representative nor identifies these
three universe levels.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceMaterialCoalgebraFinality

open _root_.CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open Mettapedia.TypeTheory.ContextualWitnessCover
open ContextualSmallCoalgebraMaterialCarrier ContextualSmallCoalgebraMaterialCoalgebra

universe u v w
variable {D : Type u} [Category.{u} D]
variable (worlds : ArgumentCoding D)
variable (arrows : (first second : D) → ArgumentCoding (first ⟶ second))

noncomputable def readout {A : D ⥤ Type w} (source : NaturalHom A (family A)) :
    NaturalHom A (classFamily worlds arrows) :=
  enumeratedReadout worlds arrows A source
    (HostChoiceContextualCoalgebraFinality.enumerations source)

theorem readout_square {A : D ⥤ Type w} (source : NaturalHom A (family A)) :
    source.comp (imageHom (readout worlds arrows source)) =
      (readout worlds arrows source).comp (classCoalgebra worlds arrows) :=
  enumeratedReadout_square worlds arrows A source
    (HostChoiceContextualCoalgebraFinality.enumerations source)

theorem readout_kernel {A : D ⥤ Type w} (source : NaturalHom A (family A))
    (point : D) (first second : A.obj point) :
    (readout worlds arrows source).app point first =
        (readout worlds arrows source).app point second ↔
      ContextualCoalgebraBisimulation.Bisimilar source point first second :=
  enumeratedReadout_eq_iff worlds arrows A source
    (HostChoiceContextualCoalgebraFinality.enumerations source) point first second

theorem readout_independent {A : D ⥤ Type w} (source : NaturalHom A (family A))
    (authored : ∀ point value, Enumeration (source.app point value).val) :
    readout worlds arrows source = enumeratedReadout worlds arrows A source authored :=
  enumeratedReadout_independent worlds arrows A source
    (HostChoiceContextualCoalgebraFinality.enumerations source) authored

theorem unique_readout {A : D ⥤ Type w} (source : NaturalHom A (family A)) :
    ∃! operation : NaturalHom A (classFamily worlds arrows),
      source.comp (imageHom operation) = operation.comp (classCoalgebra worlds arrows) :=
  unique_enumeratedReadout worlds arrows A source
    (HostChoiceContextualCoalgebraFinality.enumerations source)

/-- The actual decoded value is the lift of the generated small source graph. -/
theorem readout_member_value {A : D ⥤ Type w} (source : NaturalHom A (family A))
    (point : D) (value : A.obj point) :
    ((classToMembers worlds arrows).app point
      ((readout worlds arrows source).app point value)).val =
      HSet.lift (readValue worlds arrows point
        ⟨ContextualEnumeratedCoalgebraReadout.generatedCode A source
          (HostChoiceContextualCoalgebraFinality.enumerations source) ⟨point, value⟩,
          ContextualGeneratedCoalgebras.rootMember A source
            (HostChoiceContextualCoalgebraFinality.enumerations source) ⟨point, value⟩⟩) :=
  enumeratedReadout_value worlds arrows A source
    (HostChoiceContextualCoalgebraFinality.enumerations source) point value

def finalCoalgebra : Endofunctor.Coalgebra (futurePower (D := D) :
    HostChoiceContextualCoalgebraFinality.Ambient.{u,v} D ⥤
      HostChoiceContextualCoalgebraFinality.Ambient.{u,v} D) where
  V := ⟨HostChoiceContextualCoalgebraFinality.liftFamily.{u,v,u+1} (classFamily worlds arrows)⟩
  str := HostChoiceContextualCoalgebraFinality.liftCoalgebra (classCoalgebra worlds arrows)

noncomputable def finalMap (source : Endofunctor.Coalgebra (futurePower (D := D) :
    HostChoiceContextualCoalgebraFinality.Ambient.{u,v} D ⥤
      HostChoiceContextualCoalgebraFinality.Ambient.{u,v} D)) :
    source ⟶ finalCoalgebra worlds arrows where
  f := (readout worlds arrows source.str).comp
    (HostChoiceContextualCoalgebraFinality.raise (classFamily worlds arrows))
  h := ContextualSmallCoalgebraComparisons.compose_square source.str (classCoalgebra worlds arrows)
    (HostChoiceContextualCoalgebraFinality.liftCoalgebra (classCoalgebra worlds arrows))
    (readout worlds arrows source.str) (HostChoiceContextualCoalgebraFinality.raise _)
    (readout_square worlds arrows source.str)
    (HostChoiceContextualCoalgebraFinality.raise_square (classCoalgebra worlds arrows))

theorem finalMap_unique (source : Endofunctor.Coalgebra (futurePower (D := D) :
    HostChoiceContextualCoalgebraFinality.Ambient.{u,v} D ⥤
      HostChoiceContextualCoalgebraFinality.Ambient.{u,v} D))
    (candidate : source ⟶ finalCoalgebra worlds arrows) :
    candidate = finalMap worlds arrows source := by
  apply Endofunctor.Coalgebra.ext
  exact HostChoiceContextualCoalgebraFinality.maps_equal_into_lift source.str
    (classCoalgebra worlds arrows) (class_separated worlds arrows)
    candidate.f (finalMap worlds arrows source).f candidate.h (finalMap worlds arrows source).h

noncomputable def isTerminal : Limits.IsTerminal (finalCoalgebra worlds arrows :
    Endofunctor.Coalgebra (futurePower : HostChoiceContextualCoalgebraFinality.Ambient.{u,v} D ⥤
      HostChoiceContextualCoalgebraFinality.Ambient.{u,v} D)) :=
  Limits.IsTerminal.ofUniqueHom (finalMap worlds arrows) (finalMap_unique worlds arrows)

theorem finalMap_kernel (source : Endofunctor.Coalgebra (futurePower (D := D) :
    HostChoiceContextualCoalgebraFinality.Ambient.{u,v} D ⥤
      HostChoiceContextualCoalgebraFinality.Ambient.{u,v} D))
    (point : D) (first second : source.V.interpretation.obj point) :
    (finalMap worlds arrows source).f.app point first =
        (finalMap worlds arrows source).f.app point second ↔
      ContextualCoalgebraBisimulation.Bisimilar source.str point first second := by
  change ULift.up ((readout worlds arrows source.str).app point first) =
    ULift.up ((readout worlds arrows source.str).app point second) ↔ _
  exact (Equiv.ulift.symm.injective.eq_iff).trans
    (readout_kernel worlds arrows source.str point first second)

/-- Both independently constructed final coalgebras are compared by their universal maps. -/
noncomputable def rawMaterialIso :
    (HostChoiceContextualCoalgebraFinality.finalCoalgebra (D := D) :
      Endofunctor.Coalgebra (futurePower : HostChoiceContextualCoalgebraFinality.Ambient.{u,v} D ⥤
        HostChoiceContextualCoalgebraFinality.Ambient.{u,v} D)) ≅ finalCoalgebra worlds arrows where
  hom := finalMap worlds arrows HostChoiceContextualCoalgebraFinality.finalCoalgebra
  inv := HostChoiceContextualCoalgebraFinality.finalMap (finalCoalgebra worlds arrows)
  hom_inv_id := HostChoiceContextualCoalgebraFinality.isTerminal.hom_ext _ _
  inv_hom_id := (isTerminal worlds arrows).hom_ext _ _

def decode (point : D) :
    (finalCoalgebra.{u,v} worlds arrows).V.interpretation.obj point →
      ContextualSmallCoalgebraMaterialCarrier.Members worlds arrows point :=
  fun value => (classToMembers worlds arrows).app point value.down

theorem decode_restriction {first second : D} (step : first ⟶ second)
    (value : (finalCoalgebra.{u,v} worlds arrows).V.interpretation.obj first) :
    (ContextualSmallCoalgebraMaterialCarrier.family worlds arrows).map step
        (decode worlds arrows first value) =
      decode worlds arrows second
        ((finalCoalgebra worlds arrows).V.interpretation.map step value) :=
  (classToMembers worlds arrows).naturality step value.down

theorem decode_kernel (point : D)
    (first second : (finalCoalgebra.{u,v} worlds arrows).V.interpretation.obj point) :
    decode worlds arrows point first = decode worlds arrows point second ↔ first = second := by
  constructor
  · intro same
    apply ULift.ext
    exact (memberEquiv worlds arrows point).injective same
  · rintro rfl
    rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceMaterialCoalgebraFinality
