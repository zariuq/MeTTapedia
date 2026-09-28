import Mettapedia.OSLF.Syntax.CategoricalBindingEventEquivalence
import Mathlib.CategoryTheory.Limits.Shapes.Images

/-!
# The reduction observation of retained events

If the semantic target has images, an endpoint arrow from individual events
to program pairs has a selected image mono. This records the observation
that some firing exists at those endpoints. A map of event-equipped
interpretations always gives a commutative endpoint square. When the target
also supplies maps of images for such squares, the reduction observation
transports forward. Neither image existence nor image-map structure is
inferred from finite limits alone.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalBindingEventImage

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.CategoricalBindingQuotientEquivalence
open Mettapedia.OSLF.Binding.CategoricalBindingEventEquivalence
open Mettapedia.OSLF.Binding.SecondOrderContext

universe u v

variable {S : Signature} {schema : List (MetaArity S)}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable (Eqs : EquationPresentation S schema)
variable (program : EquationContexts Eqs)

/-- The individual events with endpoints in the selected program-pair
object. -/
abbrev EventInterpretation := Comma (𝟭 D) (programPairs Eqs program)

/-- In a target with images, the existence of a firing is the image object
of its endpoint arrow. Individual events remain available separately. -/
noncomputable def reductionImage [HasImages D]
    (T : EventInterpretation (D := D) Eqs program) : D :=
  image T.hom

/-- The reduction observation as a subobject of endpoint pairs. -/
noncomputable def reductionMono [HasImages D]
    (T : EventInterpretation (D := D) Eqs program) :
    reductionImage Eqs program T ⟶ (programPairs Eqs program).obj T.right :=
  image.ι T.hom

theorem event_factors_reduction [HasImages D]
    (T : EventInterpretation (D := D) Eqs program) :
    factorThruImage T.hom ≫ reductionMono Eqs program T = T.hom :=
  image.fac T.hom

/-- Every event-preserving interpretation map gives a square whose top and
bottom arrows are the actual endpoint maps. -/
noncomputable def endpointSquare
    {T U : EventInterpretation (D := D) Eqs program} (f : T ⟶ U) :
    Arrow.mk T.hom ⟶ Arrow.mk U.hom :=
  Arrow.homMk f.left ((programPairs Eqs program).map f.right) (by simpa using f.w)

/-- The ordinary interpretation-map law transports reduction images in the
forward direction, provided image maps exist in the target. It does not
assert target-event coverage or reflection at a chosen source pair. -/
theorem reductionImage_forward [HasImages D] [HasImageMaps D]
    {T U : EventInterpretation (D := D) Eqs program} (f : T ⟶ U) :
    image.map (endpointSquare Eqs program f) ≫ reductionMono Eqs program U =
      reductionMono Eqs program T ≫ (programPairs Eqs program).map f.right :=
  image.map_ι (endpointSquare Eqs program f)

end Mettapedia.OSLF.Binding.CategoricalBindingEventImage

#print axioms Mettapedia.OSLF.Binding.CategoricalBindingEventImage.reductionImage_forward
