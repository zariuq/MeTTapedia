import Mettapedia.OSLF.Syntax.CartesianModelLexPropertyTransport
import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Representability of generated presheaf interpretations

A left-exact interpretation into presheaves whose authored-context values
are representable has representable values on every relative finite
presentation. This is the objectwise step needed to descend a presheaf
extension back to an arbitrary finitely complete target.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CartesianContextModels

open CategoryTheory CategoryTheory.Limits
open Mettapedia.OSLF.Binding (FiniteLimitShape finiteLimitDiagram)

variable (C : Type) [SmallCategory C] [HasFiniteProducts C]
variable (D : Type) [SmallCategory D] [HasFiniteLimits D]

/-- Presheaves represented by objects of the target category. -/
def RepresentableTargetPresheaves : ObjectProperty (Dᵒᵖ ⥤ Type) :=
  (yoneda : D ⥤ Dᵒᵖ ⥤ Type).essImage

/-- Representability propagates from the authored contexts through every
finite-limit presentation, because Yoneda is fully faithful and preserves
finite limits. -/
theorem representable_of_authoredContexts
    (T : LeftExactTargetInterpretations C (Dᵒᵖ ⥤ Type))
    (hbase : ∀ X : C,
      RepresentableTargetPresheaves D (T.1.obj ((authoredContext C).obj X)))
    (X : FinitePresentationObjects C) :
    RepresentableTargetPresheaves D (T.1.obj X) := by
  have : (RepresentableTargetPresheaves D).IsClosedUnderIsomorphisms := by
    dsimp [RepresentableTargetPresheaves]
    infer_instance
  have (a : FiniteLimitShape) :
      (RepresentableTargetPresheaves D).IsClosedUnderLimitsOfShape
        (finiteLimitDiagram a) := by
    have : FinCategory (finiteLimitDiagram a) := by
      cases a <;> dsimp [finiteLimitDiagram] <;> infer_instance
    dsimp [RepresentableTargetPresheaves]
    infer_instance
  exact targetProperty_of_authoredContexts C (Dᵒᵖ ⥤ Type)
    T (RepresentableTargetPresheaves D) hbase X

end Mettapedia.OSLF.CartesianContextModels
