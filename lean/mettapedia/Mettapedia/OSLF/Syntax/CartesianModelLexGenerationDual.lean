import Mettapedia.OSLF.Syntax.FiniteClosureDuality
import Mettapedia.OSLF.Syntax.CartesianModelFiniteGeneration

/-!
# Finite-limit generation of opposite cartesian models

The strong-generator theorem for finitely presented cartesian models has a
literal dual reading: in the opposite of the ambient model category, the
finitely presented objects form the finite-limit closure of the represented
authored contexts. This statement uses all finite diagram shapes. Transport
into the internal finite-presentation full subcategory remains a separate
comparison, needed for its unrestricted universal property.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CartesianContextModels

open CategoryTheory CategoryTheory.Limits
open Mettapedia.OSLF.Binding (op_colimitsClosure_eq_limitsClosure)

variable (C : Type) [SmallCategory C] [HasFiniteProducts C]

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- In the opposite ambient model category, finitely presented models are
exactly the finite-limit closure of authored context representations. The
finite shapes retain their actual opposite variance. -/
theorem finiteModels_op_eq_authoredContexts_finiteLimitClosure :
    (isCardinalPresentable.{0} (Models C) Cardinal.aleph0.{0}).op =
      (authoredContexts C).op.limitsClosure
        (fun a : SmallCategoryCardinalLT Cardinal.aleph0.{0} =>
          (SmallCategoryCardinalLT.categoryFamily Cardinal.aleph0.{0} a)ᵒᵖ) := by
  rw [finiteModels_eq_authoredContexts_closure C]
  exact op_colimitsClosure_eq_limitsClosure
    (fun a : SmallCategoryCardinalLT Cardinal.aleph0.{0} =>
      SmallCategoryCardinalLT.categoryFamily Cardinal.aleph0.{0} a)
    (authoredContexts C)

end Mettapedia.OSLF.CartesianContextModels
