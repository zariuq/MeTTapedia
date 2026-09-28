import Mettapedia.OSLF.Syntax.FiniteLimitGeneratedPresheaves
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# The context embedding preserves authored finite products

Represented contexts land in the finite-limit-generated presheaf category.
The embedding is Yoneda after the full-subcategory inclusion. Consequently it
preserves the terminal context and binary products already present in syntax.
This constrains the domain of any free finite-limit universal property: maps
out of the authored context category must preserve its existing products.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding

open CategoryTheory
open CategoryTheory.Limits

variable (S : Signature)

/-- Send an authored substitution context to its represented presheaf inside
the finite-limit-generated full subcategory. -/
def contextIntoFiniteLimitGenerated : Syntactic.Ctxt S ⥤
    (finiteLimitGenerated S).FullSubcategory :=
  Mettapedia.OSLF.FiniteLimitYoneda.intoGenerated (Syntactic.Ctxt S)

/-- Forgetting the closure condition recovers the ordinary Yoneda embedding
on both contexts and substitutions. -/
theorem contextIntoFiniteLimitGenerated_comp_inclusion :
    contextIntoFiniteLimitGenerated S ⋙ (finiteLimitGenerated S).ι = yoneda :=
  Mettapedia.OSLF.FiniteLimitYoneda.intoGenerated_comp_inclusion
    (Syntactic.Ctxt S)

/-- Distinct authored substitutions remain distinct in the generated category. -/
instance contextIntoFiniteLimitGenerated_faithful :
    (contextIntoFiniteLimitGenerated S).Faithful :=
  Mettapedia.OSLF.FiniteLimitYoneda.intoGenerated_faithful
    (Syntactic.Ctxt S)

/-- Every map between represented contexts in the generated full subcategory
comes from a unique authored substitution. -/
instance contextIntoFiniteLimitGenerated_full :
    (contextIntoFiniteLimitGenerated S).Full :=
  Mettapedia.OSLF.FiniteLimitYoneda.intoGenerated_full
    (Syntactic.Ctxt S)

/-- Existing finite products of authored contexts survive the embedding.
The proof uses Yoneda's limit preservation and reflection by the fully
faithful inclusion, not an assumed free-completion property. -/
theorem contextIntoFiniteLimitGenerated_preservesFiniteProducts :
    PreservesFiniteProducts (contextIntoFiniteLimitGenerated S) :=
  Mettapedia.OSLF.FiniteLimitYoneda.intoGenerated_preservesFiniteProducts
    (Syntactic.Ctxt S)

end Mettapedia.OSLF.Binding
