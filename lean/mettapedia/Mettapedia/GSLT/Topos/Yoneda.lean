import Mettapedia.GSLT.Core.LambdaTheoryCategory
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Yoneda
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

/-!
# Yoneda Embedding for Lambda Theories

This file connects Mathlib's Yoneda embedding to our lambda theory structures,
establishing the presheaf category Psh(T) for a lambda theory T.

## Main Definitions

* `Presheaf` - The presheaf category Psh(T) = Tᵒᵖ ⥤ Type
* Properties of Yoneda (fully faithful, preserves limits)

## Key Insights

For a lambda theory T (a CCC with finite limits):
- The Yoneda embedding y : T → Psh(T) is fully faithful
- Psh(T) is a presheaf topos (CCC with all limits/colimits)
- y preserves finite limits (hence products and terminal object)

The presheaf topos Psh(T) provides the ambient category for
constructing native types via the Grothendieck construction.

## References

- Williams & Stay, "Native Type Theory" (ACT 2021), §3
- Mac Lane & Moerdijk, "Sheaves in Geometry and Logic", Chapter I
- Mathlib `CategoryTheory.Yoneda`
-/

namespace Mettapedia.GSLT.Topos

open CategoryTheory
open CategoryTheory.Limits

universe u v w

/-! ## Theorem-to-Source Map

Core provenance used by this module:

- `lambdaYoneda`, `yonedaEquiv`:
  Yoneda embedding and hom-equivalence (Mac Lane–Moerdijk, Ch. I.1;
  Mathlib `CategoryTheory.Yoneda`).
- `lambdaYonedaFullyFaithful`, `lambdaYonedaPreservesLimits`:
  fully faithfulness and limit preservation of Yoneda (Mathlib theorems
  `Yoneda.fullyFaithful`, `yonedaFunctor_preservesLimits`).
- `presheafHasLimits` / `presheafHasColimits` / finite variants:
  presheaf topos completeness/cocompleteness backbone (Mac Lane–Moerdijk,
  Ch. I; instantiated through Mathlib typeclass infrastructure). -/

/-! ## Presheaf Category

For a category C, the presheaf category Psh(C) = Cᵒᵖ ⥤ Type
consists of contravariant functors from C to sets.
-/

/-- The presheaf category over a category C -/
abbrev Presheaf (C : Type u) [Category.{v} C] := Cᵒᵖ ⥤ Type v

/-- Alternative notation for presheaves -/
notation "Psh(" C ")" => Presheaf C

/-! ## Yoneda Embedding

The Yoneda embedding y : C → Psh(C) sends each object X to the
representable presheaf Hom(-, X).

We use Mathlib's `yoneda` directly, which has all the key properties:
- Fully faithful (Yoneda.fullyFaithful)
- Full (yoneda_full)
- Faithful (yoneda_faithful)
- Preserves limits (yonedaFunctor_preservesLimits)
-/

/-- The Yoneda embedding is fully faithful (re-export from Mathlib) -/
example (C : Type u) [Category.{v} C] : (yoneda (C := C)).FullyFaithful :=
  Yoneda.fullyFaithful

/-- Yoneda preserves all limits (re-export from Mathlib) -/
example (C : Type u) [Category.{v} C] : PreservesLimits (yoneda (C := C)) :=
  yonedaFunctor_preservesLimits

/-! ## Yoneda for Lambda Theories

For a lambda theory T (CCC with finite limits), we establish
that the Yoneda embedding preserves the relevant structure.
-/

section LambdaTheory

open Mettapedia.GSLT.Core

variable (T : LambdaTheoryWithEquality)

/-- The Yoneda embedding for a lambda theory's underlying category -/
def lambdaYoneda : T.Obj ⥤ Psh(T.Obj) := yoneda

/-- The Yoneda embedding is fully faithful -/
instance lambdaYonedaFullyFaithful : (lambdaYoneda T).FullyFaithful :=
  Yoneda.fullyFaithful

/-- Yoneda preserves all limits for lambda theories -/
instance lambdaYonedaPreservesLimits : PreservesLimits (lambdaYoneda T) :=
  yonedaFunctor_preservesLimits

/-- The representable presheaf y(X) for an object X in T -/
def representable (X : T.Obj) : Psh(T.Obj) := (lambdaYoneda T).obj X

/-- Natural transformations y(X) → y(Y) correspond to morphisms X → Y -/
def yonedaEquiv (X Y : T.Obj) :
    ((lambdaYoneda T).obj X ⟶ (lambdaYoneda T).obj Y) ≃ (X ⟶ Y) :=
  (lambdaYonedaFullyFaithful T).homEquiv.symm

end LambdaTheory

/-! ## Presheaf Topos Structure

The category Psh(C) is a topos: it has all limits and colimits,
is cartesian closed, and has a subobject classifier.
-/

/-- Psh(C) has all limits -/
instance presheafHasLimits (C : Type u) [SmallCategory C] :
    HasLimits (Psh(C)) := inferInstance

/-- Psh(C) has all colimits -/
instance presheafHasColimits (C : Type u) [SmallCategory C] :
    HasColimits (Psh(C)) := inferInstance

/-- Psh(C) has finite limits -/
instance presheafHasFiniteLimits (C : Type u) [SmallCategory C] :
    HasFiniteLimits (Psh(C)) := inferInstance

/-- Psh(C) has finite colimits -/
instance presheafHasFiniteColimits (C : Type u) [SmallCategory C] :
    HasFiniteColimits (Psh(C)) := inferInstance

/-! ## Summary

This file establishes the Yoneda embedding for lambda theories:

1. **Presheaf**: Psh(C) = Cᵒᵖ ⥤ Type (presheaf category)
2. **lambdaYoneda**: y : T.Obj → Psh(T.Obj) (fully faithful)
3. **Limit preservation**: y preserves all limits

**Key Properties**:
- y is fully faithful (embeds C into Psh(C) faithfully)
- y preserves finite limits (products, terminal, pullbacks)
- Psh(C) is a topos (all limits/colimits, cartesian closed)

**Next Steps**:
- `SubobjectClassifier.lean`: The subobject classifier Ω
- `PredicateFibration.lean`: The fibration πΩ with Beck-Chevalley
-/

end Mettapedia.GSLT.Topos
