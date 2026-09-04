import Mettapedia.CategoryTheory.CoproductExtensionPushout
import Mettapedia.GSLT.LanguageDef.StructuralLanguageDefCategory

/-!
# Disjoint-extension gluing for validated language definitions

Suppose `LeftIncrement` and `RightIncrement` are independently adjoined to a
common `Base`, and the right increment can also be adjoined to the resulting
left language.  When all three structural sums satisfy `Compatibility`, the
canonical square of validated declaration data is a pushout:

```text
                    Base
                   /    \
    Base + LeftIncrement  Base + RightIncrement
                   \    /
       (Base + LeftIncrement) + RightIncrement
```

The universal property is inherited from the proved structural coproducts.
It concerns declaration-preserving maps only.  Operational semantics, typing,
models, and observations require their own preservation theorems.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.StructuralLanguageDefCategory
namespace DisjointExtensionGluing

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuralCoproduct

variable {Base LeftIncrement RightIncrement : ValidatedLanguageDef}

variable {leftName rightName combinedName : String}

variable
  {baseIntoLeft leftIncrementIntoLeft : LanguageDefSymbolMap}
  {baseIntoRight rightIncrementIntoRight : LanguageDefSymbolMap}
  {leftLanguageIntoCombined rightIncrementIntoCombined : LanguageDefSymbolMap}

variable
  (leftCompatibility :
    Compatibility leftName baseIntoLeft leftIncrementIntoLeft
      Base LeftIncrement)
  (rightCompatibility :
    Compatibility rightName baseIntoRight rightIncrementIntoRight
      Base RightIncrement)
  (combinedCompatibility :
    Compatibility combinedName leftLanguageIntoCombined
      rightIncrementIntoCombined leftCompatibility.combinedLanguage
      RightIncrement)

/-- The canonical map from the right extension of the base into the combined
language.  It maps the common base through the left extension and preserves
the independent right increment through its coproduct injection. -/
noncomputable def rightLeg :
    rightCompatibility.combinedLanguage ⟶
      combinedCompatibility.combinedLanguage :=
  Mettapedia.CategoryTheory.CoproductExtensionPushout.rightLeg
    (Coproduct.leftArrow leftCompatibility)
    (Coproduct.cofan rightCompatibility)
    (Coproduct.isColimit rightCompatibility)
    (Coproduct.cofan combinedCompatibility)

/-- The common base has the same image along both routes to the combined
language. -/
@[reassoc]
theorem base_commutes :
    Coproduct.leftArrow rightCompatibility ≫
        rightLeg leftCompatibility rightCompatibility combinedCompatibility =
      Coproduct.leftArrow leftCompatibility ≫
        Coproduct.leftArrow combinedCompatibility :=
  Mettapedia.CategoryTheory.CoproductExtensionPushout.base_inclusion_rightLeg
      (Coproduct.leftArrow leftCompatibility)
      (Coproduct.cofan rightCompatibility)
      (Coproduct.isColimit rightCompatibility)
      (Coproduct.cofan combinedCompatibility)

/-- The right increment is preserved exactly by the canonical right leg. -/
@[reassoc]
theorem rightIncrement_commutes :
    Coproduct.rightArrow rightCompatibility ≫
        rightLeg leftCompatibility rightCompatibility combinedCompatibility =
      Coproduct.rightArrow combinedCompatibility :=
  Mettapedia.CategoryTheory.CoproductExtensionPushout.extension_inclusion_rightLeg
      (Coproduct.leftArrow leftCompatibility)
      (Coproduct.cofan rightCompatibility)
      (Coproduct.isColimit rightCompatibility)
      (Coproduct.cofan combinedCompatibility)

/-- The canonical disjoint-extension square of validated language
definitions. -/
noncomputable def cocone :
    PushoutCocone (Coproduct.leftArrow leftCompatibility)
      (Coproduct.leftArrow rightCompatibility) :=
  Mettapedia.CategoryTheory.CoproductExtensionPushout.cocone
    (Coproduct.leftArrow leftCompatibility)
    (Coproduct.cofan rightCompatibility)
    (Coproduct.isColimit rightCompatibility)
    (Coproduct.cofan combinedCompatibility)

/-- **LanguageDef disjoint-extension theorem.**  Compatible independent
structural extensions glue by a genuine categorical pushout. -/
noncomputable def isColimit :
    IsColimit
      (cocone leftCompatibility rightCompatibility combinedCompatibility) :=
  Mettapedia.CategoryTheory.CoproductExtensionPushout.isColimit
    (Coproduct.leftArrow leftCompatibility)
    (Coproduct.cofan rightCompatibility)
    (Coproduct.isColimit rightCompatibility)
    (Coproduct.cofan combinedCompatibility)
    (Coproduct.isColimit combinedCompatibility)

#print axioms rightLeg
#print axioms base_commutes
#print axioms rightIncrement_commutes
#print axioms isColimit

end DisjointExtensionGluing
end Mettapedia.GSLT.LanguageDef.StructuralLanguageDefCategory
