import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone

/-!
# Gluing a disjoint extension by coproduct

Let `baseToLeft : Base ⟶ Left` be any map.  If `Base ⨿ Extension` and
`Left ⨿ Extension` are supplied as actual categorical coproducts, then the
canonical square

```text
           Base
          /    \
       Left   Base ⨿ Extension
          \    /
       Left ⨿ Extension
```

is a pushout.  This is the general categorical fact behind gluing two
independent extensions of a common base.  It says nothing about whether a
particular list merge, syntax translation, operational semantics, or model
interpretation realizes the displayed coproducts; those are separate
obligations for each application.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.CoproductExtensionPushout

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits

universe v u

variable {C : Type u} [_root_.CategoryTheory.Category.{v} C]
variable {Base Extension Left : C}

/-- The canonical map from `Base ⨿ Extension` to `Left ⨿ Extension`: use
`baseToLeft` on the shared base and the identity inclusion on the extension. -/
noncomputable def rightLeg
    (baseToLeft : Base ⟶ Left)
    (baseExtension : BinaryCofan Base Extension)
    (baseExtensionIsCoproduct : IsColimit baseExtension)
    (leftExtension : BinaryCofan Left Extension) :
    baseExtension.pt ⟶ leftExtension.pt :=
  BinaryCofan.IsColimit.desc baseExtensionIsCoproduct
    (baseToLeft ≫ leftExtension.inl) leftExtension.inr

@[reassoc]
theorem base_inclusion_rightLeg
    (baseToLeft : Base ⟶ Left)
    (baseExtension : BinaryCofan Base Extension)
    (baseExtensionIsCoproduct : IsColimit baseExtension)
    (leftExtension : BinaryCofan Left Extension) :
    baseExtension.inl ≫
        rightLeg baseToLeft baseExtension baseExtensionIsCoproduct
          leftExtension =
      baseToLeft ≫ leftExtension.inl :=
  BinaryCofan.IsColimit.inl_desc baseExtensionIsCoproduct _ _

@[reassoc]
theorem extension_inclusion_rightLeg
    (baseToLeft : Base ⟶ Left)
    (baseExtension : BinaryCofan Base Extension)
    (baseExtensionIsCoproduct : IsColimit baseExtension)
    (leftExtension : BinaryCofan Left Extension) :
    baseExtension.inr ≫
        rightLeg baseToLeft baseExtension baseExtensionIsCoproduct
          leftExtension =
      leftExtension.inr :=
  BinaryCofan.IsColimit.inr_desc baseExtensionIsCoproduct _ _

/-- The canonical gluing square for adjoining the same independent extension
to the base and to its image in `Left`. -/
noncomputable def cocone
    (baseToLeft : Base ⟶ Left)
    (baseExtension : BinaryCofan Base Extension)
    (baseExtensionIsCoproduct : IsColimit baseExtension)
    (leftExtension : BinaryCofan Left Extension) :
    PushoutCocone baseToLeft baseExtension.inl :=
  PushoutCocone.mk leftExtension.inl
    (rightLeg baseToLeft baseExtension baseExtensionIsCoproduct leftExtension)
    (base_inclusion_rightLeg baseToLeft baseExtension
      baseExtensionIsCoproduct leftExtension).symm

set_option backward.isDefEq.respectTransparency false in
/-- **Disjoint-extension gluing theorem.**  The canonical square is a genuine
pushout whenever its two displayed sums are genuine coproducts. -/
noncomputable def isColimit
    (baseToLeft : Base ⟶ Left)
    (baseExtension : BinaryCofan Base Extension)
    (baseExtensionIsCoproduct : IsColimit baseExtension)
    (leftExtension : BinaryCofan Left Extension)
    (leftExtensionIsCoproduct : IsColimit leftExtension) :
    IsColimit
      (cocone baseToLeft baseExtension baseExtensionIsCoproduct
        leftExtension) :=
  PushoutCocone.IsColimit.mk
    (base_inclusion_rightLeg baseToLeft baseExtension
      baseExtensionIsCoproduct leftExtension).symm
    (fun target =>
      BinaryCofan.IsColimit.desc leftExtensionIsCoproduct target.inl
        (baseExtension.inr ≫ target.inr))
    (fun target =>
      BinaryCofan.IsColimit.inl_desc leftExtensionIsCoproduct _ _)
    (fun target => by
      apply BinaryCofan.IsColimit.hom_ext baseExtensionIsCoproduct
      · rw [← Category.assoc,
          base_inclusion_rightLeg baseToLeft baseExtension
            baseExtensionIsCoproduct leftExtension,
          Category.assoc,
          BinaryCofan.IsColimit.inl_desc]
        exact target.condition
      · rw [← Category.assoc,
          extension_inclusion_rightLeg baseToLeft baseExtension
            baseExtensionIsCoproduct leftExtension,
          BinaryCofan.IsColimit.inr_desc])
    (fun target mediator leftTriangle rightTriangle => by
      apply BinaryCofan.IsColimit.hom_ext leftExtensionIsCoproduct
      · rw [leftTriangle, BinaryCofan.IsColimit.inl_desc]
      · calc
          leftExtension.inr ≫ mediator =
              (baseExtension.inr ≫
                rightLeg baseToLeft baseExtension
                  baseExtensionIsCoproduct leftExtension) ≫ mediator := by
                exact congrArg (fun arrow => arrow ≫ mediator)
                  (extension_inclusion_rightLeg baseToLeft baseExtension
                    baseExtensionIsCoproduct leftExtension).symm
          _ = baseExtension.inr ≫
                (rightLeg baseToLeft baseExtension
                  baseExtensionIsCoproduct leftExtension ≫ mediator) := by
                exact Category.assoc _ _ _
          _ = baseExtension.inr ≫ target.inr := by rw [rightTriangle]
          _ = leftExtension.inr ≫
                BinaryCofan.IsColimit.desc leftExtensionIsCoproduct
                  target.inl (baseExtension.inr ≫ target.inr) := by
                rw [BinaryCofan.IsColimit.inr_desc])

/-! ## Positive and negative controls in `Type` -/

namespace Canary

open _root_.CategoryTheory.Limits.Types

def emptyToUnit : (PEmpty : Type) ⟶ Unit :=
  ↾(fun empty : PEmpty => nomatch empty)

/-- Two independent unit extensions of the empty base form a genuine
pushout with two distinct points in the apex. -/
noncomputable def independentUnitsPushout :
    IsColimit
      (cocone emptyToUnit
        (binaryCoproductCocone PEmpty Unit)
        (binaryCoproductColimit PEmpty Unit)
        (binaryCoproductCocone Unit Unit)) :=
  isColimit emptyToUnit
    (binaryCoproductCocone PEmpty Unit)
    (binaryCoproductColimit PEmpty Unit)
    (binaryCoproductCocone Unit Unit)
    (binaryCoproductColimit Unit Unit)

/-- Illegitimately identifying the two independent unit extensions into one
unit gives a commuting square, but not a pushout. -/
def collapsedIndependentUnits :
    PushoutCocone emptyToUnit emptyToUnit :=
  PushoutCocone.mk (𝟙 (Unit : Type)) (𝟙 (Unit : Type)) (by simp)

theorem collapsedIndependentUnits_not_colimit :
    ¬ Nonempty (IsColimit collapsedIndependentUnits) := by
  rintro ⟨universal⟩
  let separated : PushoutCocone emptyToUnit emptyToUnit :=
    PushoutCocone.mk (↾(fun _ : Unit => false))
      (↾(fun _ : Unit => true)) (by
        ext empty
        exact nomatch empty)
  let mediator := universal.desc separated
  have leftTriangle := universal.fac separated WalkingSpan.left
  have rightTriangle := universal.fac separated WalkingSpan.right
  change (𝟙 (Unit : Type)) ≫ mediator = (↾(fun _ : Unit => false)) at leftTriangle
  change (𝟙 (Unit : Type)) ≫ mediator = (↾(fun _ : Unit => true)) at rightTriangle
  rw [Category.id_comp] at leftTriangle rightTriangle
  have leftValue := ConcreteCategory.congr_hom leftTriangle ()
  have rightValue := ConcreteCategory.congr_hom rightTriangle ()
  change mediator () = false at leftValue
  change mediator () = true at rightValue
  exact Bool.noConfusion (leftValue.symm.trans rightValue)

end Canary

#print axioms rightLeg
#print axioms base_inclusion_rightLeg
#print axioms extension_inclusion_rightLeg
#print axioms isColimit
#print axioms Canary.independentUnitsPushout
#print axioms Canary.collapsedIndependentUnits_not_colimit

end Mettapedia.CategoryTheory.CoproductExtensionPushout
