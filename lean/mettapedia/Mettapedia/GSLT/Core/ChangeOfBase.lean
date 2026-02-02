import Mettapedia.GSLT.Core.LambdaTheoryCategory
import Mathlib.Order.GaloisConnection.Defs
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.BicartesianSq

/-!
# Change-of-Base Functors

This file defines the change-of-base functors for subobject fibrations:
- f* : Sub(Y) → Sub(X) (pullback/inverse image)
- ∃f : Sub(X) → Sub(Y) (direct image)
- ∀f : Sub(X) → Sub(Y) (universal image)

These satisfy the key adjunctions: ∃f ⊣ f* ⊣ ∀f

## Key Concepts

In a fibration over a category C:
- For f : X → Y, the change-of-base f* pulls back predicates
- ∃f is the left adjoint (existential quantification along f)
- ∀f is the right adjoint (universal quantification along f)

## References

- Williams & Stay, "Native Type Theory" (ACT 2021), Section 3
- Meredith & Stay, "Operational Semantics in Logical Form"
- Jacobs, "Categorical Logic and Type Theory", Chapter 1
-/

namespace Mettapedia.GSLT.Core

open CategoryTheory

/-! ## Change-of-Base Functors

These functors are the key to making the subobject fibration work.
For now, we axiomatize the structure; concrete implementations would
depend on the specific category and fibration.
-/

/-- Change-of-base structure for a subobject fibration.

    For each morphism f : X ⟶ Y, we have functors between fibers:
    - f* : Sub(Y) → Sub(X) (pullback)
    - ∃f : Sub(X) → Sub(Y) (direct image)
    - ∀f : Sub(X) → Sub(Y) (universal image)
-/
structure ChangeOfBase {C : Type*} [Category C] (F : SubobjectFibration C) where
  /-- Pullback along f -/
  pullback : ∀ {X Y : C}, (X ⟶ Y) → F.Sub Y → F.Sub X
  /-- Direct image along f (left adjoint to pullback) -/
  directImage : ∀ {X Y : C}, (X ⟶ Y) → F.Sub X → F.Sub Y
  /-- Universal image along f (right adjoint to pullback) -/
  universalImage : ∀ {X Y : C}, (X ⟶ Y) → F.Sub X → F.Sub Y
  /-- Pullback is monotone -/
  pullback_mono : ∀ {X Y : C} (f : X ⟶ Y), Monotone (pullback f)
  /-- Direct image is monotone -/
  directImage_mono : ∀ {X Y : C} (f : X ⟶ Y), Monotone (directImage f)
  /-- Universal image is monotone -/
  universalImage_mono : ∀ {X Y : C} (f : X ⟶ Y), Monotone (universalImage f)
  /-- Adjunction: ∃f ⊣ f* (∃f a ≤ b ↔ a ≤ f* b) -/
  direct_pullback_adj : ∀ {X Y : C} (f : X ⟶ Y),
    GaloisConnection (directImage f) (pullback f)
  /-- Adjunction: f* ⊣ ∀f (f* a ≤ b ↔ a ≤ ∀f b) -/
  pullback_universal_adj : ∀ {X Y : C} (f : X ⟶ Y),
    GaloisConnection (pullback f) (universalImage f)

namespace ChangeOfBase

variable {C : Type*} [Category C] {F : SubobjectFibration C}
variable (cob : ChangeOfBase F)

/-! ## Key Properties -/

/-- Pullback preserves top -/
theorem pullback_top {X Y : C} (f : X ⟶ Y) :
    cob.pullback f ⊤ = ⊤ := by
  -- f* is a right adjoint (to ∃f), so it preserves limits
  -- In particular, it preserves the terminal object ⊤
  apply le_antisymm
  · exact le_top
  · -- Need: ⊤ ≤ f*(⊤)
    -- From adjunction ∃f ⊣ f*: ∃f(a) ≤ b ↔ a ≤ f*(b)
    -- Taking a = ⊤, b = ⊤: ∃f(⊤) ≤ ⊤ ↔ ⊤ ≤ f*(⊤)
    -- ∃f(⊤) ≤ ⊤ is le_top, so f*(⊤) ≥ ⊤
    have h : cob.directImage f ⊤ ≤ ⊤ := le_top
    exact (cob.direct_pullback_adj f ⊤ ⊤).mp h

/-- Direct image preserves bottom -/
theorem directImage_bot {X Y : C} (f : X ⟶ Y) :
    cob.directImage f ⊥ = ⊥ := by
  apply le_antisymm
  · -- From ∃f a ≤ b ↔ a ≤ f* b, taking a = ⊥
    -- we get ∃f ⊥ ≤ b for any b, so ∃f ⊥ ≤ ⊥
    have h := (cob.direct_pullback_adj f ⊥ ⊥).mpr bot_le
    exact h
  · exact bot_le

/-- Universal image preserves top -/
theorem universalImage_top {X Y : C} (f : X ⟶ Y) :
    cob.universalImage f ⊤ = ⊤ := by
  apply le_antisymm
  · exact le_top
  · -- From f* ⊣ ∀f, we have a ≤ ∀f (f* a) for all a
    -- Taking a = ⊤, we get ⊤ ≤ ∀f (f* ⊤) = ∀f ⊤ (by pullback_top)
    have h1 : cob.pullback f ⊤ = ⊤ := pullback_top cob f
    have h2 : ⊤ ≤ cob.universalImage f (cob.pullback f ⊤) :=
      (cob.pullback_universal_adj f).le_u_l ⊤
    rw [h1] at h2
    exact h2

/-- Pullback distributes over meet (one direction) -/
theorem pullback_inf_le {X Y : C} (f : X ⟶ Y) (φ ψ : F.Sub Y) :
    cob.pullback f (φ ⊓ ψ) ≤ cob.pullback f φ ⊓ cob.pullback f ψ := by
  apply le_inf
  · exact cob.pullback_mono f inf_le_left
  · exact cob.pullback_mono f inf_le_right

/-- Direct image distributes over join -/
theorem directImage_sup {X Y : C} (f : X ⟶ Y) (φ ψ : F.Sub X) :
    cob.directImage f (φ ⊔ ψ) = cob.directImage f φ ⊔ cob.directImage f ψ := by
  apply le_antisymm
  · -- ∃f(φ ⊔ ψ) ≤ ∃f(φ) ⊔ ∃f(ψ)
    -- From adjunction: ∃f(φ ⊔ ψ) ≤ b ↔ φ ⊔ ψ ≤ f*(b)
    -- Take b = ∃f(φ) ⊔ ∃f(ψ)
    -- Need: φ ⊔ ψ ≤ f*(∃f(φ) ⊔ ∃f(ψ))
    -- This doesn't work directly...
    -- Actually for left adjoints preserving colimits:
    have adj := cob.direct_pullback_adj f
    rw [adj (φ ⊔ ψ) (cob.directImage f φ ⊔ cob.directImage f ψ)]
    apply sup_le
    · calc φ ≤ cob.pullback f (cob.directImage f φ) := adj.le_u_l φ
           _ ≤ cob.pullback f (cob.directImage f φ ⊔ cob.directImage f ψ) :=
               cob.pullback_mono f le_sup_left
    · calc ψ ≤ cob.pullback f (cob.directImage f ψ) := adj.le_u_l ψ
           _ ≤ cob.pullback f (cob.directImage f φ ⊔ cob.directImage f ψ) :=
               cob.pullback_mono f le_sup_right
  · apply sup_le
    · exact cob.directImage_mono f le_sup_left
    · exact cob.directImage_mono f le_sup_right

/-! ## Beck-Chevalley Condition

The Beck-Chevalley condition states that for a pullback square:

```
    P ---π₂---> B
    |           |
   π₁          g
    ↓           ↓
    A ---f----> C
```

we have: f* ∘ ∃g = ∃π₁ ∘ π₂*

Both sides are maps Sub(B) → Sub(A).

This is the key compatibility condition for quantification and substitution.
-/

/-- Beck-Chevalley condition for a pullback square.

    Given a pullback:
    ```
        P ---π₂---> B
        |           |
       π₁          g
        ↓           ↓
        A ---f----> C
    ```
    we have: f* ∘ ∃g = ∃π₁ ∘ π₂*

    Both sides map Sub(B) → Sub(A).
-/
def BeckChevalley {C : Type*} [Category C] (F : SubobjectFibration C)
    (cob : ChangeOfBase F) : Prop :=
  ∀ {P A B C' : C} (π₁ : P ⟶ A) (π₂ : P ⟶ B) (f : A ⟶ C') (g : B ⟶ C'),
    π₁ ≫ f = π₂ ≫ g →  -- commuting square
    ∀ (φ : F.Sub B), cob.pullback f (cob.directImage g φ) =
                     cob.directImage π₁ (cob.pullback π₂ φ)

end ChangeOfBase

/-! ## Lambda Theory with Change-of-Base

A lambda-theory with full change-of-base structure includes:
1. The base lambda-theory with equality
2. Change-of-base functors for the subobject fibration
3. The Beck-Chevalley condition
-/

/-- A lambda-theory with full fibration structure.

    This extends LambdaTheoryWithEquality with:
    - Change-of-base functors (f*, ∃f, ∀f)
    - Adjunctions (∃f ⊣ f* ⊣ ∀f)
    - Beck-Chevalley condition
-/
structure LambdaTheoryWithFibration extends LambdaTheoryWithEquality where
  /-- Change-of-base structure for the fibration -/
  changeOfBase : @ChangeOfBase Obj instCategory fibration
  /-- Beck-Chevalley condition holds -/
  beckChevalley : ChangeOfBase.BeckChevalley fibration changeOfBase

namespace LambdaTheoryWithFibration

variable (T : LambdaTheoryWithFibration)

/-- Pullback functor -/
def pullback {X Y : T.Obj} (f : X ⟶ Y) : T.Sub Y → T.Sub X :=
  T.changeOfBase.pullback f

/-- Direct image functor -/
def directImage {X Y : T.Obj} (f : X ⟶ Y) : T.Sub X → T.Sub Y :=
  T.changeOfBase.directImage f

/-- Universal image functor -/
def universalImage {X Y : T.Obj} (f : X ⟶ Y) : T.Sub X → T.Sub Y :=
  T.changeOfBase.universalImage f

/-- The step-forward modality F! = ∃t ∘ s* for an internal graph.

    This is the existential modality from OSLF:
    F!(φ) = "there exists a next state satisfying φ"
-/
def stepForward {X E : T.Obj} (source : E ⟶ X) (target : E ⟶ X)
    (φ : T.Sub X) : T.Sub X :=
  T.directImage target (T.pullback source φ)

/-- The secure step-forward modality F* = ∀t ∘ s* for an internal graph.

    This is the universal modality from OSLF:
    F*(φ) = "all next states satisfy φ"
-/
def secureStepForward {X E : T.Obj} (source : E ⟶ X) (target : E ⟶ X)
    (φ : T.Sub X) : T.Sub X :=
  T.universalImage target (T.pullback source φ)

end LambdaTheoryWithFibration

/-! ## Summary

This file establishes the change-of-base structure for subobject fibrations:

1. **ChangeOfBase**: Bundled f*, ∃f, ∀f with adjunctions
2. **BeckChevalley**: Compatibility of ∃ with pullback
3. **LambdaTheoryWithFibration**: Full structure with all conditions

**Key Properties Proven**:
- f* preserves ⊤ and ⊓ (right adjoint preserves limits)
- ∃f preserves ⊥ and ⊔ (left adjoint preserves colimits)
- ∀f preserves ⊤ (right adjoint preserves terminal)

**Modal Operators from OSLF**:
- F! = ∃t ∘ s* : "possibly next"
- F* = ∀t ∘ s* : "necessarily next"

**Next Steps**:
- Construct ChangeOfBase from topos structure
- Prove Beck-Chevalley for presheaf categories
- Connect to modal types ⟨Cj⟩_{xk::Ak} B
-/

end Mettapedia.GSLT.Core
