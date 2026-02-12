import Mettapedia.GSLT.Topos.SubobjectClassifier
import Mettapedia.GSLT.Core.ChangeOfBase
import Mathlib.CategoryTheory.Subfunctor.Image
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.BicartesianSq

/-!
# Predicate Fibration over Presheaf Categories

This file establishes the predicate fibration πΩ over presheaf categories,
connecting the subobject classifier to the fibration structure.

## Main Definitions

* `PredicateFib` - The fibration πΩ over Psh(C)
* `beckChevalleyPresheaf` - Beck-Chevalley condition for presheaves

## Key Insights

The predicate fibration πΩ assigns to each presheaf P:
- The fiber: Sub(P) = subobjects of P (or morphisms P → Ω)
- These form a complete lattice (Frame structure)

For a morphism f : P → Q in Psh(C):
- Pullback f* : Sub(Q) → Sub(P) is inverse image
- Direct image ∃f : Sub(P) → Sub(Q) is left adjoint
- Universal image ∀f : Sub(P) → Sub(Q) is right adjoint

## References

- Williams & Stay, "Native Type Theory" (ACT 2021), §3
- Johnstone, "Sketches of an Elephant", §A.1.6
- Our `ChangeOfBase.lean` for the general framework
-/

namespace Mettapedia.GSLT.Topos

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Mettapedia.GSLT.Core

universe u v w

/-! ## Theorem-to-Source Map

Primary theorem provenance for the presheaf predicate-fibration path:

- `presheafPredicateFib`:
  predicates/subobjects as presheaf fibers (Mac Lane–Moerdijk, Ch. I.3;
  Jacobs Ch. 1 fibrational perspective).
- `presheafChangeOfBase`:
  reindexing (`f*`) with adjoints (`∃f`, `∀f`) in a fibrational setting
  (Jacobs Ch. 1), implemented concretely via subfunctor image/preimage.
- `beckChevalleyPresheafSubfunctor` and
  `beckChevalleyPresheaf_changeOfBase`:
  pullback base-change equation `f* ∘ ∃g = ∃π₁ ∘ π₂*`
  (Awodey–Bauer §4.4.1; Mac Lane–Moerdijk Ch. I.3).
- `beckChevalleyPresheaf`:
  Mathlib-level subobject base-change identity
  (`Subobject.map_pullback`) for pullback squares.
- `beckChevalleyCondition_presheafChangeOfBase`:
  concrete instantiation of the generic `BeckChevalleyCondition` through
  `presheafChangeOfBase`. -/

/-! ## Abstract Predicate Fibration

We define the predicate fibration abstractly, axiomatizing the key properties
that hold in presheaf toposes. The concrete construction would use sieves
and the subobject classifier Ω.
-/

/-- A predicate fibration over a category C assigns:
    - To each object X, a Frame Sub(X) of "predicates"
    - Change-of-base functors between fibers

    We use Frame (complete Heyting algebra) rather than just CompleteLattice
    because this is required for the quantale structure and type theory. -/
structure PredicateFib (C : Type u) [Category.{v} C] where
  /-- The fiber over each object (predicates/subobjects) -/
  Sub : C → Type w
  /-- Each fiber is a Frame (complete Heyting algebra) -/
  frame : ∀ X, Order.Frame (Sub X)
  /-- Pullback along morphisms -/
  pullback : ∀ {X Y : C}, (X ⟶ Y) → Sub Y → Sub X
  /-- Pullback is monotone -/
  pullback_mono : ∀ {X Y : C} (f : X ⟶ Y), Monotone (pullback f)
  /-- Pullback preserves top -/
  pullback_top : ∀ {X Y : C} (f : X ⟶ Y), pullback f ⊤ = ⊤
  /-- Pullback preserves binary meet -/
  pullback_inf : ∀ {X Y : C} (f : X ⟶ Y) (φ ψ : Sub Y),
    pullback f (φ ⊓ ψ) = pullback f φ ⊓ pullback f ψ

namespace PredicateFib

variable {C : Type u} [Category.{v} C] (F : PredicateFib C)

/-- Instance for the Frame structure on fibers -/
instance instFrame (X : C) : Order.Frame (F.Sub X) := F.frame X

end PredicateFib

/-! ## Presheaf Predicate Fibration

For a small category C, the presheaf category Psh(C) has a predicate fibration
where Sub(P) is the lattice of subobjects of P.
-/

/-- `Subfunctor F` is a frame in presheaf fibers.

    Reference:
    - Mac Lane–Moerdijk (1994), Ch. I.3: presheaf subobject fibers are Heyting.
    - In Mathlib we obtain this via `Order.Frame.ofMinimalAxioms` and
      pointwise distributivity (`Subfunctor.iSup_min`). -/
noncomputable instance presheafSubfunctorFrame
    {C : Type u} [Category.{v} C] (F : C ⥤ Type w) : Order.Frame (CategoryTheory.Subfunctor F) := by
  refine Order.Frame.ofMinimalAxioms ?_
  refine
    { toCompleteLattice := inferInstance
      inf_sSup_le_iSup_inf := ?_ }
  intro a s
  have hs :
      (sSup s : CategoryTheory.Subfunctor F) =
        ⨆ x : s, (x : CategoryTheory.Subfunctor F) := by
    simpa using (sSup_image' (s := s) (f := fun b : CategoryTheory.Subfunctor F => b))
  have hsub :
      a ⊓ (⨆ x : s, (x : CategoryTheory.Subfunctor F)) =
        ⨆ x : s, a ⊓ (x : CategoryTheory.Subfunctor F) := by
    calc
      a ⊓ (⨆ x : s, (x : CategoryTheory.Subfunctor F))
          = (⨆ x : s, (x : CategoryTheory.Subfunctor F)) ⊓ a := by ac_rfl
      _ = ⨆ x : s, ((x : CategoryTheory.Subfunctor F) ⊓ a) :=
          CategoryTheory.Subfunctor.iSup_min
            (S := fun x : s => (x : CategoryTheory.Subfunctor F))
            (T := a)
      _ = ⨆ x : s, a ⊓ (x : CategoryTheory.Subfunctor F) := by
          refine iSup_congr ?_
          intro x
          simp [inf_comm]
  have hEq : a ⊓ sSup s = ⨆ b ∈ s, a ⊓ b := by
    calc
      a ⊓ sSup s = a ⊓ (⨆ x : s, (x : CategoryTheory.Subfunctor F)) := by rw [hs]
      _ = ⨆ x : s, a ⊓ (x : CategoryTheory.Subfunctor F) := hsub
      _ = ⨆ b ∈ s, a ⊓ b := by simp [iSup_subtype]
  exact hEq.le

/-- Ω/subobject-backed predicate fibration over presheaves.

    Fibers are `Subfunctor P`, which are equivalent to both:
    - characteristic maps `P ⟶ Ω` via `natTransEquivSubfunctor`, and
    - `Subobject P` via `Subfunctor.orderIsoSubobject`.

    So this is no longer the prior set-level approximation.

    References:
    - Mac Lane–Moerdijk (1994), Ch. I.3 (subobjects/predicate logic in
      presheaf toposes).
    - Jacobs (1999), Ch. 1 (fibrational predicates and reindexing). -/
noncomputable def presheafPredicateFib (C : Type u) [Category C] :
    PredicateFib (Cᵒᵖ ⥤ Type v) := by
  refine
    { Sub := fun P => CategoryTheory.Subfunctor P
      frame := ?_
      pullback := ?_
      pullback_mono := ?_
      pullback_top := ?_
      pullback_inf := ?_ }
  · intro P
    infer_instance
  · intro P Q f φ
    exact CategoryTheory.Subfunctor.preimage φ f
  · intro P Q f φ ψ hφ U x hx
    exact hφ U hx
  · intro P Q f
    ext U x
    rfl
  · intro P Q f φ ψ
    ext U x
    rfl

/-! ## Concrete Change-of-Base on Presheaf Fibers -/

private theorem subfunctor_preimage_iSup
    {C : Type u} [Category C]
    {X Y : C ⥤ Type v}
    {ι : Type*}
    (f : X ⟶ Y) (G : ι → CategoryTheory.Subfunctor Y) :
    CategoryTheory.Subfunctor.preimage (⨆ i, G i) f =
      ⨆ i, CategoryTheory.Subfunctor.preimage (G i) f := by
  ext U x
  have hleft :
      (⨆ i, G i).obj U = ⋃ i, (G i).obj U :=
    CategoryTheory.Subfunctor.iSup_obj (S := G) (U := U)
  have hright :
      (⨆ i, CategoryTheory.Subfunctor.preimage (G i) f).obj U =
        ⋃ i, (CategoryTheory.Subfunctor.preimage (G i) f).obj U :=
    CategoryTheory.Subfunctor.iSup_obj
      (S := fun i => CategoryTheory.Subfunctor.preimage (G i) f) (U := U)
  change f.app U x ∈ (⨆ i, G i).obj U ↔ x ∈ (⨆ i, (G i).preimage f).obj U
  rw [hleft, hright]
  simp [CategoryTheory.Subfunctor.preimage]

/-- Concrete change-of-base structure on `Psh(C)` for the Ω/subobject-backed
fiber:

- `f*` is subfunctor preimage,
- `∃f` is subfunctor image,
- `∀f` is the right adjoint constructed pointwise as a supremum over
  admissible postconditions.

References:
- Jacobs (1999), Ch. 1 (reindexing with existential/universal adjoints).
- Mathlib: `CategoryTheory.Subfunctor.image_le_iff` (used for `∃f ⊣ f*`).
-/
noncomputable def presheafChangeOfBase (C : Type u) [Category C] :
    ChangeOfBase
      ({ Sub := (presheafPredicateFib (C := C)).Sub
         frame := (presheafPredicateFib (C := C)).frame } : SubobjectFibration (Cᵒᵖ ⥤ Type v)) := by
  classical
  refine
    { pullback := ?_
      directImage := ?_
      universalImage := ?_
      pullback_mono := ?_
      directImage_mono := ?_
      universalImage_mono := ?_
      direct_pullback_adj := ?_
      pullback_universal_adj := ?_ }
  · intro X Y f φ
    exact CategoryTheory.Subfunctor.preimage φ f
  · intro X Y f φ
    exact CategoryTheory.Subfunctor.image φ f
  · intro X Y f φ
    exact ⨆ θ : CategoryTheory.Subfunctor Y,
      if CategoryTheory.Subfunctor.preimage θ f ≤ φ then θ else ⊥
  · intro X Y f φ ψ hφ U x hx
    exact hφ U hx
  · intro X Y f φ ψ hφ U y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, hφ U hx, rfl⟩
  · intro X Y f φ ψ hφ
    refine iSup_le ?_
    intro θ
    by_cases hθ : CategoryTheory.Subfunctor.preimage θ f ≤ φ
    · have hθ' : CategoryTheory.Subfunctor.preimage θ f ≤ ψ := le_trans hθ hφ
      have hθsup : θ ≤
          (⨆ θ' : CategoryTheory.Subfunctor Y,
            if CategoryTheory.Subfunctor.preimage θ' f ≤ ψ then θ' else ⊥) :=
        le_iSup_of_le θ (by simp [hθ'])
      simpa [hθ] using hθsup
    · simp [hθ]
  · intro X Y f φ ψ
    simpa using
      (CategoryTheory.Subfunctor.image_le_iff
        (G := φ) (f := f) (G' := ψ))
  · intro X Y f ψ φ
    constructor
    · intro h
      have hψ : CategoryTheory.Subfunctor.preimage ψ f ≤ φ := h
      have hterm : ψ ≤
          (if CategoryTheory.Subfunctor.preimage ψ f ≤ φ then ψ else ⊥) := by
        simp [hψ]
      exact le_iSup_of_le ψ hterm
    · intro h
      have hpre :
          CategoryTheory.Subfunctor.preimage
            (⨆ θ : CategoryTheory.Subfunctor Y,
              if CategoryTheory.Subfunctor.preimage θ f ≤ φ then θ else ⊥) f ≤ φ := by
        calc
          CategoryTheory.Subfunctor.preimage
              (⨆ θ : CategoryTheory.Subfunctor Y,
                if CategoryTheory.Subfunctor.preimage θ f ≤ φ then θ else ⊥) f
              = ⨆ θ : CategoryTheory.Subfunctor Y,
                  CategoryTheory.Subfunctor.preimage
                    (if CategoryTheory.Subfunctor.preimage θ f ≤ φ then θ else ⊥) f := by
                  simpa using
                    (subfunctor_preimage_iSup
                      (f := f)
                      (G := fun θ : CategoryTheory.Subfunctor Y =>
                        if CategoryTheory.Subfunctor.preimage θ f ≤ φ then θ else ⊥))
          _ ≤ φ := by
            refine iSup_le ?_
            intro θ
            by_cases hθ : CategoryTheory.Subfunctor.preimage θ f ≤ φ
            · simp [hθ]
            · have hbot : CategoryTheory.Subfunctor.preimage
                (⊥ : CategoryTheory.Subfunctor Y) f ≤ φ := by
                intro U x hx
                exact False.elim hx
              simpa [hθ] using hbot
      have hmono :
          CategoryTheory.Subfunctor.preimage ψ f ≤
            CategoryTheory.Subfunctor.preimage
              (⨆ θ : CategoryTheory.Subfunctor Y,
                if CategoryTheory.Subfunctor.preimage θ f ≤ φ then θ else ⊥) f := by
        intro U x hx
        exact h U hx
      exact le_trans hmono hpre

/-- Beck–Chevalley in `Psh(C)` at the `Subfunctor` level for a pullback square.

This is the same base-change equation as `beckChevalleyPresheaf`, but expressed
on the concrete `ChangeOfBase` operations `f*` and `∃f`.

References:
- Awodey–Bauer lecture notes, §4.4.1 (Beck–Chevalley condition).
- Mac Lane–Moerdijk (1994), Ch. I.3 (base change in toposes). -/
theorem beckChevalleyPresheafSubfunctor (C : Type u) [Category.{w} C]
    {P A B D : Cᵒᵖ ⥤ Type v}
    (π₁ : P ⟶ A) (π₂ : P ⟶ B) (f : A ⟶ D) (g : B ⟶ D)
    (hpb : IsPullback π₁ π₂ f g)
    (φ : CategoryTheory.Subfunctor B) :
    CategoryTheory.Subfunctor.preimage (CategoryTheory.Subfunctor.image φ g) f =
      CategoryTheory.Subfunctor.image (CategoryTheory.Subfunctor.preimage φ π₂) π₁ := by
  ext U a
  constructor
  · intro ha
    change f.app U a ∈ (CategoryTheory.Subfunctor.image φ g).obj U at ha
    rcases ha with ⟨b, hbφ, hgb⟩
    have hpbU :
        IsPullback (π₁.app U) (π₂.app U) (f.app U) (g.app U) := by
      simpa using
        (hpb.map ((CategoryTheory.evaluation (Cᵒᵖ) (Type v)).obj U))
    have hfb : f.app U a = g.app U b := by simpa [eq_comm] using hgb
    rcases CategoryTheory.Limits.Types.exists_of_isPullback hpbU (x₂ := a) (x₃ := b) hfb with
      ⟨p, hp₁, hp₂⟩
    change a ∈
      (CategoryTheory.Subfunctor.image (CategoryTheory.Subfunctor.preimage φ π₂) π₁).obj U
    refine ⟨p, ?_, hp₁⟩
    change π₂.app U p ∈ φ.obj U
    simpa [hp₂] using hbφ
  · intro ha
    change a ∈
      (CategoryTheory.Subfunctor.image (CategoryTheory.Subfunctor.preimage φ π₂) π₁).obj U at ha
    rcases ha with ⟨p, hpPre, hp₁⟩
    change f.app U a ∈ (CategoryTheory.Subfunctor.image φ g).obj U
    refine ⟨π₂.app U p, hpPre, ?_⟩
    have hwNat : (π₁ ≫ f).app U = (π₂ ≫ g).app U := by
      exact congrArg (fun η => η.app U) hpb.w
    have hw : f.app U (π₁.app U p) = g.app U (π₂.app U p) := by
      exact congrFun hwNat p
    calc
      g.app U (π₂.app U p) = f.app U (π₁.app U p) := by simpa [eq_comm] using hw
      _ = f.app U a := by simp [hp₁]

/-- Beck–Chevalley square equation through the concrete presheaf
`ChangeOfBase` instance (pullback-scoped).

This bridges the concrete subobject theorem and the `ChangeOfBase` API layer.

Reference:
- Jacobs (1999), Ch. 1 (substitution/quantification compatibility). -/
theorem beckChevalleyPresheaf_changeOfBase (C : Type u) [Category.{w} C]
    {P A B D : Cᵒᵖ ⥤ Type v}
    (π₁ : P ⟶ A) (π₂ : P ⟶ B) (f : A ⟶ D) (g : B ⟶ D)
    (hpb : IsPullback π₁ π₂ f g)
    (φ : CategoryTheory.Subfunctor B) :
    (presheafChangeOfBase (C := C)).pullback f
      ((presheafChangeOfBase (C := C)).directImage g φ) =
    (presheafChangeOfBase (C := C)).directImage π₁
      ((presheafChangeOfBase (C := C)).pullback π₂ φ) := by
  simpa [presheafChangeOfBase] using
    (beckChevalleyPresheafSubfunctor (C := C) π₁ π₂ f g hpb φ)

/-! ## Beck-Chevalley Condition

For a pullback square in Psh(C):
```
    P ---π₂---> B
    |           |
   π₁          g
    ↓           ↓
    A ---f----> C
```

we have: f* ∘ ∃g = ∃π₁ ∘ π₂*

This is the key compatibility condition for quantification and substitution.
-/

/-- The Beck-Chevalley condition states that for pullback squares,
    substitution and quantification commute.

    This is a fundamental property of presheaf toposes that makes
    dependent type theory work correctly.

    References:
    - Jacobs (1999), Ch. 1 (fibrational Beck–Chevalley).
    - Awodey–Bauer lecture notes, §4.4.1. -/
def BeckChevalleyCondition {C : Type u} [Category.{v} C] (F : PredicateFib C)
    (cob : ChangeOfBase ⟨F.Sub, F.frame⟩) : Prop :=
  ∀ {P A B D : C} (π₁ : P ⟶ A) (π₂ : P ⟶ B) (f : A ⟶ D) (g : B ⟶ D),
    IsPullback π₁ π₂ f g →
    [Mono f] → [Mono π₂] →
    ∀ (φ : F.Sub B),
      cob.pullback f (cob.directImage g φ) = cob.directImage π₁ (cob.pullback π₂ φ)

/-- The concrete `presheafChangeOfBase` satisfies the generic
`BeckChevalleyCondition` (pullback-scoped form).

This is the concrete interface-level instantiation of
`beckChevalleyPresheafSubfunctor`. -/
theorem beckChevalleyCondition_presheafChangeOfBase
    (C : Type u) [Category.{w} C] :
    BeckChevalleyCondition (presheafPredicateFib (C := C))
      (presheafChangeOfBase (C := C)) := by
  intro P A B D π₁ π₂ f g hpb _ _ φ
  change CategoryTheory.Subfunctor B at φ
  simpa [presheafChangeOfBase] using
    (beckChevalleyPresheafSubfunctor (C := C) π₁ π₂ f g hpb φ)

/-- Concrete Beck–Chevalley square in `Psh(C)` using subobject pullback/map.

    This is the explicit pullback-square compatibility theorem (not a wrapper).
    It is the Mathlib formalization of the standard Beck–Chevalley base-change
    equation in presheaf toposes.

    Reference:
    - Mac Lane–Moerdijk (1994), Ch. I.3 (base change in toposes).
    - Mathlib theorem `Subobject.map_pullback`. -/
theorem beckChevalleyPresheaf (C : Type u) [Category.{w} C]
    {P A B D : Cᵒᵖ ⥤ Type v}
    (π₁ : P ⟶ A) (π₂ : P ⟶ B) (f : A ⟶ D) (g : B ⟶ D)
    (hpb : IsPullback π₁ π₂ f g) [Mono f] [Mono π₂]
    (φ : Subobject A) :
    (Subobject.map π₂).obj ((Subobject.pullback π₁).obj φ) =
      (Subobject.pullback g).obj ((Subobject.map f).obj φ) := by
  simpa [hpb.w] using
    (Subobject.map_pullback (f := π₁) (g := π₂) (h := f) (k := g)
      (comm := hpb.w) (t := hpb.isLimit) (p := φ))

/-! ## Connection to Our SubobjectFibration

We can convert a PredicateFib to our SubobjectFibration from Core.
-/

/-- Convert a predicate fibration to a subobject fibration.
    Now trivial since PredicateFib already has Frame fibers. -/
def PredicateFib.toSubobjectFibration {C : Type u} [Category.{v} C]
    (F : PredicateFib C) : SubobjectFibration C where
  Sub := F.Sub
  frame := F.frame

/-! ## Summary

This file establishes the predicate-fibration interface over presheaf categories:

1. **PredicateFib**: Abstract fibration with Frame fibers
2. **presheafPredicateFib**: Concrete Ω/subobject-backed instance via `Subfunctor`
3. **BeckChevalleyCondition**: f* ∘ ∃g = ∃π₁ ∘ π₂* proposition
4. **beckChevalleyPresheaf**: concrete base-change equation in `Psh(C)`

**Key Properties**:
- Fibers are complete lattices of predicates/subobjects
- Pullback preserves meets and top
- Beck-Chevalley ensures quantification commutes with substitution

**Next Steps**:
- Phase 4: Native Type Construction using Grothendieck on this fibration
- Connect to modal types ⟨Cj⟩_{xk::Ak} B
- MeTTa-IL interpretation
-/

end Mettapedia.GSLT.Topos
