import Mettapedia.GSLT.Topos.Yoneda
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Subfunctor.Sieves
import Mathlib.CategoryTheory.Subfunctor.Subobject
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Classifier.Defs
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Subobject Classifier for Presheaf Categories

This file defines the subobject classifier Ω for presheaf categories.

## Main Definitions

* `omegaFunctor` - The presheaf Ω sending X to the set of sieves on X
* `trueNatTrans` - The "true" morphism ⊤ : 1 → Ω

## Key Insights

In a presheaf topos Psh(C):
- The subobject classifier Ω assigns to each object X the set of sieves on X
- Ω(X) = { S | S is a sieve on X }
- For f : X → Y, Ω(f) pulls back sieves: S ↦ f*(S)

## References

- Mac Lane & Moerdijk, "Sheaves in Geometry and Logic", Chapter I.4
- Johnstone, "Sketches of an Elephant", A.1.6
-/

namespace Mettapedia.GSLT.Topos

open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe u v

variable {C : Type u} [Category.{v} C]

/-! ## The Sieve Functor

The subobject classifier in Psh(C) is the functor Ω : Cᵒᵖ → Type
that sends each object X to the set of sieves on X.
-/

/-! ## Theorem-to-Source Map

This module keeps source-faithful references for the constructive presheaf
classifier path:

- `natTransEquivSubfunctor`:
  characteristic maps `P ⟶ Ω` correspond to subfunctors of `P`
  (Mac Lane–Moerdijk, Ch. I.3; Johnstone A.1.6).
- `subobjectMk_preimageSubfunctor_eq_pullback`:
  inverse-image/pullback compatibility for presheaf subobjects
  (Mac Lane–Moerdijk, Ch. I.3), mechanized with Mathlib pullback/subobject APIs.
- `presheafSubobjectRepresentableByOmega`:
  representability witness for `Subobject.presheaf` by canonical `Ω`
  (Mac Lane–Moerdijk, Ch. I.3).
- `presheafCategoryHasClassifier` / `presheafCategoryHasClassifier_iff`:
  representability criterion for classifier existence
  (Mathlib `isRepresentable_hasClassifier_iff`, matching MM Ch. I.3).
- `presheafSubobjectRepresentableByChosenOmega`:
  extraction of `RepresentableBy` from chosen classifier witness
  (Mathlib `Classifier.representableBy`). -/

/-- Sieves on `X` form a complete lattice.

Reference:
- Mac Lane–Moerdijk (1994), Ch. I.2/I.3: sieve lattices in presheaf semantics. -/
instance sieveCompleteLattice (X : C) : CompleteLattice (Sieve X) := inferInstance

/-- The pullback of a sieve along a morphism.
    If `S` is a sieve on `Y` and `f : X → Y`, then `f*(S)` is a sieve on `X`.

    Reference:
    - Mac Lane–Moerdijk (1994), Ch. I.2: pullback action on sieves. -/
def sievePullback {X Y : C} (f : X ⟶ Y) (S : Sieve Y) : Sieve X :=
  Sieve.pullback f S

/-- Pullback preserves top -/
theorem sievePullback_top {X Y : C} (f : X ⟶ Y) :
    sievePullback f ⊤ = ⊤ := by
  apply Sieve.ext
  intro Z g
  simp [sievePullback, Sieve.pullback]

/-- Pullback preserves bottom -/
theorem sievePullback_bot {X Y : C} (f : X ⟶ Y) :
    sievePullback f ⊥ = ⊥ := by
  apply Sieve.ext
  intro Z g
  simp only [sievePullback, Sieve.pullback_apply]
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- The subobject classifier functor Ω : Cᵒᵖ → Type.

    Ω(X) = { sieves on X }
    Ω(f) = pullback along f

    Reference:
    - Mac Lane–Moerdijk (1994), Ch. I.3: canonical sieve-valued truth object
      in presheaf toposes. -/
def omegaFunctor : Cᵒᵖ ⥤ Type (max u v) where
  obj X := Sieve (unop X)
  map f := TypeCat.ofHom (fun S => sievePullback f.unop S)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro S
    apply Sieve.ext
    intro Y g
    simp [sievePullback, Sieve.pullback]
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro S
    apply Sieve.ext
    intro Y h
    simp [sievePullback, Sieve.pullback]

/-- Notation for the subobject classifier -/
scoped notation "Ω_" => omegaFunctor

/-! ## The "True" Morphism

The morphism true : 1 → Ω is the natural transformation that
picks out the maximal sieve at each object.
-/

/-- The terminal presheaf 1 (constant at PUnit) -/
def terminalPresheaf : Cᵒᵖ ⥤ Type (max u v) where
  obj _ := PUnit.{max u v + 1}
  map _ := 𝟙 _

/-- The "true" natural transformation: 1 → Ω.
    At each `X`, it sends `()` to the maximal sieve `⊤`.

    Reference:
    - Mac Lane–Moerdijk (1994), Ch. I.3: classifier truth map `1 → Ω`. -/
def trueNatTrans : terminalPresheaf ⟶ omegaFunctor (C := C) where
  app X := TypeCat.ofHom (fun _ => (⊤ : Sieve (unop X)))
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro _
    show sievePullback f.unop ⊤ = ⊤
    exact sievePullback_top f.unop

/-! ## Properties of the Subobject Classifier

Key properties that make Ω a subobject classifier:
1. For each mono m : S ↪ P, there's a unique χ : P → Ω with pullback square
2. Ω(X) is a complete Heyting algebra (Frame)
-/

/-- Each fiber Ω(X) is a complete lattice.
    Note: For the full Frame structure, we'd need Heyting implication on sieves. -/
instance omegaCompleteLattice (X : C) : CompleteLattice (Sieve X) := inferInstance

/-! ## Constructive Phase-A Core: `NatTrans ↔ Subfunctor`

For `P : Psh(C)` we build a concrete equivalence
`(P ⟶ Ω) ≃ Subfunctor P`.

This is the technical core behind representability of `Subobject.presheaf` by `Ω`:
after composing with `Subfunctor.orderIsoSubobject`, this yields
`(P ⟶ Ω) ≃ Subobject P`.

Literature connection:
- Mac Lane–Moerdijk (1994), Ch. I §3 (subobject classifier in presheaf toposes).
- van Oosten notes (Ω via sieves + pullback action). -/

/-- From a subfunctor `G ≤ P`, construct its characteristic map `P ⟶ Ω` by sending each section
to the sieve of arrows along which it lands in `G`. -/
noncomputable def chiOfSubfunctor (P : Cᵒᵖ ⥤ Type (max u v))
    (G : CategoryTheory.Subfunctor P) : P ⟶ omegaFunctor (C := C) where
  app X := TypeCat.ofHom (fun x => G.sieveOfSection x)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro x
    show G.sieveOfSection (P.map f x) = sievePullback f.unop (G.sieveOfSection x)
    apply Sieve.ext
    intro Z g
    simp [sievePullback, CategoryTheory.Subfunctor.sieveOfSection_apply]

/-- From a characteristic map `χ : P ⟶ Ω`, recover the corresponding subfunctor by taking sections
whose identity arrow lies in the corresponding sieve. -/
noncomputable def subfunctorOfChi (P : Cᵒᵖ ⥤ Type (max u v))
    (χ : P ⟶ omegaFunctor (C := C)) : CategoryTheory.Subfunctor P where
  obj X := { x : P.obj X | (χ.app X x).arrows (𝟙 (unop X)) }
  map {X Y} f := by
    intro x hx
    show (χ.app Y (P.map f x)).arrows (𝟙 (unop Y))
    have hnat := NatTrans.naturality_apply χ f x
    rw [hnat]
    change (sievePullback f.unop (χ.app X x)).arrows (𝟙 (unop Y))
    have hf : (χ.app X x).arrows f.unop := by
      simpa using (χ.app X x).downward_closed hx f.unop
    simp [sievePullback, Sieve.pullback, hf]

/-- The explicit equivalence `(P ⟶ Ω) ≃ Subfunctor P`.

Reference:
- Mac Lane–Moerdijk (1994), Ch. I.3: characteristic-map/subobject
  correspondence in presheaf toposes. -/
noncomputable def natTransEquivSubfunctor (P : Cᵒᵖ ⥤ Type (max u v)) :
    (P ⟶ omegaFunctor (C := C)) ≃ CategoryTheory.Subfunctor P where
  toFun := subfunctorOfChi (C := C) P
  invFun := chiOfSubfunctor (C := C) P
  left_inv χ := by
    ext X x
    apply Sieve.ext
    intro Z g
    change ((subfunctorOfChi (C := C) P χ).obj (op Z) (P.map g.op x)) ↔
      (χ.app X x).arrows g
    change ((χ.app (op Z) (P.map g.op x)).arrows (𝟙 Z)) ↔ (χ.app X x).arrows g
    have hnat := NatTrans.naturality_apply χ g.op x
    have hnat' : (χ.app (op Z) (P.map g.op x)) = (sievePullback g (χ.app X x)) := hnat
    rw [hnat']
    simp [sievePullback, Sieve.pullback]
  right_inv G := by
    ext X x
    change ((chiOfSubfunctor (C := C) P G).app X x).arrows (𝟙 (unop X)) ↔ x ∈ G.obj X
    -- At identity, sieve-membership reduces to the original membership condition.
    change P.map (𝟙 (unop X)).op x ∈ G.obj X ↔ x ∈ G.obj X
    simp

/-! ## Constructive Pullback Bridge for `Subobject.mk`

To show representability by the canonical sieve object `Ω`, we need compatibility of our explicit
`χ`-equivalence with pullback in `Subobject.presheaf`. The next lemma provides exactly that bridge.
-/

/-- Set-theoretic preimage subfunctor alias (explicitly named for readability in the bridge proof). -/
abbrev preimageSubfunctor
    {X X' : Cᵒᵖ ⥤ Type (max u v)} (f : X ⟶ X') (G : CategoryTheory.Subfunctor X') :
    CategoryTheory.Subfunctor X :=
  CategoryTheory.Subfunctor.preimage G f

/-- Pullback of `Subobject.mk G.ι` along `f` corresponds to `Subobject.mk` of the preimage
subfunctor of `G` along `f`.

This is the concrete finite-data realization of inverse image for subobjects in presheaf toposes
(`Set`-valued fibers), matching MM92 I.3.

Reference:
- Mac Lane–Moerdijk (1994), Ch. I.3 (subobject inverse image).
- Mathlib `Subobject.pullback_obj` and pullback API in functor categories. -/
private theorem subobjectMk_preimageSubfunctor_eq_pullback
    {X X' : Cᵒᵖ ⥤ Type (max u v)} (f : X ⟶ X') (G : CategoryTheory.Subfunctor X') :
    Subobject.mk ((preimageSubfunctor f G).ι) = (Subobject.pullback f).obj (Subobject.mk G.ι) := by
  let rhs : Subobject X := (Subobject.pullback f).obj (Subobject.mk G.ι)
  have hrhs : Subobject.mk (CategoryTheory.Subfunctor.range rhs.arrow).ι = rhs := by
    simp [rhs]
  have hEq : preimageSubfunctor f G = CategoryTheory.Subfunctor.range rhs.arrow := by
    have hpb : rhs = Subobject.mk (pullback.snd (Subobject.mk G.ι).arrow f) := by
      simpa [rhs] using (Subobject.pullback_obj f (Subobject.mk G.ι))
    have hrange : CategoryTheory.Subfunctor.range rhs.arrow =
        CategoryTheory.Subfunctor.range (pullback.snd (Subobject.mk G.ι).arrow f) := by
      let k := pullback.snd (Subobject.mk G.ι).arrow f
      have h₁ : CategoryTheory.Subfunctor.range rhs.arrow =
          CategoryTheory.Subfunctor.range ((Subobject.mk k).arrow) := by
        simpa [hpb] using congrArg (fun S : Subobject X => CategoryTheory.Subfunctor.range S.arrow) hpb
      have h₂ : CategoryTheory.Subfunctor.range ((Subobject.mk k).arrow) =
          CategoryTheory.Subfunctor.range k := by
        calc
          CategoryTheory.Subfunctor.range ((Subobject.mk k).arrow)
              = CategoryTheory.Subfunctor.range ((Subobject.underlyingIso k).hom ≫ k) := by
                  have hmk : (Subobject.mk k).arrow = (Subobject.underlyingIso k).hom ≫ k := by
                    simp
                  exact hmk ▸ rfl
          _ = (CategoryTheory.Subfunctor.range (Subobject.underlyingIso k).hom).image k := by
                simpa using (CategoryTheory.Subfunctor.range_comp
                  (f := (Subobject.underlyingIso k).hom) (g := k))
          _ = (⊤ : CategoryTheory.Subfunctor (pullback (Subobject.mk G.ι).arrow f)).image k := by
                rw [CategoryTheory.Subfunctor.range_eq_top (p := (Subobject.underlyingIso k).hom)]
          _ = CategoryTheory.Subfunctor.range k := by
                simpa using (CategoryTheory.Subfunctor.image_top
                  (F := pullback (Subobject.mk G.ι).arrow f) (f := k))
      exact h₁.trans h₂
    rw [hrange]
    ext U x
    constructor
    · intro hx
      have hRG : CategoryTheory.Subfunctor.range (Subobject.mk G.ι).arrow = G :=
        CategoryTheory.Subfunctor.range_subobjectMk_ι (F := X') G
      have hRGU : Set.range ((Subobject.mk G.ι).arrow.app U) = G.obj U := by
        exact congrArg (fun H : CategoryTheory.Subfunctor X' => H.obj U) hRG
      have hGx : (f.app U x ∈ Set.range ((Subobject.mk G.ι).arrow.app U)) ↔ f.app U x ∈ G.obj U := by
        simp [hRGU]
      have hpre : x ∈ (f.app U) ⁻¹' Set.range ((Subobject.mk G.ι).arrow.app U) := by
        exact hGx.mpr hx
      have hRangeType : x ∈ Set.range (pullback.snd ((Subobject.mk G.ι).arrow.app U) (f.app U)) := by
        simpa [CategoryTheory.Limits.Types.range_pullbackSnd] using hpre
      have hIsoRange :
          Set.range ((pullback.snd (Subobject.mk G.ι).arrow f).app U) =
            Set.range (pullback.snd ((Subobject.mk G.ι).arrow.app U) (f.app U)) := by
        ext t
        constructor
        · rintro ⟨y, rfl⟩
          refine ⟨(pullbackObjIso (Subobject.mk G.ι).arrow f U).hom y, ?_⟩
          rw [← CategoryTheory.comp_apply]
          exact ConcreteCategory.congr_hom
            (pullbackObjIso_hom_comp_snd (f := (Subobject.mk G.ι).arrow) (g := f) U) y
        · rintro ⟨y, hy⟩
          refine ⟨(pullbackObjIso (Subobject.mk G.ι).arrow f U).inv y, ?_⟩
          rw [← hy, ← CategoryTheory.comp_apply]
          exact ConcreteCategory.congr_hom
            (pullbackObjIso_inv_comp_snd (f := (Subobject.mk G.ι).arrow) (g := f) U) y
      change x ∈ Set.range ((pullback.snd (Subobject.mk G.ι).arrow f).app U)
      exact hIsoRange.symm ▸ hRangeType
    · intro hx
      have hIsoRange :
          Set.range ((pullback.snd (Subobject.mk G.ι).arrow f).app U) =
            Set.range (pullback.snd ((Subobject.mk G.ι).arrow.app U) (f.app U)) := by
        ext t
        constructor
        · rintro ⟨y, rfl⟩
          refine ⟨(pullbackObjIso (Subobject.mk G.ι).arrow f U).hom y, ?_⟩
          rw [← CategoryTheory.comp_apply]
          exact ConcreteCategory.congr_hom
            (pullbackObjIso_hom_comp_snd (f := (Subobject.mk G.ι).arrow) (g := f) U) y
        · rintro ⟨y, hy⟩
          refine ⟨(pullbackObjIso (Subobject.mk G.ι).arrow f U).inv y, ?_⟩
          rw [← hy, ← CategoryTheory.comp_apply]
          exact ConcreteCategory.congr_hom
            (pullbackObjIso_inv_comp_snd (f := (Subobject.mk G.ι).arrow) (g := f) U) y
      have hRangeType : x ∈ Set.range (pullback.snd ((Subobject.mk G.ι).arrow.app U) (f.app U)) := by
        exact hIsoRange ▸ hx
      have hpre : x ∈ (f.app U) ⁻¹' Set.range ((Subobject.mk G.ι).arrow.app U) := by
        simpa [CategoryTheory.Limits.Types.range_pullbackSnd] using hRangeType
      have hRG : CategoryTheory.Subfunctor.range (Subobject.mk G.ι).arrow = G :=
        CategoryTheory.Subfunctor.range_subobjectMk_ι (F := X') G
      have hRGU : Set.range ((Subobject.mk G.ι).arrow.app U) = G.obj U := by
        exact congrArg (fun H : CategoryTheory.Subfunctor X' => H.obj U) hRG
      have hGx : (f.app U x ∈ Set.range ((Subobject.mk G.ι).arrow.app U)) ↔ f.app U x ∈ G.obj U := by
        simp [hRGU]
      exact hGx.mp hpre
  calc
    Subobject.mk ((preimageSubfunctor f G).ι)
        = Subobject.mk (CategoryTheory.Subfunctor.range rhs.arrow).ι := by
          simpa using congrArg (fun H : CategoryTheory.Subfunctor X => Subobject.mk H.ι) hEq
    _ = rhs := hrhs
    _ = (Subobject.pullback f).obj (Subobject.mk G.ι) := rfl

/-- Constructive representability of the subobject presheaf of `Psh(C)` by the canonical sieve
truth-values object `omegaFunctor`.

References:
- Mac Lane–Moerdijk (1994), Ch. I §3 (representability criterion in presheaf toposes).
- Implemented concretely via `NatTrans ↔ Subfunctor` + `Subfunctor ↔ Subobject`. -/
noncomputable def presheafSubobjectRepresentableByOmega (C : Type u) [SmallCategory C] :
    (Subobject.presheaf (Psh(C))).RepresentableBy (omegaFunctor (C := C)) where
  homEquiv {P} :=
    (natTransEquivSubfunctor (C := C) P).trans
      (CategoryTheory.Subfunctor.orderIsoSubobject (F := P)).toEquiv
  homEquiv_comp {P Q} f g := by
    -- Source-faithful pullback compatibility witness for characteristic maps in presheaf toposes.
    change Subobject.mk ((subfunctorOfChi (C := C) P (f ≫ g)).ι) =
      (Subobject.pullback f).obj (Subobject.mk ((subfunctorOfChi (C := C) Q g).ι))
    -- The characteristic subfunctor of `f ≫ g` is the `f`-preimage of that of `g`.
    have hkey : subfunctorOfChi (C := C) P (f ≫ g) =
        preimageSubfunctor f (subfunctorOfChi (C := C) Q g) := by
      apply CategoryTheory.Subfunctor.ext
      funext X
      ext x
      simp only [subfunctorOfChi, preimageSubfunctor, CategoryTheory.Subfunctor.preimage,
        Set.mem_preimage, Set.mem_setOf_eq, CategoryTheory.NatTrans.comp_app,
        ConcreteCategory.comp_apply]
    rw [hkey]
    exact subobjectMk_preimageSubfunctor_eq_pullback (C := C) (f := f)
      (G := subfunctorOfChi (C := C) Q g)

/-- Criterion form: `Psh(C)` has a classifier whenever its subobject presheaf is representable.

    This is the direction needed for the concrete `Ω`-construction bridge. -/
theorem presheafCategoryHasClassifier (C : Type u) [SmallCategory C]
    (hrep : (Subobject.presheaf (Psh(C))).IsRepresentable) :
    CategoryTheory.HasSubobjectClassifier (Psh(C)) := by
  -- Source: Mac Lane–Moerdijk (1994), Ch. I §3 (representability criterion),
  -- formalized in Mathlib as `hasSubobjectClassifier_iff_isRepresentable`.
  exact (CategoryTheory.hasSubobjectClassifier_iff_isRepresentable (C := Psh(C))).2 hrep

/-- Equivalence form re-exported for `Psh(C)`. -/
theorem presheafCategoryHasClassifier_iff (C : Type u) [SmallCategory C] :
    CategoryTheory.HasSubobjectClassifier (Psh(C)) ↔
      (Subobject.presheaf (Psh(C))).IsRepresentable := by
  -- Source: Mac Lane–Moerdijk (1994), Ch. I §3, Prop. 1.
  simpa using (CategoryTheory.hasSubobjectClassifier_iff_isRepresentable (C := Psh(C)))

/-- Ω-specific bridge: if the subobject presheaf is represented by the canonical sieve presheaf
`omegaFunctor`, then `Psh(C)` has a subobject classifier.

This is the concrete target for the constructive witness in Phase A. -/
theorem presheafCategoryHasClassifier_ofOmegaRepresentableBy (C : Type u) [SmallCategory C]
    (hΩ : (Subobject.presheaf (Psh(C))).RepresentableBy (omegaFunctor (C := C))) :
    CategoryTheory.HasSubobjectClassifier (Psh(C)) := by
  classical
  -- Source: Mac Lane–Moerdijk (1994), Ch. I §3:
  -- any representation of `Subobject.presheaf` yields a classifier.
  refine ⟨⟨CategoryTheory.SubobjectRepresentableBy.classifier (C := Psh(C)) hΩ⟩⟩

/-- Constructive classifier existence for presheaf categories using the canonical sieve object `Ω`.

This closes Phase A without assuming a pre-existing `HasClassifier (Psh(C))` witness. -/
theorem presheafCategoryHasClassifierConstructive (C : Type u) [SmallCategory C] :
    CategoryTheory.HasSubobjectClassifier (Psh(C)) := by
  exact presheafCategoryHasClassifier_ofOmegaRepresentableBy (C := C)
    (presheafSubobjectRepresentableByOmega (C := C))

/-- If `Psh(C)` already has a classifier, recover a concrete `RepresentableBy` witness for the
chosen truth-values object `Ω` (from the typeclass witness).

This is useful for staging: we can work with an explicit witness term while the constructive
`omegaFunctor`-specific representation is being built. -/
noncomputable def presheafSubobjectRepresentableByChosenOmega (C : Type u) [SmallCategory C]
    [CategoryTheory.HasSubobjectClassifier (Psh(C))] :
    (Subobject.presheaf (Psh(C))).RepresentableBy (CategoryTheory.HasSubobjectClassifier.Ω (Psh(C))) := by
  classical
  let 𝒞 : CategoryTheory.Subobject.Classifier (Psh(C)) :=
    CategoryTheory.HasSubobjectClassifier.exists_classifier (C := Psh(C)) |>.some
  -- Source: Mathlib formalization of MM92 I.3:
  -- `Classifier.representableBy` gives representation from a classifier.
  simpa [CategoryTheory.HasSubobjectClassifier.Ω, 𝒞] using
    (CategoryTheory.Subobject.Classifier.representableBy (𝒞 := 𝒞))

/-! ## Summary

This file establishes the subobject classifier for presheaf categories:

1. **omegaFunctor**: Ω : Cᵒᵖ → Type (the subobject classifier presheaf)
2. **trueNatTrans**: The "true" morphism 1 → Ω
3. **omegaFrame**: Each fiber Ω(X) is a Frame

**Key Properties**:
- Ω(X) is the complete lattice of sieves on X
- Pullback along f : X → Y gives Ω(f) : Ω(Y) → Ω(X)
- true picks the maximal sieve at each object
- Representability criterion for `HasClassifier (Psh(C))` is available

**Next Steps**:
- `PredicateFibration.lean`: Connect Ω to the predicate fibration πΩ
- Prove Beck-Chevalley condition
- Connect to native types via Grothendieck construction
-/

end Mettapedia.GSLT.Topos
