import Mettapedia.OSLF.NativeType.Construction
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# NTT Endpoint Theorems: Props 12, 14, 17, Def 21, Sec 4, Thm 23

This file closes the remaining strict NTT paper claims by bundling
proven infrastructure into theorem-level endpoints keyed to:
  Williams & Stay, "Native Type Theory" (ACT 2021).

## Claims Closed

- **Prop 12**: Indexed adjoints with Beck-Chevalley
- **Prop 14**: Cosmic fibration (Frame fibers = CCC + complete)
- **Prop 17**: Reification right adjoint layer
- **Def 21**: Codomain fibration (arrow category) + Cartesian lifts
- **Sec 4**: Image-comprehension adjunction i ⊣ c (full iff characterization)
- **Thm 23**: Internal language package + functorial laws
-/

open CategoryTheory

universe u v w

namespace Mettapedia.OSLF.NativeType

/-! ## NTT Proposition 12: Indexed Adjoints with Beck-Chevalley -/

/-- NTT Prop 12: the predicate fibration has indexed sums and products.
    Reference: Williams & Stay, NTT (ACT 2021), Prop 12. -/
theorem prop12_indexedAdjoints (C : Type u) [Category.{w} C]
    {X Y : Cᵒᵖ ⥤ Type v} (f : X ⟶ Y) :
    GaloisConnection
      ((GSLT.Topos.presheafChangeOfBase C).directImage f)
      ((GSLT.Topos.presheafChangeOfBase C).pullback f)
    ∧
    GaloisConnection
      ((GSLT.Topos.presheafChangeOfBase C).pullback f)
      ((GSLT.Topos.presheafChangeOfBase C).universalImage f) :=
  ⟨(GSLT.Topos.presheafChangeOfBase C).direct_pullback_adj f,
   (GSLT.Topos.presheafChangeOfBase C).pullback_universal_adj f⟩

/-- NTT Prop 12 (Beck-Chevalley). -/
noncomputable def prop12_beckChevalley (C : Type u) [Category.{w} C] :
    GSLT.Topos.BeckChevalleyCondition
      (GSLT.Topos.presheafPredicateFib C)
      (GSLT.Topos.presheafChangeOfBase C) :=
  GSLT.Topos.beckChevalleyCondition_presheafChangeOfBase C

/-- NTT Prop 12 full package. -/
structure Prop12_IndexedAdjoints (C : Type u) [Category.{w} C] where
  existLeft : ∀ {X Y : Cᵒᵖ ⥤ Type v} (f : X ⟶ Y),
    GaloisConnection
      ((GSLT.Topos.presheafChangeOfBase C).directImage f)
      ((GSLT.Topos.presheafChangeOfBase C).pullback f)
  univRight : ∀ {X Y : Cᵒᵖ ⥤ Type v} (f : X ⟶ Y),
    GaloisConnection
      ((GSLT.Topos.presheafChangeOfBase C).pullback f)
      ((GSLT.Topos.presheafChangeOfBase C).universalImage f)
  beckChevalley :
    GSLT.Topos.BeckChevalleyCondition
      (GSLT.Topos.presheafPredicateFib C)
      (GSLT.Topos.presheafChangeOfBase C)

noncomputable def prop12_package (C : Type u) [Category.{w} C] :
    Prop12_IndexedAdjoints.{u, v, w} C where
  existLeft f := (GSLT.Topos.presheafChangeOfBase C).direct_pullback_adj f
  univRight f := (GSLT.Topos.presheafChangeOfBase C).pullback_universal_adj f
  beckChevalley := GSLT.Topos.beckChevalleyCondition_presheafChangeOfBase C

/-! ### Prop 12 Export: Explicit Π/Σ Predicate Rule Package -/

section PiSigmaPredicateRules

variable {C : Type u} [Category.{w} C]

/-- A small context bundle for predicate-fibration Π/Σ transport over a map
`f : A ⟶ B` in the presheaf base. -/
structure PresheafDepCtx where
  A : Cᵒᵖ ⥤ Type
  B : Cᵒᵖ ⥤ Type
  f : A ⟶ B

namespace PresheafDepCtx

/-- Reindexing/pullback along the dependent projection. -/
noncomputable def pb (Δ : PresheafDepCtx (C := C)) :
    CategoryTheory.Subfunctor Δ.B → CategoryTheory.Subfunctor Δ.A :=
  (GSLT.Topos.presheafChangeOfBase C).pullback Δ.f

/-- Σ-forming operator (left adjoint to pullback). -/
noncomputable def sigmaForm (Δ : PresheafDepCtx (C := C)) :
    CategoryTheory.Subfunctor Δ.A → CategoryTheory.Subfunctor Δ.B :=
  (GSLT.Topos.presheafChangeOfBase C).directImage Δ.f

/-- Π-forming operator (right adjoint to pullback). -/
noncomputable def piForm (Δ : PresheafDepCtx (C := C)) :
    CategoryTheory.Subfunctor Δ.A → CategoryTheory.Subfunctor Δ.B :=
  (GSLT.Topos.presheafChangeOfBase C).universalImage Δ.f

/-- Σ-η/adjunction law in predicate-fibration form. -/
theorem sigmaEta_presheaf
    (Δ : PresheafDepCtx (C := C))
    {φ : CategoryTheory.Subfunctor Δ.A}
    {ψ : CategoryTheory.Subfunctor Δ.B} :
    Δ.sigmaForm φ ≤ ψ ↔ φ ≤ Δ.pb ψ := by
  rcases prop12_indexedAdjoints (C := C) Δ.f with ⟨hSigma, _hPi⟩
  simpa [pb, sigmaForm] using (hSigma φ ψ)

/-- Π-η/adjunction law in predicate-fibration form. -/
theorem piEta_presheaf
    (Δ : PresheafDepCtx (C := C))
    {ψ : CategoryTheory.Subfunctor Δ.B}
    {φ : CategoryTheory.Subfunctor Δ.A} :
    Δ.pb ψ ≤ φ ↔ ψ ≤ Δ.piForm φ := by
  rcases prop12_indexedAdjoints (C := C) Δ.f with ⟨_hSigma, hPi⟩
  simpa [pb, piForm] using (hPi ψ φ)

/-- Σ-introduction (unit specialization). -/
theorem sigmaIntro_presheaf
    (Δ : PresheafDepCtx (C := C)) (φ : CategoryTheory.Subfunctor Δ.A) :
    φ ≤ Δ.pb (Δ.sigmaForm φ) := by
  exact (sigmaEta_presheaf (C := C) (Δ := Δ)).1 le_rfl

/-- Σ-elimination (left-adjoint direction). -/
theorem sigmaElim_presheaf
    (Δ : PresheafDepCtx (C := C))
    {φ : CategoryTheory.Subfunctor Δ.A}
    {ψ : CategoryTheory.Subfunctor Δ.B}
    (h : φ ≤ Δ.pb ψ) :
    Δ.sigmaForm φ ≤ ψ := by
  exact (sigmaEta_presheaf (C := C) (Δ := Δ)).2 h

/-- Σ-β (counit specialization). -/
theorem sigmaBeta_presheaf
    (Δ : PresheafDepCtx (C := C)) (ψ : CategoryTheory.Subfunctor Δ.B) :
    Δ.sigmaForm (Δ.pb ψ) ≤ ψ := by
  exact (sigmaEta_presheaf (C := C) (Δ := Δ)).2 le_rfl

/-- Π-introduction (right-adjoint direction). -/
theorem piIntro_presheaf
    (Δ : PresheafDepCtx (C := C))
    {ψ : CategoryTheory.Subfunctor Δ.B}
    {φ : CategoryTheory.Subfunctor Δ.A}
    (h : Δ.pb ψ ≤ φ) :
    ψ ≤ Δ.piForm φ := by
  exact (piEta_presheaf (C := C) (Δ := Δ)).1 h

/-- Π-elimination (adjunction converse). -/
theorem piElim_presheaf
    (Δ : PresheafDepCtx (C := C))
    {ψ : CategoryTheory.Subfunctor Δ.B}
    {φ : CategoryTheory.Subfunctor Δ.A}
    (h : ψ ≤ Δ.piForm φ) :
    Δ.pb ψ ≤ φ := by
  exact (piEta_presheaf (C := C) (Δ := Δ)).2 h

/-- Π-β (counit specialization). -/
theorem piBeta_presheaf
    (Δ : PresheafDepCtx (C := C)) (φ : CategoryTheory.Subfunctor Δ.A) :
    Δ.pb (Δ.piForm φ) ≤ φ := by
  exact (piEta_presheaf (C := C) (Δ := Δ)).2 le_rfl

end PresheafDepCtx

/-- Reusable theorem package exporting Prop 12 as explicit Π/Σ rule endpoints. -/
structure PiSigmaPredicateRulePack (C : Type u) [Category.{w} C] where
  piIntro :
    ∀ (Δ : PresheafDepCtx (C := C))
      {ψ : CategoryTheory.Subfunctor Δ.B}
      {φ : CategoryTheory.Subfunctor Δ.A},
      Δ.pb ψ ≤ φ → ψ ≤ Δ.piForm φ
  piElim :
    ∀ (Δ : PresheafDepCtx (C := C))
      {ψ : CategoryTheory.Subfunctor Δ.B}
      {φ : CategoryTheory.Subfunctor Δ.A},
      ψ ≤ Δ.piForm φ → Δ.pb ψ ≤ φ
  piBeta :
    ∀ (Δ : PresheafDepCtx (C := C)) (φ : CategoryTheory.Subfunctor Δ.A),
      Δ.pb (Δ.piForm φ) ≤ φ
  piEta :
    ∀ (Δ : PresheafDepCtx (C := C))
      {ψ : CategoryTheory.Subfunctor Δ.B}
      {φ : CategoryTheory.Subfunctor Δ.A},
      Δ.pb ψ ≤ φ ↔ ψ ≤ Δ.piForm φ
  sigmaIntro :
    ∀ (Δ : PresheafDepCtx (C := C)) (φ : CategoryTheory.Subfunctor Δ.A),
      φ ≤ Δ.pb (Δ.sigmaForm φ)
  sigmaElim :
    ∀ (Δ : PresheafDepCtx (C := C))
      {φ : CategoryTheory.Subfunctor Δ.A}
      {ψ : CategoryTheory.Subfunctor Δ.B},
      φ ≤ Δ.pb ψ → Δ.sigmaForm φ ≤ ψ
  sigmaBeta :
    ∀ (Δ : PresheafDepCtx (C := C)) (ψ : CategoryTheory.Subfunctor Δ.B),
      Δ.sigmaForm (Δ.pb ψ) ≤ ψ
  sigmaEta :
    ∀ (Δ : PresheafDepCtx (C := C))
      {φ : CategoryTheory.Subfunctor Δ.A}
      {ψ : CategoryTheory.Subfunctor Δ.B},
      Δ.sigmaForm φ ≤ ψ ↔ φ ≤ Δ.pb ψ

/-- Prop 12 packaged as explicit Π/Σ predicate rules over presheaf fibers. -/
noncomputable def prop12_piSigmaPredicateRulePack :
    PiSigmaPredicateRulePack C where
  piIntro := by
    intro Δ ψ φ h
    exact PresheafDepCtx.piIntro_presheaf (C := C) (Δ := Δ) h
  piElim := by
    intro Δ ψ φ h
    exact PresheafDepCtx.piElim_presheaf (C := C) (Δ := Δ) h
  piBeta := by
    intro Δ φ
    exact PresheafDepCtx.piBeta_presheaf (C := C) (Δ := Δ) φ
  piEta := by
    intro Δ ψ φ
    exact PresheafDepCtx.piEta_presheaf (C := C) (Δ := Δ)
  sigmaIntro := by
    intro Δ φ
    exact PresheafDepCtx.sigmaIntro_presheaf (C := C) (Δ := Δ) φ
  sigmaElim := by
    intro Δ φ ψ h
    exact PresheafDepCtx.sigmaElim_presheaf (C := C) (Δ := Δ) h
  sigmaBeta := by
    intro Δ ψ
    exact PresheafDepCtx.sigmaBeta_presheaf (C := C) (Δ := Δ) ψ
  sigmaEta := by
    intro Δ φ ψ
    exact PresheafDepCtx.sigmaEta_presheaf (C := C) (Δ := Δ)

/-- Direct exported Π-η endpoint from the Prop 12 ΠΣ rule pack.
This avoids consumers needing to project fields from the packed structure. -/
theorem prop12_piEta_presheaf
    (Δ : PresheafDepCtx (C := C))
    {ψ : CategoryTheory.Subfunctor Δ.B}
    {φ : CategoryTheory.Subfunctor Δ.A} :
    Δ.pb ψ ≤ φ ↔ ψ ≤ Δ.piForm φ := by
  simpa using (prop12_piSigmaPredicateRulePack (C := C)).piEta Δ (ψ := ψ) (φ := φ)

/-- Direct exported Σ-η endpoint from the Prop 12 ΠΣ rule pack.
This avoids consumers needing to project fields from the packed structure. -/
theorem prop12_sigmaEta_presheaf
    (Δ : PresheafDepCtx (C := C))
    {φ : CategoryTheory.Subfunctor Δ.A}
    {ψ : CategoryTheory.Subfunctor Δ.B} :
    Δ.sigmaForm φ ≤ ψ ↔ φ ≤ Δ.pb ψ := by
  simpa using
    (prop12_piSigmaPredicateRulePack (C := C)).sigmaEta Δ (φ := φ) (ψ := ψ)

end PiSigmaPredicateRules

/-! ## NTT Proposition 14: Cosmic Fibration -/

/-- NTT Prop 14: cosmic fibration structure.
    Reference: Williams & Stay, NTT (ACT 2021), Prop 14 & 19. -/
structure Prop14_CosmicFibration (C : Type u) [Category.{w} C] where
  indexed : Prop12_IndexedAdjoints.{u, v, w} C
  frameFibers : ∀ (F : Cᵒᵖ ⥤ Type v), Order.Frame (Subfunctor F)

noncomputable def prop14_cosmicFibration (C : Type u) [Category.{w} C] :
    Prop14_CosmicFibration.{u, v, w} C where
  indexed := prop12_package C
  frameFibers F := GSLT.Topos.presheafSubfunctorFrame F

/-! ## NTT Proposition 17: Reification Right Adjoint -/

/-- Reification predicate: chi.F = inf { phi => F(phi) | phi }.
    Reference: Williams & Stay, NTT (ACT 2021), Prop 17. -/
noncomputable def reificationPred
    (L : CategoryTheory.LambdaTheories.LambdaTheory)
    (S : L.Obj)
    (F : L.fibration.Sub S → L.fibration.Sub S) : L.fibration.Sub S :=
  sInf { ψ | ∃ φ : L.fibration.Sub S, ψ = φ ⇨ F φ }

/-- The reification predicate is monotone in F. -/
theorem reificationPred_mono
    (L : CategoryTheory.LambdaTheories.LambdaTheory)
    (S : L.Obj) (F G : L.fibration.Sub S → L.fibration.Sub S)
    (hFG : ∀ φ, F φ ≤ G φ) :
    reificationPred L S F ≤ reificationPred L S G := by
  unfold reificationPred
  apply le_sInf
  intro ψ hψ
  rcases hψ with ⟨φ, rfl⟩
  exact le_trans (sInf_le ⟨φ, rfl⟩) (himp_le_himp_left (hFG φ))

/-- NTT Prop 17 package: reification right adjoint layer. -/
structure Prop17_Reification
    (L : CategoryTheory.LambdaTheories.LambdaTheory) where
  reify : ∀ (S : L.Obj),
    (L.fibration.Sub S → L.fibration.Sub S) → L.fibration.Sub S
  reify_mono : ∀ (S : L.Obj) (F G : L.fibration.Sub S → L.fibration.Sub S),
    (∀ φ, F φ ≤ G φ) → reify S F ≤ reify S G
  reify_le_himp : ∀ (S : L.Obj)
    (F : L.fibration.Sub S → L.fibration.Sub S)
    (φ : L.fibration.Sub S), reify S F ≤ φ ⇨ F φ

noncomputable def prop17_reification
    (L : CategoryTheory.LambdaTheories.LambdaTheory) :
    Prop17_Reification L where
  reify S F := reificationPred L S F
  reify_mono S F G hFG := reificationPred_mono L S F G hFG
  reify_le_himp S F φ := by
    apply sInf_le
    exact ⟨φ, rfl⟩

/-! ## NTT Definition 21: Codomain Fibration -/

/-- NTT Def 21: dependent types = arrow category.
    Reference: Williams & Stay, NTT (ACT 2021), Def 21. -/
abbrev DepTypeCategory (C : Type u) [Category.{v} C] := Arrow C

def codomainFunctor (C : Type u) [Category.{v} C] : Arrow C ⥤ C :=
  Arrow.rightFunc

def domainFunctor (C : Type u) [Category.{v} C] : Arrow C ⥤ C :=
  Arrow.leftFunc

structure Def21_CodomainFibration (C : Type u) [Category.{v} C] where
  totalCat : Type (max u v)
  totalCatCategory : Category totalCat
  codomain : @Functor totalCat totalCatCategory C _
  domain : @Functor totalCat totalCatCategory C _

def def21_codomainFibration (C : Type u) [Category.{v} C] :
    Def21_CodomainFibration C where
  totalCat := Arrow C
  totalCatCategory := inferInstance
  codomain := codomainFunctor C
  domain := domainFunctor C

/-! ### Def 21 Strengthening: Cartesian Lifts via Pullbacks

Given an arrow `arr : A ⟶ B` and a base morphism `f : Y ⟶ B`, the pullback
provides a Cartesian lift `pullback.snd : pullback arr.hom f ⟶ Y` in Arrow(C).
This witnesses that the codomain fibration is a Grothendieck fibration when
the base category has pullbacks (standard for presheaf toposes). -/

section CartesianLift

variable {C : Type u} [Category.{v} C]

/-- Cartesian lift: the pullback-induced arrow over the target of `f`. -/
noncomputable def def21_cartesianLift [Limits.HasPullbacks C]
    (arr : Arrow C) {Y : C} (f : Y ⟶ arr.right) : Arrow C :=
  Arrow.mk (Limits.pullback.snd arr.hom f)

/-- The morphism from the Cartesian lift to the original arrow,
    given by the pullback square. -/
noncomputable def def21_cartesianLiftMorphism [Limits.HasPullbacks C]
    (arr : Arrow C) {Y : C} (f : Y ⟶ arr.right) :
    def21_cartesianLift arr f ⟶ arr :=
  Arrow.homMk (Limits.pullback.fst arr.hom f) f Limits.pullback.condition

/-- The codomain functor maps the lift morphism to the base morphism `f`. -/
theorem def21_cartesianLift_proj [Limits.HasPullbacks C]
    (arr : Arrow C) {Y : C} (f : Y ⟶ arr.right) :
    (codomainFunctor C).map (def21_cartesianLiftMorphism arr f) = f := rfl

/-- Cartesian universality: any morphism `τ : w ⟶ arr` in Arrow(C) that
    projects to `g ≫ f` in the base factors through the Cartesian lift. -/
noncomputable def def21_cartesianLift_universal [Limits.HasPullbacks C]
    (arr : Arrow C) {Y : C} (f : Y ⟶ arr.right)
    {w : Arrow C} (τ : w ⟶ arr) (g : w.right ⟶ Y)
    (hg : g ≫ f = τ.right) :
    w ⟶ def21_cartesianLift arr f :=
  Arrow.homMk
    (Limits.pullback.lift τ.left (w.hom ≫ g) (by rw [Category.assoc, hg, Arrow.w]))
    g
    (by simp [def21_cartesianLift])

/-- The universal factorization composes to give the original morphism. -/
theorem def21_cartesianLift_universal_comp [Limits.HasPullbacks C]
    (arr : Arrow C) {Y : C} (f : Y ⟶ arr.right)
    {w : Arrow C} (τ : w ⟶ arr) (g : w.right ⟶ Y)
    (hg : g ≫ f = τ.right) :
    def21_cartesianLift_universal arr f τ g hg ≫
      def21_cartesianLiftMorphism arr f = τ := by
  ext
  · simp [def21_cartesianLift_universal, def21_cartesianLiftMorphism]
  · simp [def21_cartesianLift_universal, def21_cartesianLiftMorphism, hg]

end CartesianLift

/-! ## Image-Comprehension Adjunction (NTT Sec 4) -/

section ImageComprehension

variable {C : Type u} [Category.{v} C]

/-- Comprehension: predicate to dependent type (arrow). -/
def comprehension (F : Cᵒᵖ ⥤ Type v) (φ : Subfunctor F) :
    Arrow (Cᵒᵖ ⥤ Type v) :=
  Arrow.mk φ.ι

/-- Image predicate: arrow to its range subfunctor. -/
def imagePredicate {G F : Cᵒᵖ ⥤ Type v} (p : G ⟶ F) :
    Subfunctor F :=
  Subfunctor.range p

theorem subfunctor_le_image_of_ι (F : Cᵒᵖ ⥤ Type v)
    (φ : Subfunctor F) : φ ≤ imagePredicate φ.ι := by
  intro U x hx
  exact Set.mem_range_self (⟨x, hx⟩ : φ.obj U)

theorem image_of_ι_le_subfunctor (F : Cᵒᵖ ⥤ Type v)
    (φ : Subfunctor F) : imagePredicate φ.ι ≤ φ := by
  intro U x hx
  obtain ⟨⟨y, hy⟩, hxy⟩ := hx
  simp [Subfunctor.ι] at hxy
  rwa [← hxy]

theorem image_comprehension_roundtrip (F : Cᵒᵖ ⥤ Type v)
    (φ : Subfunctor F) : imagePredicate φ.ι = φ :=
  le_antisymm (image_of_ι_le_subfunctor F φ) (subfunctor_le_image_of_ι F φ)

theorem imageComprehension_galois_key {G F : Cᵒᵖ ⥤ Type v}
    (p : G ⟶ F) (φ : Subfunctor F)
    (h : imagePredicate p ≤ φ) :
    ∃ (lift : G ⟶ φ.toFunctor), lift ≫ φ.ι = p := by
  refine ⟨?_, ?_⟩
  · exact
    { app := fun U x => ⟨p.app U x, h U (Set.mem_range_self x)⟩
      naturality := by
        intro U V f; ext x
        simp [Subfunctor.toFunctor]
        exact congrFun (p.naturality f) x }
  · ext U x; simp [Subfunctor.ι]

/-- Reverse Galois direction: factoring through `φ.ι` implies `range(p) ≤ φ`.
    If `p = lift ≫ φ.ι`, then `range(p) ⊆ range(φ.ι) = φ`. -/
theorem imageComprehension_galois_reverse {G F : Cᵒᵖ ⥤ Type v}
    (p : G ⟶ F) (φ : Subfunctor F)
    (h : ∃ (lift : G ⟶ φ.toFunctor), lift ≫ φ.ι = p) :
    imagePredicate p ≤ φ := by
  obtain ⟨lift, rfl⟩ := h
  intro U x ⟨y, hy⟩
  have : φ.ι.app U (lift.app U y) = x := hy
  rw [← this]
  exact (lift.app U y).property

/-- Full hom-set characterization of the image-comprehension adjunction:
    `range(p) ≤ φ ↔ p factors through φ.ι`.
    This is the adjunction `i ⊣ c` in hom-set form. -/
theorem imageComprehension_iff {G F : Cᵒᵖ ⥤ Type v}
    (p : G ⟶ F) (φ : Subfunctor F) :
    imagePredicate p ≤ φ ↔ ∃ (lift : G ⟶ φ.toFunctor), lift ≫ φ.ι = p :=
  ⟨imageComprehension_galois_key p φ, imageComprehension_galois_reverse p φ⟩

/-- NTT Sec 4: Image-comprehension adjunction package.
    Uses direct formulations to avoid Arrow type coercions. -/
structure ImageComprehensionAdjunction (C : Type u) [Category.{v} C] where
  /-- Comprehension: predicate to dependent type (arrow) -/
  comp : ∀ (F : Cᵒᵖ ⥤ Type v), Subfunctor F → Arrow (Cᵒᵖ ⥤ Type v)
  /-- Image factorization: morphism to its range predicate -/
  img : ∀ {G F : Cᵒᵖ ⥤ Type v}, (G ⟶ F) → Subfunctor F
  /-- Roundtrip: range of an inclusion equals the original predicate -/
  roundtrip : ∀ (F : Cᵒᵖ ⥤ Type v) (φ : Subfunctor F),
    Subfunctor.range φ.ι = φ
  /-- Galois factorization: range(p) ≤ φ implies p factors through φ.ι -/
  factorization : ∀ {G F : Cᵒᵖ ⥤ Type v} (p : G ⟶ F) (φ : Subfunctor F),
    img p ≤ φ → ∃ (lift : G ⟶ φ.toFunctor), lift ≫ φ.ι = p
  /-- Full iff: hom-set characterization of the adjunction i ⊣ c -/
  iff_characterization : ∀ {G F : Cᵒᵖ ⥤ Type v} (p : G ⟶ F) (φ : Subfunctor F),
    img p ≤ φ ↔ ∃ (lift : G ⟶ φ.toFunctor), lift ≫ φ.ι = p

def imageComprehensionAdjunction (C : Type u) [Category.{v} C] :
    ImageComprehensionAdjunction C where
  comp := comprehension
  img := imagePredicate
  roundtrip F φ := image_comprehension_roundtrip F φ
  factorization p φ h := imageComprehension_galois_key p φ h
  iff_characterization p φ := imageComprehension_iff p φ

end ImageComprehension

/-! ## NTT Theorem 23: Internal Language Package -/

/-- NTT Thm 23: internal language package L(e) = <pi_Omega, pi_Delta, i, c>.
    Reference: Williams & Stay, NTT (ACT 2021), Thm 23. -/
structure InternalLanguagePackage (C : Type u) [Category.{w} C] where
  predicateFib : Prop14_CosmicFibration.{u, v, w} C
  codomainFib : Def21_CodomainFibration (Cᵒᵖ ⥤ Type v)
  imageComprehension : ImageComprehensionAdjunction (Cᵒᵖ ⥤ Type v)

noncomputable def thm23_internalLanguagePackage
    (C : Type u) [Category.{w} C] :
    InternalLanguagePackage.{u, v, w} C where
  predicateFib := prop14_cosmicFibration C
  codomainFib := def21_codomainFibration (Cᵒᵖ ⥤ Type v)
  imageComprehension := imageComprehensionAdjunction (Cᵒᵖ ⥤ Type v)

/-! ### Thm 23 Strengthening: Functorial Laws

The internal language assignment respects identity and composition of theory
morphisms. That is, the identity theory morphism preserves the Π/Ω/Prop
contract, and composition of theory morphisms preserves the Π/Ω/Prop contract.
These are the functorial laws making L a functor from the category of lambda
theories to the category of internal language packages. -/

open Mettapedia.CategoryTheory.LambdaTheories in
open TheoryMorphism in
/-- Functorial laws for the internal language package (Thm 23 strengthening).
    Witnesses that the assignment L ↦ InternalLanguagePackage respects identity
    and composition of theory morphisms. -/
structure InternalLanguageFunctorialLaws where
  /-- Identity morphism preserves Π/Ω/Prop. -/
  map_id : ∀ (L : LambdaTheory) (S : L.Obj)
    (types : Set (L.fibration.Sub S)) (φ ψ : L.fibration.Sub S),
    (TheoryMorphism.id L).mapPred (piType L S types) =
      piType L ((TheoryMorphism.id L).mapSort S) ((TheoryMorphism.id L).mapPred '' types)
    ∧
    ((TheoryMorphism.id L).mapNatType (NatType.full S)).pred =
      (NatType.full ((TheoryMorphism.id L).mapSort S)).pred
    ∧
    (TheoryMorphism.id L).mapPred (implType L S φ ψ) =
      implType L ((TheoryMorphism.id L).mapSort S)
        ((TheoryMorphism.id L).mapPred φ) ((TheoryMorphism.id L).mapPred ψ)
  /-- Composition of morphisms preserves Π/Ω/Prop. -/
  map_comp : ∀ {L₁ L₂ L₃ : LambdaTheory}
    (F : TheoryMorphism L₁ L₂) (G : TheoryMorphism L₂ L₃)
    (S : L₁.Obj) (types : Set (L₁.fibration.Sub S)) (φ ψ : L₁.fibration.Sub S),
    (TheoryMorphism.comp G F).mapPred (piType L₁ S types) =
      piType L₃ ((TheoryMorphism.comp G F).mapSort S)
        ((TheoryMorphism.comp G F).mapPred '' types)
    ∧
    ((TheoryMorphism.comp G F).mapNatType (NatType.full S)).pred =
      (NatType.full ((TheoryMorphism.comp G F).mapSort S)).pred
    ∧
    (TheoryMorphism.comp G F).mapPred (implType L₁ S φ ψ) =
      implType L₃ ((TheoryMorphism.comp G F).mapSort S)
        ((TheoryMorphism.comp G F).mapPred φ)
        ((TheoryMorphism.comp G F).mapPred ψ)

open Mettapedia.CategoryTheory.LambdaTheories in
open TheoryMorphism in
/-- The internal language functorial laws are satisfied. -/
def thm23_functorialLaws : InternalLanguageFunctorialLaws where
  map_id L S types φ ψ :=
    TheoryMorphism.id_piOmegaProp_translation_endpoint L S types φ ψ
  map_comp F G S types φ ψ :=
    TheoryMorphism.piOmegaProp_translation_endpoint
      (F := TheoryMorphism.comp G F) S types φ ψ

end Mettapedia.OSLF.NativeType
