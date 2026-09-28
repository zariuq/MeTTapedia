import Mettapedia.OSLF.Syntax.CartesianContextProducts
import Mathlib.CategoryTheory.ObjectProperty.Local
import Mathlib.CategoryTheory.MorphismProperty.IsSmall
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Binary-product preservation as a local-object condition

For a cartesian authored context category, the projections from a product
induce a map from the coproduct of the two covariant representables to the
representable product. A set-valued interpretation is local to this map
exactly when it preserves that chosen binary product.

This identifies the actual equations a later reflection must impose. It does
not itself construct the reflector or a relative free classifying category.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CartesianContextModels

open CategoryTheory CategoryTheory.Limits Opposite
open Mettapedia.OSLF.FormalFiniteLimits (CovariantPresheaf)

variable (C : Type) [SmallCategory C] [HasBinaryProducts C]

/-- The canonical map whose orthogonality expresses the product equation. -/
noncomputable def productLocalizingMap (X Y : C) :
    (coyoneda.obj (op X) ⨿ coyoneda.obj (op Y) :
      CovariantPresheaf C) ⟶ coyoneda.obj (op (X ⨯ Y)) :=
  coprod.desc (coyoneda.map (prod.fst : X ⨯ Y ⟶ X).op)
    (coyoneda.map (prod.snd : X ⨯ Y ⟶ Y).op)

/-- A map out of the two-representable coproduct selects one element at each
authored context. -/
noncomputable def coprodHomElements (F : CovariantPresheaf C) (X Y : C) :
    ((coyoneda.obj (op X) ⨿ coyoneda.obj (op Y) :
      CovariantPresheaf C) ⟶ F) ≃
      F.obj X × F.obj Y where
  toFun h :=
    (coyonedaEquiv (coprod.inl ≫ h),
      coyonedaEquiv (coprod.inr ≫ h))
  invFun p :=
    coprod.desc (coyonedaEquiv.symm p.1)
      (coyonedaEquiv.symm p.2)
  left_inv h := by
    apply coprod.hom_ext
    · simp only [coprod.inl_desc, Equiv.symm_apply_apply]
    · simp only [coprod.inr_desc, Equiv.symm_apply_apply]
  right_inv p := by
    apply Prod.ext
    · simp only [coprod.inl_desc, Equiv.apply_symm_apply]
    · simp only [coprod.inr_desc, Equiv.apply_symm_apply]

/-- Precomposition with the canonical map acts by the two projections. -/
theorem productLocalizingMap_components (F : CovariantPresheaf C)
    (X Y : C) (h : coyoneda.obj (op (X ⨯ Y)) ⟶ F) :
    coprodHomElements C F X Y (productLocalizingMap C X Y ≫ h) =
      (F.map prod.fst (coyonedaEquiv h),
        F.map prod.snd (coyonedaEquiv h)) := by
  apply Prod.ext
  · change coyonedaEquiv (coprod.inl ≫
        productLocalizingMap C X Y ≫ h) = _
    rw [← Category.assoc]
    dsimp only [productLocalizingMap]
    rw [coprod.inl_desc]
    exact (coyonedaEquiv_naturality h prod.fst).symm
  · change coyonedaEquiv (coprod.inr ≫
        productLocalizingMap C X Y ≫ h) = _
    rw [← Category.assoc]
    dsimp only [productLocalizingMap]
    rw [coprod.inr_desc]
    exact (coyonedaEquiv_naturality h prod.snd).symm

/-- Locality is precisely bijectivity of the set-level comparison. -/
theorem productLocalizingMap_local_iff_bijective
    (F : CovariantPresheaf C) (X Y : C) :
    (MorphismProperty.single (productLocalizingMap C X Y)).isLocal F ↔
      Function.Bijective (fun z : F.obj (X ⨯ Y) =>
        (F.map prod.fst z, F.map prod.snd z)) := by
  rw [MorphismProperty.isLocal_single_iff_bijective]
  let pre : (coyoneda.obj (op (X ⨯ Y)) ⟶ F) →
      ((coyoneda.obj (op X) ⨿ coyoneda.obj (op Y) :
        CovariantPresheaf C) ⟶ F) :=
    fun h => productLocalizingMap C X Y ≫ h
  let e₁ : F.obj (X ⨯ Y) ≃
      (coyoneda.obj (op (X ⨯ Y)) ⟶ F) := coyonedaEquiv.symm
  let e₂ := coprodHomElements C F X Y
  have hcomp :
      (fun z : F.obj (X ⨯ Y) =>
        (F.map prod.fst z, F.map prod.snd z)) =
        e₂ ∘ pre ∘ e₁ := by
    funext z
    simpa only [e₁, e₂, pre, Function.comp_apply,
      Equiv.apply_symm_apply] using
      (productLocalizingMap_components C F X Y (e₁ z)).symm
  constructor
  · intro hp
    rw [hcomp]
    exact e₂.bijective.comp (hp.comp e₁.bijective)
  · intro hc
    rw [hcomp] at hc
    have hc' : Function.Bijective (e₂ ∘ pre) :=
      (Function.Bijective.of_comp_iff (e₂ ∘ pre) e₁.bijective).mp hc
    exact (Function.Bijective.of_comp_iff' e₂.bijective pre).mp hc'

/-- Mathlib's categorical comparison computes the same pair of elements. -/
theorem productComparisonElements (F : CovariantPresheaf C)
    (X Y : C) (z : F.obj (X ⨯ Y)) :
    (Types.binaryProductIso (F.obj X) (F.obj Y)).hom
        ((prodComparison F X Y) z) =
      (F.map prod.fst z, F.map prod.snd z) := by
  apply Prod.ext
  · have e : prodComparison F X Y ≫
        (Types.binaryProductIso (F.obj X) (F.obj Y)).hom ≫
        TypeCat.ofHom Prod.fst = F.map prod.fst := by
      rw [Types.binaryProductIso_hom_comp_fst]
      exact prodComparison_fst F X Y
    exact ConcreteCategory.congr_hom e z
  · have e : prodComparison F X Y ≫
        (Types.binaryProductIso (F.obj X) (F.obj Y)).hom ≫
        TypeCat.ofHom Prod.snd = F.map prod.snd := by
      rw [Types.binaryProductIso_hom_comp_snd]
      exact prodComparison_snd F X Y
    exact ConcreteCategory.congr_hom e z

/-- Orthogonality to the canonical map is exactly preservation of this
authored binary product, not merely substitution stability. -/
theorem product_local_iff_preserves_pair
    (F : CovariantPresheaf C) (X Y : C) :
    (MorphismProperty.single (productLocalizingMap C X Y)).isLocal F ↔
      PreservesLimit (pair X Y) F := by
  rw [productLocalizingMap_local_iff_bijective]
  have hpair :
      (fun z : F.obj (X ⨯ Y) =>
        (F.map prod.fst z, F.map prod.snd z)) =
        (Types.binaryProductIso (F.obj X) (F.obj Y)).hom ∘
          prodComparison F X Y := by
    funext z
    exact (productComparisonElements C F X Y z).symm
  rw [hpair]
  constructor
  · intro hb
    have hcomparison : Function.Bijective (prodComparison F X Y) :=
      (Function.Bijective.of_comp_iff'
        ((isIso_iff_bijective
          (Types.binaryProductIso (F.obj X) (F.obj Y)).hom).mp inferInstance)
        (prodComparison F X Y)).mp hb
    have : IsIso (prodComparison F X Y) :=
      (isIso_iff_bijective _).mpr hcomparison
    exact PreservesLimitPair.of_iso_prod_comparison F X Y
  · intro h
    have : PreservesLimit (pair X Y) F := h
    exact ((isIso_iff_bijective
      (Types.binaryProductIso (F.obj X) (F.obj Y)).hom).mp inferInstance).comp
        ((isIso_iff_bijective (prodComparison F X Y)).mp inferInstance)

/-- Every product-preserving model satisfies the corresponding local law. -/
theorem product_model_local_at_pair (F : Models C) (X Y : C) :
    (MorphismProperty.single (productLocalizingMap C X Y)).isLocal F.1 := by
  rw [product_local_iff_preserves_pair]
  have : PreservesFiniteProducts F.1 := F.property
  infer_instance

/-- A constant two-element interpretation fails this product law at every
pair, independently of any terminal-context condition. -/
theorem constantBool_not_local_at_pair (X Y : C) :
    ¬ (MorphismProperty.single (productLocalizingMap C X Y)).isLocal
      ((Functor.const C).obj Bool) := by
  rw [productLocalizingMap_local_iff_bijective]
  intro hb
  obtain ⟨b, h⟩ := hb.2 (false, true)
  simp only [Functor.const_obj_map] at h
  exact Bool.false_ne_true (congrArg Prod.fst h |>.symm.trans (congrArg Prod.snd h))

variable [HasTerminal C]

/-- Orthogonality to this map says that the empty authored context has a
singleton set of interpretations. -/
noncomputable def terminalLocalizingMap :
    (⊥_ (CovariantPresheaf C)) ⟶ coyoneda.obj (op (⊤_ C)) :=
  initial.to _

omit [HasBinaryProducts C] in
theorem terminal_local_iff_unique (F : CovariantPresheaf C) :
    (MorphismProperty.single (terminalLocalizingMap C)).isLocal F ↔
      Nonempty (Unique (F.obj (⊤_ C))) := by
  rw [MorphismProperty.isLocal_single_iff_bijective]
  constructor
  · intro hb
    let h₀ : (⊥_ (CovariantPresheaf C)) ⟶ F := initial.to F
    obtain ⟨h, _⟩ := hb.surjective h₀
    have uniq (x y : F.obj (⊤_ C)) : x = y := by
      apply coyonedaEquiv.symm.injective
      apply hb.injective
      exact initial.hom_ext _ _
    exact ⟨{ default := coyonedaEquiv h, uniq := fun x => uniq x _ }⟩
  · rintro ⟨hu⟩
    let : Unique (F.obj (⊤_ C)) := hu
    constructor
    · intro f g _
      apply coyonedaEquiv.injective
      exact Subsingleton.elim _ _
    · intro k
      refine ⟨coyonedaEquiv.symm default, ?_⟩
      exact initial.hom_ext _ _

omit [HasBinaryProducts C] in
/-- The terminal local law is exactly preservation of the empty product. -/
theorem terminal_local_iff_preserves_terminal (F : CovariantPresheaf C) :
    (MorphismProperty.single (terminalLocalizingMap C)).isLocal F ↔
      PreservesLimit (Functor.empty.{0} C) F := by
  rw [terminal_local_iff_unique]
  constructor
  · rintro ⟨hu⟩
    have ht : IsTerminal (F.obj (⊤_ C)) :=
      (Types.isTerminalEquivUnique _).symm hu
    have : IsIso (terminalComparison F) :=
      isIso_of_isTerminal ht terminalIsTerminal _
    exact PreservesTerminal.of_iso_comparison F
  · intro h
    have : PreservesLimit (Functor.empty.{0} C) F := h
    exact ⟨Types.isTerminalEquivUnique _
      (isLimitOfHasTerminalOfPreservesLimit F)⟩

variable [HasFiniteProducts C]

/-- Finite-product-preserving interpretations are exactly those local to the
terminal generator and every binary-product generator. This is the explicit
orthogonality presentation used by a subsequent reflective construction. -/
theorem product_model_iff_local_generators (F : CovariantPresheaf C) :
    ProductModel C F ↔
      (MorphismProperty.single (terminalLocalizingMap C)).isLocal F ∧
        ∀ X Y : C,
          (MorphismProperty.single (productLocalizingMap C X Y)).isLocal F := by
  constructor
  · intro h
    have : PreservesFiniteProducts F := h
    constructor
    · exact (terminal_local_iff_preserves_terminal C F).mpr inferInstance
    · intro X Y
      exact (product_local_iff_preserves_pair C F X Y).mpr inferInstance
  · rintro ⟨hterminal, hpairs⟩
    have hterm : PreservesLimit (Functor.empty.{0} C) F :=
      (terminal_local_iff_preserves_terminal C F).mp hterminal
    have : PreservesLimitsOfShape (Discrete.{0} PEmpty) F :=
      preservesLimitsOfShape_pempty_of_preservesTerminal F
    have hp : ∀ {X Y : C}, IsIso (prodComparison F X Y) := by
      intro X Y
      have : PreservesLimit (pair X Y) F :=
        (product_local_iff_preserves_pair C F X Y).mp (hpairs X Y)
      infer_instance
    have : PreservesLimitsOfShape (Discrete WalkingPair) F :=
      preservesBinaryProducts_of_isIso_prodComparison F
    exact PreservesFiniteProducts.of_preserves_binary_and_terminal F

/-- A small, explicit family of maps presenting all finite-product laws. -/
noncomputable def cartesianLawAt :
    Option (C × C) → MorphismProperty (CovariantPresheaf C)
  | none => MorphismProperty.single (terminalLocalizingMap C)
  | some (X, Y) => MorphismProperty.single (productLocalizingMap C X Y)

noncomputable def cartesianLaws :
    MorphismProperty (CovariantPresheaf C) :=
  ⨆ index : Option (C × C), cartesianLawAt C index

/-- The authored cartesian model predicate is precisely the local-object
predicate of the displayed small family of maps. -/
theorem product_model_iff_cartesian_local (F : CovariantPresheaf C) :
    ProductModel C F ↔ (cartesianLaws C).isLocal F := by
  rw [cartesianLaws, MorphismProperty.isLocal_iSup]
  simp only [iInf_apply, iInf_Prop_eq]
  rw [product_model_iff_local_generators]
  constructor
  · rintro ⟨hterminal, hpairs⟩ index
    cases index with
    | none => exact hterminal
    | some pair => exact hpairs pair.1 pair.2
  · intro h
    exact ⟨h none, fun X Y => h (some (X, Y))⟩

theorem productModel_eq_cartesianLocal :
    ProductModel C = (cartesianLaws C).isLocal := by
  ext F
  exact product_model_iff_cartesian_local C F

/-- The generating morphisms form a set, as required by a later orthogonal
reflection construction. -/
instance cartesianLaws_isSmall :
    MorphismProperty.IsSmall.{0} (cartesianLaws C) := by
  dsimp [cartesianLaws]
  have hsmall (index : Option (C × C)) :
      MorphismProperty.IsSmall.{0} (cartesianLawAt C index) := by
    cases index with
    | none => dsimp [cartesianLawAt, MorphismProperty.single]; infer_instance
    | some pair =>
      rcases pair with ⟨X, Y⟩
      dsimp [cartesianLawAt, MorphismProperty.single]
      infer_instance
  have : ∀ index : Option (C × C),
      MorphismProperty.IsSmall.{0} (cartesianLawAt C index) := hsmall
  infer_instance

end Mettapedia.OSLF.CartesianContextModels
