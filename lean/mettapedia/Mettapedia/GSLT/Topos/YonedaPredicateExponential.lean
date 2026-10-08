import Mettapedia.GSLT.Topos.YonedaPredicateProducts
import Mettapedia.GSLT.Topos.PresheafPredicateYonedaRestriction

/-!
# Exponentials of the canonical Yoneda predicate theory

The base's selected exponential carries the future-sensitive function
predicate through Yoneda's earned canonical representing isomorphism.
Product and exponential comparison isomorphisms relate these objects to the
existing unrestricted predicate category. Its independent transposition
then supplies actual restricted curry/uncurry, both round trips, naturality
and a genuine adjunction. Their base readouts identify that transposition
with the original base adjunction.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.YonedaPredicate

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory

universe u
variable {C : Type u} [Category.{u} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]

set_option backward.isDefEq.respectTransparency false in
/-- Actual product comparison, including both predicate directions. -/
noncomputable def productComparison (a b : Total C) :
    (embedding C).obj (product a b) ≅
      prodTotal ((embedding C).obj a) ((embedding C).obj b) where
  hom := Topos.homOfEntailment (prodComparison (yoneda (C := C)) a.base b.base) (by
    change (predicate a).preimage (yoneda.map (fst a.base b.base)) ⊓
        (predicate b).preimage (yoneda.map (snd a.base b.base)) ≤
      ((predicate a).preimage (fst (yoneda.obj a.base) (yoneda.obj b.base)) ⊓
        (predicate b).preimage (snd (yoneda.obj a.base) (yoneda.obj b.base))).preimage _
    rw [preimage_inf, ← Subfunctor.preimage_comp, ← Subfunctor.preimage_comp,
      prodComparison_fst, prodComparison_snd])
  inv := Topos.homOfEntailment (inv (prodComparison (yoneda (C := C)) a.base b.base)) (by
    change (predicate a).preimage (fst (yoneda.obj a.base) (yoneda.obj b.base)) ⊓
        (predicate b).preimage (snd (yoneda.obj a.base) (yoneda.obj b.base)) ≤
      ((predicate a).preimage (yoneda.map (fst a.base b.base)) ⊓
        (predicate b).preimage (yoneda.map (snd a.base b.base))).preimage _
    rw [preimage_inf, ← Subfunctor.preimage_comp, ← Subfunctor.preimage_comp,
      inv_prodComparison_map_fst, inv_prodComparison_map_snd])
  hom_inv_id := Topos.hom_ext _ _ (IsIso.hom_inv_id
    (prodComparison (yoneda (C := C)) a.base b.base))
  inv_hom_id := Topos.hom_ext _ _ (IsIso.inv_hom_id
    (prodComparison (yoneda (C := C)) a.base b.base))

/-- The actual restricted exponential, over the selected base exponential. -/
noncomputable abbrev exponentialObject (a b : Total C) : Total C :=
  ofPredicate ((ihom a.base).obj b.base)
    (canonicalYonedaExpPredicate (predicate a) (predicate b))

set_option backward.isDefEq.respectTransparency false in
/-- The restricted exponential represents the full unrestricted function
predicate through the earned canonical exponential comparison. -/
noncomputable def exponentialComparison (a b : Total C) :
    (embedding C).obj (exponentialObject a b) ≅
      expTotal ((embedding C).obj a) ((embedding C).obj b) where
  hom := Topos.homOfEntailment (YonedaClosed.exponentialIso a.base b.base).hom le_rfl
  inv := Topos.homOfEntailment (YonedaClosed.exponentialIso a.base b.base).inv (by
    change expPredicate ((embedding C).obj a) ((embedding C).obj b) ≤
      ((expPredicate ((embedding C).obj a) ((embedding C).obj b)).preimage
        (YonedaClosed.exponentialIso a.base b.base).hom).preimage
          (YonedaClosed.exponentialIso a.base b.base).inv
    rw [← Subfunctor.preimage_comp, Iso.inv_hom_id]
    exact (Subfunctor.preimage_id _).symm.le)
  hom_inv_id := Topos.hom_ext _ _ (Iso.hom_inv_id _)
  inv_hom_id := Topos.hom_ext _ _ (Iso.inv_hom_id _)

/-- Transpose an admitted body through the independently earned total
transposition and the actual product/exponential comparisons. -/
noncomputable def curry {a b context : Total C} (body : product a context ⟶ b) :
    context ⟶ exponentialObject a b :=
  (fullyFaithful C).preimage
    (expCurry ((productComparison a context).inv ≫ (embedding C).map body) ≫
      (exponentialComparison a b).inv)

/-- Untranspose the full supplied function, retaining its predicate entailment. -/
noncomputable def uncurry {a b context : Total C}
    (function : context ⟶ exponentialObject a b) : product a context ⟶ b :=
  (fullyFaithful C).preimage
    ((productComparison a context).hom ≫
      expUncurry ((embedding C).map function ≫ (exponentialComparison a b).hom))

theorem curry_embedding {a b context : Total C} (body : product a context ⟶ b) :
    (embedding C).map (curry body) =
      expCurry ((productComparison a context).inv ≫ (embedding C).map body) ≫
        (exponentialComparison a b).inv :=
  (fullyFaithful C).map_preimage _

theorem uncurry_embedding {a b context : Total C}
    (function : context ⟶ exponentialObject a b) :
    (embedding C).map (uncurry function) =
      (productComparison a context).hom ≫
        expUncurry ((embedding C).map function ≫ (exponentialComparison a b).hom) :=
  (fullyFaithful C).map_preimage _

theorem uncurry_curry {a b context : Total C} (body : product a context ⟶ b) :
    uncurry (curry body) = body := by
  apply (embedding C).map_injective
  rw [uncurry_embedding, curry_embedding]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    expUncurry_expCurry, Iso.hom_inv_id_assoc]

theorem curry_uncurry {a b context : Total C}
    (function : context ⟶ exponentialObject a b) : curry (uncurry function) = function := by
  apply (embedding C).map_injective
  rw [curry_embedding, uncurry_embedding]
  simp only [Iso.inv_hom_id_assoc, expCurry_expUncurry,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Both genuine directions of the restricted exponential universal property. -/
noncomputable def exponentialHomEquiv (a b context : Total C) :
    (product a context ⟶ b) ≃ (context ⟶ exponentialObject a b) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

set_option backward.isDefEq.respectTransparency false in
/-- Restricted transposition is exactly the supplied base transposition. -/
theorem curry_base {a b context : Total C} (body : product a context ⟶ b) :
    (curry body).base = MonoidalClosed.curry body.base := by
  apply yoneda.map_injective
  have reading := congrArg Pseudofunctor.CoGrothendieck.Hom.base (curry_embedding body)
  change yoneda.map (curry body).base =
    MonoidalClosed.curry (inv (prodComparison (yoneda (C := C)) a.base context.base) ≫
      yoneda.map body.base) ≫ (YonedaClosed.exponentialIso a.base b.base).inv at reading
  rw [reading, ← YonedaClosed.map_curry, Category.assoc]
  change yoneda.map (MonoidalClosed.curry body.base) ≫
    ((YonedaClosed.exponentialIso a.base b.base).hom ≫
      (YonedaClosed.exponentialIso a.base b.base).inv) = _
  rw [Iso.hom_inv_id, Category.comp_id]

theorem uncurry_base {a b context : Total C}
    (function : context ⟶ exponentialObject a b) :
    (uncurry function).base = MonoidalClosed.uncurry function.base := by
  have reading := congrArg Pseudofunctor.CoGrothendieck.Hom.base (curry_uncurry function)
  rw [curry_base] at reading
  have full := congrArg MonoidalClosed.uncurry reading
  rw [MonoidalClosed.uncurry_curry] at full
  exact full

/-- Evaluation is a real restricted predicate morphism. -/
noncomputable def evaluation (a b : Total C) : product a (exponentialObject a b) ⟶ b :=
  uncurry (𝟙 (exponentialObject a b))

theorem evaluation_base (a b : Total C) :
    (evaluation a b).base = (ihom.ev a.base).app b.base := by
  rw [evaluation, uncurry_base]
  exact MonoidalClosed.uncurry_id_eq_ev a.base b.base

theorem curry_naturality {a b context other : Total C}
    (change : other ⟶ context) (body : product a context ⟶ b) :
    curry (productMap (𝟙 a) change ≫ body) = change ≫ curry body := by
  apply hom_ext
  rw [curry_base]
  change MonoidalClosed.curry
      (lift (fst a.base other.base ≫ 𝟙 a.base)
        (snd a.base other.base ≫ change.base) ≫ body.base) =
    change.base ≫ (curry body).base
  rw [curry_base, Category.comp_id]
  have productRead : lift (fst a.base other.base) (snd a.base other.base ≫ change.base) =
      a.base ◁ change.base := by ext <;> simp
  rw [productRead, MonoidalClosed.curry_natural_left]

/-- The covariant exponential action is earned from evaluation and transposition. -/
noncomputable def exponentialMap (a : Total C) {b c : Total C} (f : b ⟶ c) :
    exponentialObject a b ⟶ exponentialObject a c :=
  curry (evaluation a b ≫ f)

theorem exponentialMap_base (a : Total C) {b c : Total C} (f : b ⟶ c) :
    (exponentialMap a f).base = (ihom a.base).map f.base := by
  rw [exponentialMap, curry_base]
  change MonoidalClosed.curry ((evaluation a b).base ≫ f.base) = _
  rw [evaluation_base, MonoidalClosed.curry_natural_right]
  rw [← MonoidalClosed.uncurry_id_eq_ev, MonoidalClosed.curry_uncurry, Category.id_comp]

noncomputable def exponential (a : Total C) : Total C ⥤ Total C where
  obj := exponentialObject a
  map := exponentialMap a
  map_id b := hom_ext _ _ (by rw [exponentialMap_base]; exact (ihom a.base).map_id b.base)
  map_comp f g := hom_ext _ _ (by
    rw [exponentialMap_base]
    change (ihom a.base).map (f.base ≫ g.base) =
      (exponentialMap a f).base ≫ (exponentialMap a g).base
    rw [exponentialMap_base, exponentialMap_base, Functor.map_comp])

set_option backward.isDefEq.respectTransparency false in
/-- The actual tensor--exponential adjunction, with both naturality equations. -/
noncomputable def exponentialAdjunction (a : Total C) : tensorLeft a ⊣ exponential a :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun context b => exponentialHomEquiv a b context
      homEquiv_naturality_left_symm := by
        intro context other b change function
        apply hom_ext
        change (uncurry (change ≫ function)).base =
          ((tensorLeft a).map change ≫ uncurry function).base
        rw [uncurry_base]
        change MonoidalClosed.uncurry (change.base ≫ function.base) =
          ((tensorLeft a).map change).base ≫ (uncurry function).base
        rw [uncurry_base, tensorLeft_map]
        change MonoidalClosed.uncurry (change.base ≫ function.base) =
          lift (fst a.base context.base ≫ 𝟙 a.base)
            (snd a.base context.base ≫ change.base) ≫ MonoidalClosed.uncurry function.base
        rw [Category.comp_id]
        have productRead : lift (fst a.base context.base) (snd a.base context.base ≫ change.base) =
            a.base ◁ change.base := by ext <;> simp
        rw [productRead, MonoidalClosed.uncurry_natural_left]
      homEquiv_naturality_right := by
        intro context b c body f
        apply hom_ext
        change (curry (body ≫ f)).base = (curry body ≫ exponentialMap a f).base
        rw [curry_base]
        change MonoidalClosed.curry (body.base ≫ f.base) =
          (curry body).base ≫ (exponentialMap a f).base
        rw [curry_base, exponentialMap_base, MonoidalClosed.curry_natural_right] }

noncomputable instance closed : MonoidalClosed (Total C) where
  closed a := { rightAdj := exponential a, adj := exponentialAdjunction a }

theorem canonical_curry {a b context : Total C} (body : product a context ⟶ b) :
    MonoidalClosed.curry body = curry body := by
  change (exponentialAdjunction a).homEquiv context b body = curry body
  rw [exponentialAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

theorem canonical_uncurry {a b context : Total C}
    (function : context ⟶ exponentialObject a b) : MonoidalClosed.uncurry function = uncurry function := by
  change ((exponentialAdjunction a).homEquiv context b).symm function = uncurry function
  rw [exponentialAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The actual canonical evaluation projects to the chosen base evaluation. -/
theorem projection_evaluation (a b : Total C) :
    (projection C).map ((ihom.ev a).app b) = (ihom.ev a.base).app b.base := by
  change (evaluation a b).base = _
  exact evaluation_base a b

set_option backward.isDefEq.respectTransparency false in
/-- The actual canonical exponential comparison of the projection is identity. -/
theorem projection_expComparison (a b : Total C) :
    (expComparison (projection C) a).natTrans.app b = 𝟙 ((ihom a.base).obj b.base) := by
  apply MonoidalClosed.uncurry_injective
  rw [uncurry_expComparison]
  change inv (prodComparison (projection C) a (exponentialObject a b)) ≫
    (projection C).map ((ihom.ev a).app b) =
      MonoidalClosed.uncurry (𝟙 ((ihom a.base).obj b.base))
  have inverse : inv (prodComparison (projection C) a (exponentialObject a b)) =
      𝟙 (a.base ⊗ (ihom a.base).obj b.base) := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [projection_productComparison]
    exact Category.id_comp _
  rw [inverse, projection_evaluation]
  exact (Category.id_comp _).trans (MonoidalClosed.uncurry_id_eq_ev a.base b.base).symm

set_option backward.isDefEq.respectTransparency false in
/-- Closedness of the projection uses the earned actual canonical comparison. -/
noncomputable instance projectionClosed : MonoidalClosedFunctor (projection C) where
  comparison_iso a := by
    have (b : Total C) : IsIso ((expComparison (projection C) a).natTrans.app b) := by
      rw [projection_expComparison]
      exact inferInstanceAs (IsIso (𝟙 ((ihom a.base).obj b.base)))
    exact NatIso.isIso_of_isIso_app _

end Mettapedia.GSLT.Topos.YonedaPredicate
