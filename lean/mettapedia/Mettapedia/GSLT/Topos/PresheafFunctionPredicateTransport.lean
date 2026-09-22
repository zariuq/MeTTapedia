import Mettapedia.GSLT.Topos.PresheafPredicateReification

/-!
# Transport of function predicates along predicate-respecting maps

A function predicate built over one pair of typed objects transports to
another pair along total morphisms: contravariantly in the source,
covariantly in the target.  If a function carries `source` into `target`,
then composing it with a map into the source and a map out of the target
carries the new source into the new target, and the transported function
still satisfies the transported predicate.

The transport map is assembled from machinery already established rather
than constructed by hand:

  `expMap p q = expCurry ( prodTotalMap p id ≫ expEvalHom ≫ q )`

Every component is already a total morphism, so the construction carries no
new entailment obligation at all — the predicate side is discharged by the
components.  Functoriality is then `expMap_id` and `expMap_comp`.

## The transport boundary

This is transport along **maps of presheaves over a fixed base**.  That is
exactly the setting in which reindexing preserves Heyting implication
(`preimage_himp`), which is what the exponential predicate is built from.

Transport along a **change of base category** is a different question and the
general form of it is false: restriction along a base functor need not
preserve Heyting implication even when that functor preserves products, the
terminal object and exponentials.  That is proved at
`Mettapedia/OSLF/PresheafNativeType/TheoryTranslationCounterexample.lean`
(`actual_precomposition_does_not_preserve_implication`), which stands as the
regression control for any attempt to widen the statements below to base
change.  Nothing here should be read as licensing that widening.

## Supporting laws established on the way

* `expEvalHom_base` — evaluation's base map is the base category's evaluation;
* `expUncurry_eq` — uncurrying is pairing followed by evaluation;
* `expUncurry_naturality` — uncurrying is natural in the context;
* `prodTotalMap_id`, `prodTotalMap_comp` — the product is a functor.

## References

- Williams & Stay, "Native Type Theory" (ACT 2021), §3 and §5.
- Jacobs, "Categorical Logic and Type Theory" (1999), Ch. 1.
-/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

universe u

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos

variable {C : Type u} [Category.{u} C]

theorem prodTotalMap_id (a c : PresheafPredicateTotal C) :
    prodTotalMap (𝟙 a) (𝟙 c) = 𝟙 (prodTotal a c) :=
  hom_ext _ _ (by
    show lift (fst a.base c.base ≫ 𝟙 a.base)
        (snd a.base c.base ≫ 𝟙 c.base) = 𝟙 (a.base ⊗ c.base)
    rw [Category.comp_id, Category.comp_id]
    exact lift_fst_snd)

/-- Transport of the exponential along total morphisms: contravariant in the
source, covariant in the target. -/
noncomputable def expMap {a a' b b' : PresheafPredicateTotal C}
    (p : a' ⟶ a) (q : b ⟶ b') : expTotal a b ⟶ expTotal a' b' :=
  expCurry (prodTotalMap p (𝟙 (expTotal a b)) ≫ expEvalHom a b ≫ q)

/-- Transport at the identity pair is the identity. -/
theorem expMap_id (a b : PresheafPredicateTotal C) :
    expMap (𝟙 a) (𝟙 b) = 𝟙 (expTotal a b) := by
  rw [expMap, prodTotalMap_id, Category.id_comp, Category.comp_id]
  show expCurry (expUncurry (𝟙 (expTotal a b))) = 𝟙 (expTotal a b)
  exact expCurry_expUncurry (𝟙 (expTotal a b))

/-- The base of a product map with an identity first component is a
whiskering. -/
theorem prodTotalMap_id_base {a c c' : PresheafPredicateTotal C} (g : c ⟶ c') :
    (prodTotalMap (𝟙 a) g).base = a.base ◁ g.base := by
  show lift (fst a.base c.base ≫ 𝟙 a.base)
      (snd a.base c.base ≫ g.base) = a.base ◁ g.base
  rw [Category.comp_id]
  ext <;> simp

/-- Evaluation's base map is the base's evaluation. -/
theorem expEvalHom_base (a b : PresheafPredicateTotal C) :
    (expEvalHom a b).base = expEval a b := by
  show MonoidalClosed.uncurry (𝟙 (expBase a b)) = expEval a b
  exact MonoidalClosed.uncurry_id_eq_ev _ _

/-- Uncurrying is pairing followed by evaluation. -/
theorem expUncurry_eq {a b c : PresheafPredicateTotal C}
    (g : c ⟶ expTotal a b) :
    expUncurry g = prodTotalMap (𝟙 a) g ≫ expEvalHom a b :=
  hom_ext _ _ (by
    show MonoidalClosed.uncurry g.base =
      (prodTotalMap (𝟙 a) g).base ≫ (expEvalHom a b).base
    rw [prodTotalMap_id_base, expEvalHom_base]
    exact MonoidalClosed.uncurry_eq g.base)

/-- Uncurrying is natural in the context argument. -/
theorem expUncurry_naturality {a b c c' : PresheafPredicateTotal C}
    (h : c' ⟶ c) (g : c ⟶ expTotal a b) :
    expUncurry (h ≫ g) = prodTotalMap (𝟙 a) h ≫ expUncurry g :=
  hom_ext _ _ (by
    show MonoidalClosed.uncurry (h.base ≫ g.base) =
      (prodTotalMap (𝟙 a) h).base ≫ MonoidalClosed.uncurry g.base
    rw [prodTotalMap_id_base, MonoidalClosed.uncurry_natural_left])


theorem prodTotalMap_comp {a a' a'' c c' c'' : PresheafPredicateTotal C}
    (u : a ⟶ a') (v : c ⟶ c') (u' : a' ⟶ a'') (v' : c' ⟶ c'') :
    prodTotalMap u v ≫ prodTotalMap u' v' =
      prodTotalMap (u ≫ u') (v ≫ v') :=
  hom_ext _ _ (by
    show lift (fst a.base c.base ≫ u.base) (snd a.base c.base ≫ v.base) ≫
        lift (fst a'.base c'.base ≫ u'.base) (snd a'.base c'.base ≫ v'.base)
      = lift (fst a.base c.base ≫ (u.base ≫ u'.base))
          (snd a.base c.base ≫ (v.base ≫ v'.base))
    ext <;> simp)

theorem expUncurry_injective (a b c : PresheafPredicateTotal C) :
    Function.Injective (expUncurry (a := a) (b := b) (c := c)) := by
  intro X Y equal
  rw [← expCurry_expUncurry X, ← expCurry_expUncurry Y, equal]

/-- Transport is functorial in both arguments. -/
theorem expMap_comp {a a' a'' b b' b'' : PresheafPredicateTotal C}
    (p : a' ⟶ a) (q : b ⟶ b') (p' : a'' ⟶ a') (q' : b' ⟶ b'') :
    expMap p q ≫ expMap p' q' = expMap (p' ≫ p) (q ≫ q') := by
  refine expUncurry_injective a'' b'' (expTotal a b) ?_
  have inner : expUncurry (expMap p' q') =
      prodTotalMap p' (𝟙 (expTotal a' b')) ≫ expEvalHom a' b' ≫ q' :=
    expUncurry_expCurry _
  have outer : expUncurry (expMap p q) =
      prodTotalMap p (𝟙 (expTotal a b)) ≫ expEvalHom a b ≫ q :=
    expUncurry_expCurry _
  calc expUncurry (expMap p q ≫ expMap p' q')
      = prodTotalMap (𝟙 a'') (expMap p q) ≫ expUncurry (expMap p' q') :=
        expUncurry_naturality _ _
    _ = prodTotalMap (𝟙 a'') (expMap p q) ≫
          (prodTotalMap p' (𝟙 (expTotal a' b')) ≫ expEvalHom a' b' ≫ q') := by
        rw [inner]
    _ = (prodTotalMap (𝟙 a'') (expMap p q) ≫
          prodTotalMap p' (𝟙 (expTotal a' b'))) ≫ (expEvalHom a' b' ≫ q') := by
        simp only [Category.assoc]
    _ = prodTotalMap p' (expMap p q) ≫ (expEvalHom a' b' ≫ q') := by
        rw [prodTotalMap_comp, Category.id_comp, Category.comp_id]
    _ = (prodTotalMap p' (𝟙 (expTotal a b)) ≫
          prodTotalMap (𝟙 a') (expMap p q)) ≫ (expEvalHom a' b' ≫ q') := by
        rw [prodTotalMap_comp, Category.comp_id, Category.id_comp]
    _ = prodTotalMap p' (𝟙 (expTotal a b)) ≫
          (prodTotalMap (𝟙 a') (expMap p q) ≫ expEvalHom a' b') ≫ q' := by
        simp only [Category.assoc]
    _ = prodTotalMap p' (𝟙 (expTotal a b)) ≫ expUncurry (expMap p q) ≫ q' := by
        rw [← expUncurry_eq]
    _ = prodTotalMap p' (𝟙 (expTotal a b)) ≫
          (prodTotalMap p (𝟙 (expTotal a b)) ≫ expEvalHom a b ≫ q) ≫ q' := by
        rw [outer]
    _ = (prodTotalMap p' (𝟙 (expTotal a b)) ≫
          prodTotalMap p (𝟙 (expTotal a b))) ≫ expEvalHom a b ≫ (q ≫ q') := by
        simp only [Category.assoc]
    _ = prodTotalMap (p' ≫ p) (𝟙 (expTotal a b)) ≫ expEvalHom a b ≫ (q ≫ q') := by
        rw [prodTotalMap_comp, Category.comp_id]
    _ = expUncurry (expMap (p' ≫ p) (q ≫ q')) := (expUncurry_expCurry _).symm

/-! ## Evaluation is natural under transport -/

/-- Evaluation commutes with transport: pairing the transported function with
an argument and evaluating equals transporting the argument, evaluating, and
transporting the result.  This is the law a consumer needs in order to treat
transport as an operation on functions rather than on their codes. -/
theorem expMap_eval {a a' b b' : PresheafPredicateTotal C}
    (p : a' ⟶ a) (q : b ⟶ b') :
    prodTotalMap (𝟙 a') (expMap p q) ≫ expEvalHom a' b'
      = prodTotalMap p (𝟙 (expTotal a b)) ≫ expEvalHom a b ≫ q := by
  rw [← expUncurry_eq, expMap, expUncurry_expCurry]

/-- At the identity pair it degenerates to evaluation itself. -/
theorem expMap_eval_id (a b : PresheafPredicateTotal C) :
    prodTotalMap (𝟙 a) (expMap (𝟙 a) (𝟙 b)) ≫ expEvalHom a b
      = expEvalHom a b := by
  rw [expMap_id, prodTotalMap_id, Category.id_comp]

/-! ## Naturality of curried evaluation under transport -/

@[simp] theorem lift_app_apply {c a b : Cᵒᵖ ⥤ Type u} (u : c ⟶ a) (v : c ⟶ b)
    (U : Cᵒᵖ) (x : c.obj U) :
    ((lift u v).app U x : a.obj U × b.obj U) = (u.app U x, v.app U x) := rfl

theorem expMap_eval_apply {a a' b b' : PresheafPredicateTotal C}
    (p : a' ⟶ a) (q : b ⟶ b')
    (U : Cᵒᵖ) (arg : a'.base.obj U) (f : (expBase a b).obj U) :
    (expEval a' b').app U (arg, (expMap p q).base.app U f)
      = q.base.app U ((expEval a b).app U (p.base.app U arg, f)) := by
  have based : (prodTotalMap (𝟙 a') (expMap p q) ≫ expEvalHom a' b').base
      = (prodTotalMap p (𝟙 (expTotal a b)) ≫ expEvalHom a b ≫ q).base :=
    congrArg Pseudofunctor.CoGrothendieck.Hom.base (expMap_eval p q)
  have appd := NatTrans.congr_app based U
  have pointwise := ConcreteCategory.congr_hom appd
    ((arg, f) : (a'.base ⊗ expBase a b).obj U)
  exact pointwise

/-- Curried evaluation is natural under transport: applying transported
functions to transported arguments lands in the transported results. -/
theorem applyPred_expMap_le {a a' b b' : PresheafPredicateTotal C}
    (p : a' ⟶ a) (q : b ⟶ b')
    (Θ : Subfunctor (expBase a b)) (α : Subfunctor a.base) :
    applyPred a' b' (Θ.image (expMap p q).base) (α.preimage p.base) ≤
      (applyPred a b Θ α).image q.base := by
  intro U value member
  obtain ⟨pair, held, image⟩ := member
  obtain ⟨arg, fn⟩ := pair
  obtain ⟨source, inTheta, mapped⟩ := held.2
  have first : p.base.app U arg ∈ α.obj U := held.1
  subst mapped
  refine ⟨(expEval a b).app U (p.base.app U arg, source),
    ⟨(p.base.app U arg, source), ⟨first, inTheta⟩, rfl⟩, ?_⟩
  refine Eq.trans ?_ image
  exact (expMap_eval_apply p q U arg source).symm

end Mettapedia.GSLT.Topos

#print axioms Mettapedia.GSLT.Topos.prodTotalMap_id
#print axioms Mettapedia.GSLT.Topos.prodTotalMap_comp
#print axioms Mettapedia.GSLT.Topos.expEvalHom_base
#print axioms Mettapedia.GSLT.Topos.expUncurry_eq
#print axioms Mettapedia.GSLT.Topos.expUncurry_naturality
#print axioms Mettapedia.GSLT.Topos.expMap_id
#print axioms Mettapedia.GSLT.Topos.expMap_comp
#print axioms Mettapedia.GSLT.Topos.expMap_eval
#print axioms Mettapedia.GSLT.Topos.expMap_eval_id
#print axioms Mettapedia.GSLT.Topos.expMap_eval_apply
#print axioms Mettapedia.GSLT.Topos.applyPred_expMap_le
