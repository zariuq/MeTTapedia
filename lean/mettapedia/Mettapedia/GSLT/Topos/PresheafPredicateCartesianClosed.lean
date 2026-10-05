import Mettapedia.GSLT.Topos.PresheafPredicateProjectionPreservation
import Mathlib.CategoryTheory.Monoidal.Closed.Functor
import Mettapedia.GSLT.Topos.PresheafPredicateLimits

/-!
# Cartesian closed structure of the total predicate category

The chosen products and exponentials already constructed for presheaf predicates
supply the actual cartesian monoidal and closed instances. Their adjunction is
the existing curry/uncurry bijection. The projection preserves products and has
invertible exponential comparison, so it is a cartesian closed functor. The
Frobenius proof works for any chosen closed structure on the presheaf base;
the strict comparison additionally uses the standard pointwise presentation.

This is Proposition 14 of Williams and Stay, *Native Type Theory* (ACT 2021),
for small categories and presheaves in the same universe. Together with
`PresheafPredicateLimits`, it gives the total category's cosmic structure.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.PredicateCartesianClosed

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory

universe u
variable {C : Type u} [Category.{u} C]

def productIsLimit (a b : PresheafPredicateTotal C) :
    IsLimit (BinaryFan.mk (prodTotalFst a b) (prodTotalSnd a b)) :=
  BinaryFan.isLimitMk (fun s => prodTotalLift s.fst s.snd)
    (fun s => prodTotalLift_fst s.fst s.snd)
    (fun s => prodTotalLift_snd s.fst s.snd)
    (fun s m first second => prodTotalLift_unique s.fst s.snd m first second)

noncomputable instance cartesian : CartesianMonoidalCategory (PresheafPredicateTotal C) :=
  CartesianMonoidalCategory.ofChosenFiniteProducts
    { cone := asEmptyCone (unitTotal C), isLimit := unitTotalIsTerminal C }
    (fun a b =>
      { cone := BinaryFan.mk (prodTotalFst a b) (prodTotalSnd a b)
        isLimit := productIsLimit a b })

theorem tensorLeft_map (a : PresheafPredicateTotal C)
    {b c : PresheafPredicateTotal C} (f : b ⟶ c) :
    (tensorLeft a).map f = prodTotalMap (𝟙 a) f := by
  apply hom_ext
  change lift (fst a.base b.base) (snd a.base b.base ≫ f.base) =
    lift (fst a.base b.base ≫ 𝟙 a.base) (snd a.base b.base ≫ f.base)
  rw [Category.comp_id]

noncomputable def exponential (a : PresheafPredicateTotal C) :
    PresheafPredicateTotal C ⥤ PresheafPredicateTotal C where
  obj b := expTotal a b
  map f := expMap (𝟙 a) f
  map_id b := expMap_id a b
  map_comp f g := by
    rw [expMap_comp, Category.id_comp]

noncomputable def exponentialAdjunction (a : PresheafPredicateTotal C) :
    tensorLeft a ⊣ exponential a :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun c b => expHomEquiv a b c
      homEquiv_naturality_left_symm := by
        intro c c' b g f
        rw [tensorLeft_map]
        exact expUncurry_naturality g f
      homEquiv_naturality_right := by
        intro c b b' f g
        change expCurry (f ≫ g) = expCurry f ≫ expMap (𝟙 a) g
        apply expUncurry_injective
        rw [expUncurry_expCurry, expUncurry_naturality,
          expMap, expUncurry_expCurry, prodTotalMap_id, Category.id_comp,
          ← Category.assoc, ← expUncurry_eq, expUncurry_expCurry] }

noncomputable instance closed : MonoidalClosed (PresheafPredicateTotal C) where
  closed a := { rightAdj := exponential a, adj := exponentialAdjunction a }

theorem curry_is_existing {a b c : PresheafPredicateTotal C}
    (f : prodTotal a c ⟶ b) : MonoidalClosed.curry f = expCurry f := by
  change (exponentialAdjunction a).homEquiv c b f = expCurry f
  rw [exponentialAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

theorem uncurry_is_existing {a b c : PresheafPredicateTotal C}
    (f : c ⟶ expTotal a b) : MonoidalClosed.uncurry f = expUncurry f := by
  change ((exponentialAdjunction a).homEquiv c b).symm f = expUncurry f
  rw [exponentialAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

theorem projection_productComparison (a b : PresheafPredicateTotal C) :
    CartesianMonoidalCategory.prodComparison (presheafPredicateProjection C) a b = 𝟙 (a.base ⊗ b.base) := by
  change lift (fst a.base b.base) (snd a.base b.base) = 𝟙 (a.base ⊗ b.base)
  exact lift_fst_snd

theorem projection_evaluation (a b : PresheafPredicateTotal C) :
    (presheafPredicateProjection C).map ((ihom.ev a).app b) =
      (ihom.ev a.base).app b.base := by
  change (expEvalHom a b).base = expEval a b
  exact expEvalHom_base a b

section CanonicalBaseClosed

attribute [local instance] FunctorToTypes.monoidalClosed

/-- The canonical exponential comparison is the identity on the underlying
presheaf exponential. This proves preservation as a cartesian closed functor. -/
theorem projection_expComparison (a b : PresheafPredicateTotal C) :
    (expComparison (presheafPredicateProjection C) a).natTrans.app b =
      𝟙 ((ihom a.base).obj b.base) := by
  apply MonoidalClosed.uncurry_injective
  rw [uncurry_expComparison]
  change inv (CartesianMonoidalCategory.prodComparison (presheafPredicateProjection C)
      a (expTotal a b)) ≫ (expEvalHom a b).base =
    MonoidalClosed.uncurry (𝟙 ((ihom a.base).obj b.base))
  have inverse : inv (CartesianMonoidalCategory.prodComparison
      (presheafPredicateProjection C) a (expTotal a b)) =
        𝟙 (a.base ⊗ expBase a b) := by
    apply IsIso.inv_eq_of_hom_inv_id
    exact (Category.comp_id _).trans (projection_productComparison a (expTotal a b))
  rw [inverse]
  change 𝟙 (a.base ⊗ expBase a b) ≫ expEval a b =
    MonoidalClosed.uncurry (𝟙 ((ihom a.base).obj b.base))
  rw [Category.id_comp, MonoidalClosed.uncurry_id_eq_ev]

end CanonicalBaseClosed

/-- Equip each presheaf with the empty predicate. -/
noncomputable def falsityFunctor : (Cᵒᵖ ⥤ Type u) ⥤ PresheafPredicateTotal C where
  obj P := totalOfPredicate P ⊥
  map f := homOfEntailment f bot_le
  map_id _ := hom_ext _ _ rfl
  map_comp _ _ := hom_ext _ _ rfl

/-- Every base map out of an empty predicate is a predicate morphism. -/
noncomputable def falsityAdjunction : falsityFunctor (C := C) ⊣ presheafPredicateProjection C :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P a =>
        { toFun := fun f => f.base
          invFun := fun f => homOfEntailment f bot_le
          left_inv := fun f => hom_ext _ _ rfl
          right_inv := fun _ => rfl }
      homEquiv_naturality_left_symm := by intros; exact hom_ext _ _ rfl
      homEquiv_naturality_right := by intros; rfl }

/-- Pairing an arbitrary predicate with falsity gives falsity. The resulting
Frobenius isomorphism proves closedness without choosing a base exponential. -/
noncomputable instance projectionFrobenius (a : PresheafPredicateTotal C) :
    IsIso (frobeniusMorphism (presheafPredicateProjection C) falsityAdjunction a).natTrans := by
  have (P : Cᵒᵖ ⥤ Type u) :
      IsIso ((frobeniusMorphism (presheafPredicateProjection C) falsityAdjunction a).natTrans.app P) := by
    let backward : a ⊗ falsityFunctor.obj P ⟶ falsityFunctor.obj (a.base ⊗ P) :=
      homOfEntailment (𝟙 _) (by intro U x member; exact member.2)
    refine ⟨⟨backward, ?_, ?_⟩⟩
    · apply hom_ext
      change (lift (fst a.base P) (snd a.base P)) ≫
          (lift (fst a.base P ≫ 𝟙 _) (snd a.base P)) ≫ 𝟙 _ = 𝟙 _
      simp only [Category.comp_id, lift_fst_snd]
    · apply hom_ext
      change 𝟙 _ ≫ (lift (fst a.base P) (snd a.base P)) ≫
          (lift (fst a.base P ≫ 𝟙 _) (snd a.base P)) = 𝟙 _
      simp only [Category.comp_id, lift_fst_snd]
  exact NatIso.isIso_of_isIso_app _

/-- Exponential preservation is independent of the chosen base right adjoints. -/
noncomputable instance projectionClosed [MonoidalClosed (Cᵒᵖ ⥤ Type u)] :
    MonoidalClosedFunctor (presheafPredicateProjection C) where
  comparison_iso a :=
    expComparison_iso_of_frobeniusMorphism_iso (presheafPredicateProjection C) falsityAdjunction a

end Mettapedia.GSLT.Topos.PredicateCartesianClosed
