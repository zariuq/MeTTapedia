import Mettapedia.OSLF.Syntax.CategoricalBindingClassification
import Mettapedia.OSLF.Syntax.CategoricalBindingEquations

/-!
# Classification by models, with equations

Isomorphic models have naturally isomorphic classifying functors. For an
equation presentation, a structure-preserving functor that identifies
equation-related assignments has a model satisfying the presentation, and the
classifying functor of a model satisfying the presentation identifies them.
With the reconstruction of preserving functors from their models, this
classifies the structure-preserving interpretations of the equation-class
context category by the models of the presentation, up to isomorphism.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalBindingModel

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.SecondOrderContext

universe u v

variable {S : Signature}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

namespace Model

/-! ## Isomorphic models, isomorphic classifying functors -/

theorem projectVar_ctxMap {M N : Model S D} (f : ∀ s, M.sort s ⟶ N.sort s) :
    ∀ {Γ : Ctx S} {γ : S.Srt} (v : Var Γ γ),
      ctxMap f Γ ≫ projectVar N.sort v = projectVar M.sort v ≫ f γ
  | _ :: _, _, .zero => tensorHom_fst _ _
  | _ :: _, _, .succ v => by
      change (f _ ⊗ₘ ctxMap f _) ≫ snd _ _ ≫ projectVar N.sort v = (snd _ _ ≫ projectVar M.sort v) ≫ _
      rw [tensorHom_snd_assoc, projectVar_ctxMap f v, Category.assoc]

theorem familyMap_hom_inv {M N : Model S D} (e : M ≅ N) (L : List (List S.Srt × S.Srt)) :
    familyMap (Hom.power e.hom) L ≫ familyMap (Hom.power e.inv) L = 𝟙 _ := by
  rw [← familyMap_comp]
  have components : (fun Γ s => Hom.power e.hom Γ s ≫ Hom.power e.inv Γ s) = fun _ _ => 𝟙 _ := by
    funext Γ s
    rw [← comp_power, e.hom_inv_id]
    rfl
  rw [components]
  exact familyMap_id M L

/-- Generic values in isomorphic models correspond. -/
theorem generic_transport {M N : Model S D} (e : M ≅ N) (X : List (MetaArity S)) {Γ : Ctx S}
    {s : S.Srt} (t : Term (withMetas S X) Γ s) :
    (N.ctx Γ ◁ familyMap (Hom.power e.hom) X) ≫ N.generic X t =
      (ctxMap (Hom.sort e.inv) Γ ▷ M.family X) ≫ M.generic X t ≫ Hom.sort e.hom s := by
  unfold generic
  rw [← interp_transport e X t]
  change (N.ctx Γ ◁ familyMap (Hom.power e.hom) X) ≫ ((M.interp X t).value _
      (snd _ _ ≫ familyMap (Hom.power e.inv) X)
      (fun γ v => N.genericEnv Γ (N.family X) γ v ≫ Hom.sort e.inv γ) ≫ Hom.sort e.hom s) = _
  rw [← Category.assoc, ← (M.interp X t).natural, ← Category.assoc (ctxMap _ Γ ▷ _),
    ← (M.interp X t).natural]
  congr 2
  · rw [← Category.assoc, whiskerLeft_snd, Category.assoc, familyMap_hom_inv, Category.comp_id,
      whiskerRight_snd]
  · funext γ v
    change (N.ctx Γ ◁ familyMap (Hom.power e.hom) X) ≫ (fst _ _ ≫ projectVar N.sort v) ≫
        Hom.sort e.inv γ = (ctxMap (Hom.sort e.inv) Γ ▷ M.family X) ≫ fst _ _ ≫ projectVar M.sort v
    rw [Category.assoc, whiskerLeft_fst_assoc, whiskerRight_fst_assoc, projectVar_ctxMap]

/-- The classifying functors of isomorphic models are naturally isomorphic. -/
noncomputable def classifyingIsoOfIso {M N : Model S D} (e : M ≅ N) :
    M.classifyingFunctor ≅ N.classifyingFunctor :=
  NatIso.ofComponents
    (fun X => {
      hom := familyMap (Hom.power e.hom) X.arities
      inv := familyMap (Hom.power e.inv) X.arities
      hom_inv_id := familyMap_hom_inv e X.arities
      inv_hom_id := familyMap_inv_hom e X.arities })
    (fun {X Y} σ => by
      change M.assignHom σ ≫ familyMap (Hom.power e.hom) Y.arities =
        familyMap (Hom.power e.hom) X.arities ≫ N.assignHom σ
      unfold assignHom
      rw [N.familyLift_comp]
      apply N.familyLift_unique
      intro j
      rw [Category.assoc, familyMap_proj, ← Category.assoc, M.familyLift_proj, curry_transport,
        ← N.curry_natural, generic_transport])

end Model

/-! ## Equations -/

namespace Preserving

variable {F : SecondOrderContext.Object S ⥤ D} (hF : Preserving F)

/-- A natural family is determined by its generic value. -/
theorem elem_eq_of_generic {M : Model S D} {X : List (MetaArity S)} {Γ : Ctx S} {s : S.Srt}
    {x y : M.Elem X Γ s}
    (h : x.value (M.ctx Γ ⊗ M.family X) (snd _ _) (M.genericEnv Γ (M.family X)) =
      y.value (M.ctx Γ ⊗ M.family X) (snd _ _) (M.genericEnv Γ (M.family X))) : x = y := by
  apply Model.ElemOver.ext
  funext Z m ρ
  rw [M.value_eq_generic x, M.value_eq_generic y, h]

/-- **A preserving functor that identifies equation-related assignments has a
model of the presentation.** -/
theorem satisfies_of_respects {schema : List (MetaArity S)} (P : EquationPresentation S schema)
    (respects : ∀ {X Y : SecondOrderContext.Object S} {σ τ : X ⟶ Y}, P.homRel σ τ → F.map σ = F.map τ) :
    hF.toModel.Satisfies P := by
  intro X i Θ Δ body ambient ordinary
  have related : P.homRel
      (termArrow (ContextualAssignment.instantiate body ambient ordinary ((P.axioms X).get i).lhs))
      (termArrow (ContextualAssignment.instantiate body ambient ordinary ((P.axioms X).get i).rhs)) := by
    intro k
    rcases k with ⟨n, bound⟩
    change n < 1 at bound
    obtain rfl : n = 0 := by omega
    exact EqClosure.ax (E := P.axioms X) i body ambient ordinary
  have equal := respects related
  rw [hF.map_termArrow, hF.map_termArrow] at equal
  have curried := (cancel_epi (hF.famIso X.arities).hom).mp equal
  apply elem_eq_of_generic
  have generic := congrArg hF.toModel.uncurry curried
  rw [hF.toModel.uncurry_curry, hF.toModel.uncurry_curry] at generic
  exact generic

end Preserving

/-! ## The classification -/

/-- **Classification of structure-preserving interpretations by models.**

* the classifying functor of every model preserves the structure, and the
  model is recovered from it up to isomorphism;
* every structure-preserving functor is naturally isomorphic to the
  classifying functor of its own model;
* isomorphic models have naturally isomorphic classifying functors;
* a model satisfies an equation presentation exactly when its classifying
  functor identifies equation-related assignments, and then that functor
  factors through the equation-class context category. -/
theorem classification (M : Model S D) {F : SecondOrderContext.Object S ⥤ D} (hF : Preserving F)
    {schema : List (MetaArity S)} (P : EquationPresentation S schema) :
    Nonempty (M ≅ M.classifyingPreserving.toModel) ∧
      Nonempty (F ≅ hF.toModel.classifyingFunctor) ∧
      (M.Satisfies P → ∀ {X Y : SecondOrderContext.Object S} {σ τ : X ⟶ Y},
        P.homRel σ τ → M.classifyingFunctor.map σ = M.classifyingFunctor.map τ) ∧
      ((∀ {X Y : SecondOrderContext.Object S} {σ τ : X ⟶ Y}, P.homRel σ τ → F.map σ = F.map τ) →
        hF.toModel.Satisfies P) :=
  ⟨⟨M.classifyingModelIso⟩, ⟨hF.isoClassifying⟩,
    fun sat _ _ _ _ related => M.assignHom_congr P sat related,
    fun respects => hF.satisfies_of_respects P respects⟩

end Mettapedia.OSLF.Binding.CategoricalBindingModel

#print axioms Mettapedia.OSLF.Binding.CategoricalBindingModel.classification
#print axioms Mettapedia.OSLF.Binding.CategoricalBindingModel.Model.classifyingIsoOfIso
#print axioms Mettapedia.OSLF.Binding.CategoricalBindingModel.Preserving.isoClassifying
#print axioms Mettapedia.OSLF.Binding.CategoricalBindingModel.Model.classifyingPreserving
