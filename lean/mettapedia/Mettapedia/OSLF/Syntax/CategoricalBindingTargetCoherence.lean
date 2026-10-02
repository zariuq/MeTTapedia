import Mettapedia.OSLF.Syntax.CategoricalBindingTargetComposition
import Mettapedia.OSLF.Syntax.CategoricalBindingTargetPreservationEquations

/-!
# Coherence of successive target changes for binding interpretations

The context and family product comparisons respect identity and composition.
They identify the actual mapped program objects and selected function objects,
and induce the corresponding coherence isomorphisms of equation models.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.CategoricalBindingModel

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.SecondOrderContext

universe u v u' v' u'' v''

variable {S : Signature}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {D' : Type u'} [Category.{v'} D'] [CartesianMonoidalCategory D']
variable {D'' : Type u''} [Category.{v''} D''] [CartesianMonoidalCategory D'']

/-- Evaluation and operator data determine a model: currying is forced by
the selected function objects' universal properties. -/
theorem Model.eq_of_operation_data {M N : Model S D}
    (sort : M.sort = N.sort) (power : M.power = N.power)
    (eval : HEq M.eval N.eval) (op : HEq (@M.op) (@N.op)) : M = N := by
  cases M with
  | mk msort mpower meval mcurry mcurry_eval mcurry_unique mop =>
    cases N with
    | mk nsort npower neval ncurry ncurry_eval ncurry_unique nop =>
      cases sort
      cases power
      cases eq_of_heq eval
      cases eq_of_heq op
      have curry : @mcurry = @ncurry := by
        funext Γ s Z f
        exact (ncurry_unique f (mcurry f) (mcurry_eval f)).symm
      cases curry
      rfl

theorem terminalComparison_identity :
    CartesianMonoidalCategory.terminalComparison (𝟭 D) = 𝟙 (𝟙_ D) :=
  toUnit_unique _ _

theorem terminalComparison_composite (H : D ⥤ D') (K : D' ⥤ D'') :
    CartesianMonoidalCategory.terminalComparison (H ⋙ K) =
      K.map (CartesianMonoidalCategory.terminalComparison H) ≫
        CartesianMonoidalCategory.terminalComparison K :=
  toUnit_unique _ _

@[simp]
theorem contextComparison_identity (sort : S.Srt → D) :
    ∀ Γ, contextComparison (𝟭 D) sort Γ = Iso.refl (contextOf sort Γ)
  | [] => by
      apply Iso.ext
      simp only [contextComparison, Iso.symm_hom, asIso_inv,
        terminalComparison_identity, Iso.refl_hom]
      exact IsIso.inv_id
  | s :: Γ => by
      apply Iso.ext
      simp only [contextComparison, contextComparison_identity sort Γ, prodComparisonIso_id,
        Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
        Iso.refl_inv, Functor.id_obj]
      simp only [id_tensorHom_id, Category.comp_id]

@[simp]
theorem familyComparison_identity (power : Ctx S → S.Srt → D) :
    ∀ L, familyComparison (𝟭 D) power L = Iso.refl (familyOf power L)
  | [] => by
      apply Iso.ext
      simp only [familyComparison, Iso.symm_hom, asIso_inv,
        terminalComparison_identity, Iso.refl_hom]
      exact IsIso.inv_id
  | a :: L => by
      apply Iso.ext
      simp only [familyComparison, familyComparison_identity power L, prodComparisonIso_id,
        Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
        Iso.refl_inv, Functor.id_obj]
      simp only [id_tensorHom_id, Category.comp_id]

variable (H : D ⥤ D') (K : D' ⥤ D'')
variable [PreservesFiniteProducts H] [PreservesFiniteProducts K]

theorem productComparison_inv_composite (A B : D) :
    inv (CartesianMonoidalCategory.prodComparison (H ⋙ K) A B) =
      inv (CartesianMonoidalCategory.prodComparison K (H.obj A) (H.obj B)) ≫
        K.map (inv (CartesianMonoidalCategory.prodComparison H A B)) := by
  rw [← productComparisonIso_inv, prodComparisonIso_comp]
  simp only [Iso.trans_inv, Functor.mapIso_inv, productComparisonIso_inv]

theorem contextComparison_composite (sort : S.Srt → D) :
    ∀ Γ, contextComparison (H ⋙ K) sort Γ =
      contextComparison K (fun s => H.obj (sort s)) Γ ≪≫
        K.mapIso (contextComparison H sort Γ)
  | [] => by
      apply Iso.ext
      simp only [contextComparison, Iso.symm_hom, asIso_inv, Iso.trans_hom,
        Functor.mapIso_hom]
      simp only [terminalComparison_composite, IsIso.inv_comp, K.map_inv]
  | s :: Γ => by
      apply Iso.ext
      simp only [contextComparison, contextComparison_composite sort Γ,
        Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Iso.symm_hom,
        Functor.mapIso_hom, K.map_comp, productComparisonIso_inv]
      rw [productComparison_inv_composite H K]
      simp only [Category.assoc]
      rw [CartesianMonoidalCategory.prodComparison_inv_natural_assoc K, K.map_id]
      simp only [id_tensorHom, whiskerLeft_comp, Category.assoc, Functor.comp_obj]

theorem familyComparison_composite (power : Ctx S → S.Srt → D) :
    ∀ L, familyComparison (H ⋙ K) power L =
      familyComparison K (fun Γ s => H.obj (power Γ s)) L ≪≫
        K.mapIso (familyComparison H power L)
  | [] => by
      apply Iso.ext
      simp only [familyComparison, Iso.symm_hom, asIso_inv, Iso.trans_hom,
        Functor.mapIso_hom]
      simp only [terminalComparison_composite, IsIso.inv_comp, K.map_inv]
  | a :: L => by
      apply Iso.ext
      simp only [familyComparison, familyComparison_composite power L,
        Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Iso.symm_hom,
        Functor.mapIso_hom, K.map_comp, productComparisonIso_inv]
      rw [productComparison_inv_composite H K]
      simp only [Category.assoc]
      rw [CartesianMonoidalCategory.prodComparison_inv_natural_assoc K, K.map_id]
      simp only [id_tensorHom, whiskerLeft_comp, Category.assoc, Functor.comp_obj]

theorem mapModel_identity_eval (M : Model S D) (Γ : Ctx S) (s : S.Srt) :
    (mapModel (𝟭 D) M).eval Γ s = M.eval Γ s := by
  rw [mapModel_eval, contextComparison_identity, ← productComparisonIso_inv,
    prodComparisonIso_id]
  simp only [Iso.refl_hom, Iso.refl_inv, Functor.id_obj, Functor.id_map,
    id_whiskerRight, Category.id_comp]

theorem mapModel_identity_op (M : Model S D) {s : S.Srt} (o : S.Op s) :
    (mapModel (𝟭 D) M).op o = M.op o := by
  change (familyComparison (𝟭 D) M.power (S.arity o)).hom ≫ M.op o = M.op o
  rw [familyComparison_identity]
  exact Category.id_comp _

theorem mapModel_identity (M : Model S D) : mapModel (𝟭 D) M = M := by
  apply Model.eq_of_operation_data (M := mapModel (𝟭 D) M) (N := M) rfl rfl
  · exact heq_of_eq (funext fun Γ => funext fun s => mapModel_identity_eval M Γ s)
  · exact heq_of_eq (funext fun s => funext fun o => mapModel_identity_op M (s := s) o)

variable [ExponentialPreservation H] [ExponentialPreservation K]

theorem mapModel_composite_op (M : Model S D) {s : S.Srt} (o : S.Op s) :
    (mapModel K (mapModel H M)).op o = (mapModel (H ⋙ K) M).op o := by
  change (familyComparison K (fun Γ s => H.obj (M.power Γ s)) (S.arity o)).hom ≫
      K.map ((familyComparison H M.power (S.arity o)).hom ≫ H.map (M.op o)) =
    (familyComparison (H ⋙ K) M.power (S.arity o)).hom ≫ K.map (H.map (M.op o))
  rw [familyComparison_composite]
  simp only [Iso.trans_hom, Functor.mapIso_hom, K.map_comp, Category.assoc]

theorem mapModel_composite_eval (M : Model S D) (Γ : Ctx S) (s : S.Srt) :
    (mapModel K (mapModel H M)).eval Γ s = (mapModel (H ⋙ K) M).eval Γ s := by
  rw [mapModel_eval, mapModel_eval, mapModel_eval, K.map_comp, K.map_comp]
  change ((contextComparison K (fun s => H.obj (M.sort s)) Γ).hom ▷ K.obj (H.obj (M.power Γ s))) ≫
    inv (CartesianMonoidalCategory.prodComparison K (contextOf (fun s => H.obj (M.sort s)) Γ)
      (H.obj (M.power Γ s))) ≫
    (K.map ((contextComparison H M.sort Γ).hom ▷ H.obj (M.power Γ s)) ≫
      K.map (inv (CartesianMonoidalCategory.prodComparison H (M.ctx Γ) (M.power Γ s))) ≫
        K.map (H.map (M.eval Γ s))) =
    ((contextComparison (H ⋙ K) M.sort Γ).hom ▷ K.obj (H.obj (M.power Γ s))) ≫
      inv (CartesianMonoidalCategory.prodComparison (H ⋙ K) (M.ctx Γ) (M.power Γ s)) ≫
        K.map (H.map (M.eval Γ s))
  rw [contextComparison_composite, productComparison_inv_composite]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [CartesianMonoidalCategory.prodComparison_inv_natural_whiskerRight_assoc K]
  rw [comp_whiskerRight]
  simp only [Category.assoc]

theorem mapModel_composite (M : Model S D) :
    mapModel K (mapModel H M) = mapModel (H ⋙ K) M := by
  apply Model.eq_of_operation_data (M := mapModel K (mapModel H M))
    (N := mapModel (H ⋙ K) M) rfl rfl
  · exact heq_of_eq (funext fun Γ => funext fun s => mapModel_composite_eval H K M Γ s)
  · exact heq_of_eq (funext fun s => funext fun o => mapModel_composite_op H K M (s := s) o)

namespace SatisfyingTargetCoherence

open CategoricalBindingEquationEquivalence CategoricalBindingInterpretationMaps

variable {schema : List (MetaArity S)} {P : EquationPresentation S schema}

theorem eq_of_model_eq {M N : SatisfyingInterpretation (D := D) P}
    (same : M.interpretation.model = N.interpretation.model) : M = N := by
  cases M with
  | mk mi ms =>
    cases N with
    | mk ni ns =>
      cases mi
      cases ni
      cases same
      rfl

theorem eqToHom_sort {M N : SatisfyingInterpretation (D := D) P}
    (same : M = N) (s : S.Srt) :
    (eqToHom same).underlying.sort s =
      eqToHom (congrArg (fun M => M.interpretation.model.sort s) same) := by
  cases same
  rfl

theorem eqToHom_power {M N : SatisfyingInterpretation (D := D) P}
    (same : M = N) (Γ : Ctx S) (s : S.Srt) :
    (eqToHom same).underlying.power Γ s =
      eqToHom (congrArg (fun M => M.interpretation.model.power Γ s) same) := by
  cases same
  rfl

end SatisfyingTargetCoherence

open CategoricalBindingEquationEquivalence CategoricalBindingInterpretationMaps

variable {schema : List (MetaArity S)} (P : EquationPresentation S schema)

theorem mapSatisfyingInterpretations_identity_obj
    (M : SatisfyingInterpretation (D := D) P) :
    (mapSatisfyingInterpretations (𝟭 D) P).obj M = M :=
  SatisfyingTargetCoherence.eq_of_model_eq (mapModel_identity M.interpretation.model)

/-- The identity target change has identity components on the actual sort
and chosen function objects. -/
def mapSatisfyingIdentityComponent (M : SatisfyingInterpretation (D := D) P) :
    (mapSatisfyingInterpretations (𝟭 D) P).obj M ≅ M :=
  eqToIso (mapSatisfyingInterpretations_identity_obj P M)

@[simp]
theorem mapSatisfyingIdentityComponent_hom_sort (M : SatisfyingInterpretation (D := D) P)
    (s : S.Srt) :
    (mapSatisfyingIdentityComponent P M).hom.underlying.sort s = 𝟙 (M.interpretation.model.sort s) := by
  exact SatisfyingTargetCoherence.eqToHom_sort (mapSatisfyingInterpretations_identity_obj P M) s

@[simp]
theorem mapSatisfyingIdentityComponent_hom_power (M : SatisfyingInterpretation (D := D) P)
    (Γ : Ctx S) (s : S.Srt) :
    (mapSatisfyingIdentityComponent P M).hom.underlying.power Γ s =
      𝟙 (M.interpretation.model.power Γ s) := by
  exact SatisfyingTargetCoherence.eqToHom_power (mapSatisfyingInterpretations_identity_obj P M) Γ s

/-- Identity target change is naturally isomorphic to the identity on the
whole equation-model category, including all noninvertible maps. -/
def mapSatisfyingInterpretationsIdentityIso :
    mapSatisfyingInterpretations (𝟭 D) P ≅ 𝟭 (SatisfyingInterpretation (D := D) P) :=
  NatIso.ofComponents (mapSatisfyingIdentityComponent P) (fun {M N} f => by
    apply CategoricalBindingInterpretationMaps.Hom.ext
    apply Model.Hom.ext
    · funext s
      change (mapModelHom (𝟭 D) f.underlying).sort s ≫
        (mapSatisfyingIdentityComponent P N).hom.underlying.sort s =
          (mapSatisfyingIdentityComponent P M).hom.underlying.sort s ≫ f.underlying.sort s
      rw [mapSatisfyingIdentityComponent_hom_sort, mapSatisfyingIdentityComponent_hom_sort]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
    · funext Γ s
      change (mapModelHom (𝟭 D) f.underlying).power Γ s ≫
        (mapSatisfyingIdentityComponent P N).hom.underlying.power Γ s =
          (mapSatisfyingIdentityComponent P M).hom.underlying.power Γ s ≫ f.underlying.power Γ s
      rw [mapSatisfyingIdentityComponent_hom_power, mapSatisfyingIdentityComponent_hom_power]
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

theorem mapSatisfyingInterpretations_composite_obj (M : SatisfyingInterpretation (D := D) P) :
    (mapSatisfyingInterpretations K P).obj ((mapSatisfyingInterpretations H P).obj M) =
      (mapSatisfyingInterpretations (H ⋙ K) P).obj M :=
  SatisfyingTargetCoherence.eq_of_model_eq (mapModel_composite H K M.interpretation.model)

/-- Successive target changes compare the actual iterated image objects to
the objects of the composite functor. -/
def mapSatisfyingCompositeComponent (M : SatisfyingInterpretation (D := D) P) :
    (mapSatisfyingInterpretations K P).obj ((mapSatisfyingInterpretations H P).obj M) ≅
      (mapSatisfyingInterpretations (H ⋙ K) P).obj M :=
  eqToIso (mapSatisfyingInterpretations_composite_obj H K P M)

@[simp]
theorem mapSatisfyingCompositeComponent_hom_sort (M : SatisfyingInterpretation (D := D) P)
    (s : S.Srt) :
    (mapSatisfyingCompositeComponent H K P M).hom.underlying.sort s =
      𝟙 (K.obj (H.obj (M.interpretation.model.sort s))) := by
  exact SatisfyingTargetCoherence.eqToHom_sort (mapSatisfyingInterpretations_composite_obj H K P M) s

@[simp]
theorem mapSatisfyingCompositeComponent_hom_power (M : SatisfyingInterpretation (D := D) P)
    (Γ : Ctx S) (s : S.Srt) :
    (mapSatisfyingCompositeComponent H K P M).hom.underlying.power Γ s =
      𝟙 (K.obj (H.obj (M.interpretation.model.power Γ s))) := by
  exact SatisfyingTargetCoherence.eqToHom_power (mapSatisfyingInterpretations_composite_obj H K P M) Γ s

/-- Successive target changes agree naturally with their composite on all
lawful equation models and their interpretation maps. -/
def mapSatisfyingInterpretationsCompositeIso :
    mapSatisfyingInterpretations H P ⋙ mapSatisfyingInterpretations K P ≅
      mapSatisfyingInterpretations (H ⋙ K) P :=
  NatIso.ofComponents (mapSatisfyingCompositeComponent H K P) (fun {M N} f => by
    apply CategoricalBindingInterpretationMaps.Hom.ext
    apply Model.Hom.ext
    · funext s
      change K.map (H.map (f.underlying.sort s)) ≫
        (mapSatisfyingCompositeComponent H K P N).hom.underlying.sort s =
          (mapSatisfyingCompositeComponent H K P M).hom.underlying.sort s ≫
            (H ⋙ K).map (f.underlying.sort s)
      rw [mapSatisfyingCompositeComponent_hom_sort, mapSatisfyingCompositeComponent_hom_sort]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
    · funext Γ s
      change K.map (H.map (f.underlying.power Γ s)) ≫
        (mapSatisfyingCompositeComponent H K P N).hom.underlying.power Γ s =
          (mapSatisfyingCompositeComponent H K P M).hom.underlying.power Γ s ≫
            (H ⋙ K).map (f.underlying.power Γ s)
      rw [mapSatisfyingCompositeComponent_hom_power, mapSatisfyingCompositeComponent_hom_power]
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

end Mettapedia.OSLF.Binding.CategoricalBindingModel
