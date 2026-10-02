import Mettapedia.OSLF.Syntax.CategoricalBindingTargetChange

/-!
# Term interpretation through preserved selected function objects

The comparison is first proved on image stages. Generic generalized elements
then determine the interpretation at every stage of the new target.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.CategoricalBindingModel

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.FreeBindingTerms (FamilyArgs)

universe u v u' v'

variable {S : Signature}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {D' : Type u'} [Category.{v'} D'] [CartesianMonoidalCategory D']
variable (H : D ⥤ D') [PreservesFiniteProducts H] [ExponentialPreservation H]

set_option allowUnsafeReducibility true

attribute [local reducible] mapModel Model.kripke Model.kripkeSubstitution Model.interp
  BindingCloneFoldSubstitution.interpret BindingCloneFoldSubstitution.interpretArgs

/-- The product comparison used at a binder stage. -/
def binderStageComparison (M : Model S D) (bs : Ctx S) (Z : D) :
    (mapModel H M).ctx bs ⊗ H.obj Z ≅ H.obj (M.ctx bs ⊗ Z) :=
  tensorIso (contextComparison H M.sort bs) (Iso.refl _) ≪≫
    (prodComparisonIso H (M.ctx bs) Z).symm

@[reassoc]
theorem binderStageComparison_snd (M : Model S D) (bs : Ctx S) (Z : D) :
    (binderStageComparison H M bs Z).hom ≫ H.map (snd (M.ctx bs) Z) = snd _ _ := by
  simp only [binderStageComparison, Iso.trans_hom, MonoidalCategory.tensorIso, Iso.refl_hom,
    Iso.symm_hom, productComparisonIso_inv, Category.assoc,
    CartesianMonoidalCategory.inv_prodComparison_map_snd, tensorHom_snd, Category.comp_id]

@[reassoc]
theorem binderStageComparison_fst (M : Model S D) (bs : Ctx S) (Z : D) :
    (binderStageComparison H M bs Z).hom ≫ H.map (fst (M.ctx bs) Z) =
      fst _ _ ≫ (contextComparison H M.sort bs).hom := by
  simp only [binderStageComparison, Iso.trans_hom, MonoidalCategory.tensorIso, Iso.refl_hom,
    Iso.symm_hom, productComparisonIso_inv, Category.assoc,
    CartesianMonoidalCategory.inv_prodComparison_map_fst, tensorHom_fst]

/-- Mapping an environment componentwise. -/
def mapEnvironment (M : Model S D) {Γ : Ctx S} {Z : D} (ρ : M.Env Z Γ) :
    (mapModel H M).Env (H.obj Z) Γ := fun γ v => H.map (ρ γ v)

/-- The environment extension is compatible with the binder-stage comparison. -/
theorem extendEnv_map (M : Model S D) {Γ : Ctx S} {Z : D} (ρ : M.Env Z Γ) :
    ∀ (bs : Ctx S) {γ : S.Srt} (v : Var (bs ++ Γ) γ),
      (binderStageComparison H M bs Z).hom ≫ H.map (M.extendEnv bs ρ γ v) =
        (mapModel H M).extendEnv bs (mapEnvironment H M ρ) γ v
  | [], γ, v => by
      change (binderStageComparison H M [] Z).hom ≫ H.map (snd _ _ ≫ ρ γ v) = _
      rw [H.map_comp, binderStageComparison_snd_assoc]
      rfl
  | b :: bs, γ, v => by
      cases v with
      | zero =>
          change (binderStageComparison H M (b :: bs) Z).hom ≫ H.map (fst _ _ ≫ fst _ _) = _
          rw [H.map_comp, binderStageComparison_fst_assoc]
          change fst _ _ ≫ (contextComparison H M.sort (b :: bs)).hom ≫ H.map (projectVar M.sort Var.zero) =
            fst _ _ ≫ projectVar (fun s => H.obj (M.sort s)) Var.zero
          rw [contextComparison_projectVar]
      | succ w =>
          change (binderStageComparison H M (b :: bs) Z).hom ≫
            H.map (lift (fst _ _ ≫ snd _ _) (snd _ _) ≫ M.extendEnv bs ρ γ w) =
            lift (fst _ _ ≫ snd _ _) (snd _ _) ≫
              (mapModel H M).extendEnv bs (mapEnvironment H M ρ) γ w
          rw [H.map_comp]
          have exchange : (binderStageComparison H M (b :: bs) Z).hom ≫
              H.map (lift (fst _ _ ≫ snd _ _) (snd _ _)) =
              lift (fst _ _ ≫ snd _ _) (snd _ _) ≫ (binderStageComparison H M bs Z).hom := by
            apply (cancel_mono (prodComparisonIso H (M.ctx bs) Z).hom).mp
            apply hom_ext
            · simp only [Category.assoc, prodComparisonIso_hom,
                CartesianMonoidalCategory.prodComparison_fst, ← H.map_comp, lift_fst]
              rw [H.map_comp, binderStageComparison_fst_assoc]
              simp only [binderStageComparison_fst, Category.assoc, lift_fst_assoc]
              simp only [contextComparison, Iso.trans_hom, MonoidalCategory.tensorIso, Iso.refl_hom,
                Iso.symm_hom, productComparisonIso_inv, Category.assoc,
                CartesianMonoidalCategory.inv_prodComparison_map_snd, tensorHom_snd]
            · simp only [Category.assoc, prodComparisonIso_hom,
                CartesianMonoidalCategory.prodComparison_snd, ← H.map_comp, lift_snd,
                binderStageComparison_snd]
              exact binderStageComparison_snd H M (b :: bs) Z
          rw [← Category.assoc, exchange, Category.assoc, extendEnv_map M ρ bs w]


/-- Mapping a metavariable-family element through the family comparison. -/
def mapFamilyPoint (M : Model S D) (N : List (MetaArity S)) {Z : D}
    (m : Z ⟶ M.family N) : H.obj Z ⟶ (mapModel H M).family N :=
  H.map m ≫ (familyComparison H M.power N).inv

omit [PreservesFiniteProducts H] [ExponentialPreservation H] in
/-- An image of a product cone agrees with tupling its mapped components. -/
theorem map_lift_comparison {X Y Z : D} (f : Z ⟶ X) (g : Z ⟶ Y) :
    H.map (lift f g) ≫ CartesianMonoidalCategory.prodComparison H X Y =
      lift (H.map f) (H.map g) := by
  apply hom_ext <;> simp [← H.map_comp]

mutual

/-- Term interpretation agrees with mapping at each image stage. -/
theorem interp_value_map (M : Model S D) (N : List (MetaArity S)) :
    ∀ {Γ : Ctx S} {s : S.Srt} (t : Term (withMetas S N) Γ s)
      (Z : D) (m : Z ⟶ M.family N) (ρ : M.Env Z Γ),
      ((mapModel H M).interp N t).value (H.obj Z) (mapFamilyPoint H M N m)
        (mapEnvironment H M ρ) = H.map ((M.interp N t).value Z m ρ)
  | _, _, .var v, Z, m, ρ => rfl
  | Γ, s, .op (.inl o) args, Z, m, ρ => by
      change (mapModel H M).tupleArgs
          (BindingCloneFoldSubstitution.interpretArgs ((mapModel H M).kripke N) args)
          (H.obj Z) (mapFamilyPoint H M N m) (mapEnvironment H M ρ) ≫
          ((familyComparison H M.power (S.arity o)).hom ≫ H.map (M.op o)) = _
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ H.map (M.op o)) (tupleArgs_interp_map M N args Z m ρ)).trans
        (H.map_comp _ _).symm)
  | Γ, _, .op (.inr (.mk j)) args, Z, m, ρ => by
      change lift ((mapModel H M).tupleCtx (N.get j).1
          (BindingCloneFoldSubstitution.interpretArgs ((mapModel H M).kripke N) args)
          (H.obj Z) (mapFamilyPoint H M N m) (mapEnvironment H M ρ))
          (mapFamilyPoint H M N m ≫ (mapModel H M).familyProj N j) ≫
          (mapModel H M).eval _ _ = _
      rw [mapModel_eval]
      rw [← Category.assoc, lift_whiskerRight, tupleCtx_interp_map M N _ args Z m ρ]
      have component : mapFamilyPoint H M N m ≫ (mapModel H M).familyProj N j =
          H.map (m ≫ M.familyProj N j) := by
        rw [← familyComparison_proj H M, mapFamilyPoint]
        simp only [Category.assoc, Iso.inv_hom_id_assoc, ← H.map_comp]
      rw [component, ← map_lift_comparison H, Category.assoc]
      change H.map (lift _ _) ≫ CartesianMonoidalCategory.prodComparison H _ _ ≫
        inv (CartesianMonoidalCategory.prodComparison H _ _) ≫ H.map (M.eval _ _) = _
      rw [IsIso.hom_inv_id_assoc, ← H.map_comp]
      rfl
termination_by Γ s t Z _m _ρ => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- The tuple of curried authored arguments agrees under target change. -/
theorem tupleArgs_interp_map (M : Model S D) (N : List (MetaArity S)) :
    ∀ {Γ : Ctx S} {arity : List (MetaArity S)} (args : Args (withMetas S N) arity Γ)
      (Z : D) (m : Z ⟶ M.family N) (ρ : M.Env Z Γ),
      (mapModel H M).tupleArgs
          (BindingCloneFoldSubstitution.interpretArgs ((mapModel H M).kripke N) args)
          (H.obj Z) (mapFamilyPoint H M N m) (mapEnvironment H M ρ) ≫
          (familyComparison H M.power arity).hom =
        H.map (M.tupleArgs (BindingCloneFoldSubstitution.interpretArgs (M.kripke N) args) Z m ρ)
  | _, _, .nil, Z, m, ρ => by
      apply (isTerminalTensorUnit.isTerminalObj H).hom_ext
  | Γ, _, .cons (bs := bs) head tail, Z, m, ρ => by
      have headValue :
          ((mapModel H M).interp N head).value ((mapModel H M).ctx bs ⊗ H.obj Z)
            (snd _ _ ≫ mapFamilyPoint H M N m)
            ((mapModel H M).extendEnv bs (mapEnvironment H M ρ)) =
          (binderStageComparison H M bs Z).hom ≫
            H.map ((M.interp N head).value (M.ctx bs ⊗ Z) (snd _ _ ≫ m) (M.extendEnv bs ρ)) := by
        rw [← interp_value_map M N head (M.ctx bs ⊗ Z) (snd _ _ ≫ m) (M.extendEnv bs ρ),
          ← ((mapModel H M).interp N head).natural]
        congr 1
        · simp only [mapFamilyPoint, H.map_comp, Category.assoc,
            binderStageComparison_snd_assoc]
        · funext γ v
          exact (extendEnv_map H M ρ bs v).symm
      have headCurry : (mapModel H M).curry
          (((mapModel H M).interp N head).value ((mapModel H M).ctx bs ⊗ H.obj Z)
            (snd _ _ ≫ mapFamilyPoint H M N m)
            ((mapModel H M).extendEnv bs (mapEnvironment H M ρ))) =
          H.map (M.curry ((M.interp N head).value (M.ctx bs ⊗ Z) (snd _ _ ≫ m) (M.extendEnv bs ρ))) := by
        rw [headValue]
        simp only [binderStageComparison, Iso.trans_hom, MonoidalCategory.tensorIso, Iso.refl_hom,
          Iso.symm_hom, productComparisonIso_inv, tensorHom_id, Category.assoc]
        exact mapModel_curry H M _
      apply (cancel_mono (prodComparisonIso H (M.power bs _) (M.family _)).hom).mp
      change (lift _ _ ≫ ((familyComparison H M.power (_ :: _)).hom)) ≫
        CartesianMonoidalCategory.prodComparison H _ _ = _
      simp only [familyComparison, Iso.trans_hom, MonoidalCategory.tensorIso, Iso.refl_hom,
        Iso.symm_hom, productComparisonIso_inv, Category.assoc, IsIso.inv_hom_id,
        Category.comp_id, lift_map, Category.comp_id]
      exact (congrArg₂ lift headCurry (tupleArgs_interp_map M N tail Z m ρ)).trans
        (map_lift_comparison H _ _).symm
termination_by Γ arity args Z _m _ρ => sizeOf args
decreasing_by
  all_goals simp_wf
  all_goals omega


/-- The tuple of unbound metavariable arguments agrees under target change. -/
theorem tupleCtx_interp_map (M : Model S D) (N : List (MetaArity S)) :
    ∀ (bs : Ctx S) {Γ : Ctx S}
      (args : Args (withMetas S N) (bs.map fun b => ([], b)) Γ)
      (Z : D) (m : Z ⟶ M.family N) (ρ : M.Env Z Γ),
      (mapModel H M).tupleCtx bs
          (BindingCloneFoldSubstitution.interpretArgs ((mapModel H M).kripke N) args)
          (H.obj Z) (mapFamilyPoint H M N m) (mapEnvironment H M ρ) ≫
          (contextComparison H M.sort bs).hom =
        H.map (M.tupleCtx bs (BindingCloneFoldSubstitution.interpretArgs (M.kripke N) args) Z m ρ)
  | [], _, .nil, Z, m, ρ => by
      apply (isTerminalTensorUnit.isTerminalObj H).hom_ext
  | _ :: bs, Γ, .cons head tail, Z, m, ρ => by
      apply (cancel_mono (prodComparisonIso H (M.sort _) (M.ctx bs)).hom).mp
      change (lift _ _ ≫ ((contextComparison H M.sort (_ :: _)).hom)) ≫
        CartesianMonoidalCategory.prodComparison H _ _ = _
      simp only [contextComparison, Iso.trans_hom, MonoidalCategory.tensorIso, Iso.refl_hom,
        Iso.symm_hom, productComparisonIso_inv, Category.assoc, IsIso.inv_hom_id,
        Category.comp_id, lift_map, Category.comp_id]
      exact (congrArg₂ lift (interp_value_map M N head Z m ρ)
        (tupleCtx_interp_map M N bs tail Z m ρ)).trans (map_lift_comparison H _ _).symm
termination_by bs Γ args Z _m _ρ => sizeOf args
decreasing_by
  all_goals simp_wf
  all_goals have size := Args.cons.sizeOf_spec head tail
  all_goals omega


end

/-- The generic term arrow is the image of the original interpretation,
compared along the context and metavariable products. -/
theorem mapModel_generic (M : Model S D) (N : List (MetaArity S))
    {Γ : Ctx S} {s : S.Srt} (t : Term (withMetas S N) Γ s) :
    (mapModel H M).generic N t =
      ((contextComparison H M.sort Γ).hom ⊗ₘ (familyComparison H M.power N).hom) ≫
        inv (CartesianMonoidalCategory.prodComparison H (M.ctx Γ) (M.family N)) ≫
          H.map (M.generic N t) := by
  let k : (mapModel H M).ctx Γ ⊗ (mapModel H M).family N ⟶ H.obj (M.ctx Γ ⊗ M.family N) :=
    ((contextComparison H M.sort Γ).hom ⊗ₘ (familyComparison H M.power N).hom) ≫
      inv (CartesianMonoidalCategory.prodComparison H (M.ctx Γ) (M.family N))
  have point : k ≫ mapFamilyPoint H M N (snd (M.ctx Γ) (M.family N)) = snd _ _ := by
    dsimp [k, mapFamilyPoint]
    simp only [Category.assoc, CartesianMonoidalCategory.inv_prodComparison_map_snd_assoc,
      tensorHom_snd_assoc, Iso.hom_inv_id, Category.comp_id]
  have environment : (mapModel H M).restage k (mapEnvironment H M (M.genericEnv Γ (M.family N))) =
      (mapModel H M).genericEnv Γ ((mapModel H M).family N) := by
    funext γ v
    change k ≫ H.map (fst _ _ ≫ projectVar M.sort v) = fst _ _ ≫ projectVar _ v
    dsimp [k]
    rw [H.map_comp]
    simp only [Category.assoc, CartesianMonoidalCategory.inv_prodComparison_map_fst_assoc,
      tensorHom_fst_assoc, contextComparison_projectVar]
  have value := congrArg (k ≫ ·) (interp_value_map H M N t (M.ctx Γ ⊗ M.family N)
    (snd _ _) (M.genericEnv Γ (M.family N)))
  rw [← ((mapModel H M).interp N t).natural, point, environment] at value
  simpa only [Model.generic, k, Category.assoc] using value

/-- Mapping the curried generic term agrees with currying its transported
interpretation. -/
theorem mapModel_curry_generic (M : Model S D) (N : List (MetaArity S))
    {Γ : Ctx S} {s : S.Srt} (t : Term (withMetas S N) Γ s) :
    (mapModel H M).curry ((mapModel H M).generic N t) =
      (familyComparison H M.power N).hom ≫ H.map (M.curry (M.generic N t)) := by
  rw [mapModel_generic H M N t]
  have exchange : ((contextComparison H M.sort Γ).hom ⊗ₘ (familyComparison H M.power N).hom) =
      ((mapModel H M).ctx Γ ◁ (familyComparison H M.power N).hom) ≫
        ((contextComparison H M.sort Γ).hom ▷ H.obj (M.family N)) := by
    apply hom_ext <;> simp
  rw [exchange, Category.assoc, (mapModel H M).curry_natural, mapModel_curry]

end Mettapedia.OSLF.Binding.CategoricalBindingModel
