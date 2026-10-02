import Mettapedia.OSLF.Syntax.CategoricalBindingFunctor
import Mettapedia.OSLF.Syntax.SecondOrderBindingModelRestriction

/-!
# Binding clones of generalized elements

Natural families over a stage are represented by the selected function
objects. Their operators, substitution and restaging precede equation soundness.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalBindingModel

open _root_.CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.FreeBindingTerms (FamilyArgs)
open Mettapedia.OSLF.Binding.SecondOrderContext

universe u v

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

namespace Model

variable {S : Signature} (M : Model S D)

/-! ## Natural families are maps into function objects -/

/-- The value of a natural family at its generic stage. -/
def elemValue {C : D} {Γ : Ctx S} {s : S.Srt} (x : M.ElemOver C Γ s) :
    M.ctx Γ ⊗ C ⟶ M.sort s :=
  x.value (M.ctx Γ ⊗ C) (snd _ _) (M.genericEnv Γ C)

/-- The natural family named by a map into a function object. -/
def elemOfPoint {C : D} {Γ : Ctx S} {s : S.Srt} (g : C ⟶ M.power Γ s) : M.ElemOver C Γ s where
  value W w ρ := lift (M.tupleEnv ρ) (w ≫ g) ≫ M.eval Γ s
  natural h w ρ := by
    rw [M.tupleEnv_restage, Category.assoc, ← comp_lift_assoc]

/-- **Natural families over a stage are maps into the function object.** -/
def elemEquiv {C : D} {Γ : Ctx S} {s : S.Srt} : M.ElemOver C Γ s ≃ (C ⟶ M.power Γ s) where
  toFun x := M.curry (M.elemValue x)
  invFun g := M.elemOfPoint g
  left_inv x := by
    apply ElemOver.ext
    funext W w ρ
    change lift (M.tupleEnv ρ) (w ≫ M.curry (M.elemValue x)) ≫ M.eval Γ s = x.value W w ρ
    rw [M.value_eq_generic x W w ρ, ← lift_whiskerLeft, Category.assoc, M.curry_eval]
    rfl
  right_inv g := by
    apply M.curry_unique
    change (M.ctx Γ ◁ g) ≫ M.eval Γ s =
      lift (M.tupleEnv (M.genericEnv Γ C)) (snd _ _ ≫ g) ≫ M.eval Γ s
    rw [genericEnv, M.tupleEnv_restage, M.tupleEnv_projections, Category.comp_id,
      lift_fst_snd_comp]

/-- Natural families over a stage object, with the operators of the signature
and no metavariables. -/
def stageKripke (C : D) : BindingCloneAlgebra.Algebra.{max u v} (withMetas S []) where
  substitution := M.kripkeSubstitution C
  operation := fun o args =>
    match o, args with
    | .inl o, args => M.opElem o args
    | .inr (.mk i), _ => i.elim0
  operation_substitute := by
    intro Γ Δ s env o args
    match o, args with
    | .inl o, args => exact M.opElem_substitute env o args
    | .inr (.mk i), _ => exact i.elim0

/-- The binding clone of natural families over a stage object. -/
def stage (C : D) : BindingCloneAlgebra.Algebra.{max u v} S :=
  restrictAlgebra ⟨[]⟩ (M.stageKripke C)

theorem tupleArgs_toAmbientArgs {C : D} (X Y : Object S) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : FamilyArgs S (M.ElemOver C) arity Γ) (Z : D) (m : Z ⟶ C) (ρ : M.Env Z Γ),
      M.tupleArgs (toAmbientArgs X args) Z m ρ = M.tupleArgs (toAmbientArgs Y args) Z m ρ
  | _, _, .nil, _, _, _ => rfl
  | _, _, .cons _ tail, Z, m, ρ => by
      show lift _ _ = lift _ _
      rw [tupleArgs_toAmbientArgs X Y tail Z m ρ]

/-- Restaging commutes with an operator, whichever metavariable signature
carries the arguments. -/
theorem restageElem_opElem {C C' : D} (x : C' ⟶ C) (X Y : Object S) {Γ : Ctx S} {s : S.Srt}
    (o : S.Op s) (args : FamilyArgs S (M.ElemOver C) (S.arity o) Γ) :
    M.restageElem x (M.opElem o (toAmbientArgs X args)) =
      M.opElem o (toAmbientArgs Y (FamilyArgs.map (fun e => M.restageElem x e) args)) := by
  apply ElemOver.ext
  funext W w ρ
  refine congrArg (· ≫ M.op o) ?_
  refine (M.tupleArgs_toAmbientArgs X Y args W (w ≫ x) ρ).trans ?_
  refine (M.tupleArgs_restage x (toAmbientArgs Y args) W w ρ).symm.trans ?_
  exact congrArg (fun a => M.tupleArgs a W w ρ)
    (toAmbientArgs_map Y (fun e => M.restageElem x e) args).symm

/-- Restaging natural families along a generalized element of the
metavariable family is a map of binding clones. -/
def restageHom (X : Object S) {Z : D} (x : Z ⟶ M.family X.arities) :
    FreeBindingClone.Hom (restrictAlgebra X (M.kripke X.arities)) (M.stage Z) where
  raw :=
    { map := fun e => M.restageElem x e
      map_variable := by intro Γ s v; rfl
      map_operation := fun o args => M.restageElem_opElem x X ⟨[]⟩ o args }
  map_substitute := by
    intro Γ Δ s env e
    rfl

/-- Restaging along a map of stages is a map of stage clones. -/
def stageRestage {Z Z' : D} (h : Z' ⟶ Z) : FreeBindingClone.Hom (M.stage Z) (M.stage Z') where
  raw :=
    { map := fun e => M.restageElem h e
      map_variable := by intro Γ s v; rfl
      map_operation := fun o args => M.restageElem_opElem h ⟨[]⟩ ⟨[]⟩ o args }
  map_substitute := by
    intro Γ Δ s env e
    rfl

theorem stageRestage_id (Z : D) :
    M.stageRestage (𝟙 Z) = FreeBindingClone.Hom.id (M.stage Z) := by
  apply FreeBindingClone.Hom.ext
  apply FreeBindingTerms.Hom.ext
  intro Γ s e
  apply ElemOver.ext
  funext W w ρ
  exact congrArg (fun m => (e : M.ElemOver Z Γ s).value W m ρ) (Category.comp_id w)

theorem stageRestage_comp {Z Z' Z'' : D} (h : Z' ⟶ Z) (k : Z'' ⟶ Z') :
    M.stageRestage (k ≫ h) =
      FreeBindingClone.Hom.comp (M.stageRestage h) (M.stageRestage k) := by
  apply FreeBindingClone.Hom.ext
  apply FreeBindingTerms.Hom.ext
  intro Γ s e
  apply ElemOver.ext
  funext W w ρ
  exact congrArg (fun m => (e : M.ElemOver Z Γ s).value W m ρ) (Category.assoc w k h).symm

/-- The function-object point of a restaged family is the restaged point. -/
theorem elemEquiv_restage {C C' : D} (h : C' ⟶ C) {Γ : Ctx S} {s : S.Srt}
    (x : M.ElemOver C Γ s) : M.elemEquiv (M.restageElem h x) = h ≫ M.elemEquiv x := by
  change M.curry (x.value _ (snd _ _ ≫ h) (M.genericEnv Γ C')) =
    h ≫ M.curry (x.value _ (snd _ _) (M.genericEnv Γ C))
  rw [← M.curry_natural, ← x.natural]
  congr 2
  · exact (whiskerLeft_snd _ _).symm
  · funext γ v
    change (fst _ _ ≫ projectVar M.sort v) = (M.ctx Γ ◁ h) ≫ fst _ _ ≫ projectVar M.sort v
    rw [whiskerLeft_fst_assoc]


end Model

end Mettapedia.OSLF.Binding.CategoricalBindingModel
