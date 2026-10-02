import Mettapedia.OSLF.Syntax.CategoricalBindingUniversal

/-!
# Classification of structure-preserving functors by models

The classifying functor of a model preserves the structure of the
second-order context category, and the model it determines is isomorphic to
the original model. Together with the reconstruction of every preserving
functor from its own model, this classifies structure-preserving functors by
models up to isomorphism. An isomorphism of models induces a natural
isomorphism of their classifying functors.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalBindingModel

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.FreeBindingTerms (FamilyArgs)
open Mettapedia.OSLF.Binding.SecondOrderContext (Object)

universe u v

variable {S : Signature}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

theorem familyOfMap_id (P : Ctx S → S.Srt → D) :
    ∀ L : List (List S.Srt × S.Srt), familyOfMap (fun Γ s => 𝟙 (P Γ s)) L = 𝟙 _
  | [] => rfl
  | a :: L => by
      change 𝟙 _ ⊗ₘ familyOfMap (fun Γ s => 𝟙 (P Γ s)) L = _
      rw [familyOfMap_id P L, id_tensorHom_id]

theorem familyOfMap_comp {P Q R : Ctx S → S.Srt → D} (f : ∀ Γ s, P Γ s ⟶ Q Γ s)
    (g : ∀ Γ s, Q Γ s ⟶ R Γ s) :
    ∀ L : List (List S.Srt × S.Srt),
      familyOfMap (fun Γ s => f Γ s ≫ g Γ s) L = familyOfMap f L ≫ familyOfMap g L
  | [] => (Category.id_comp _).symm
  | a :: L => by
      change (f a.1 a.2 ≫ g a.1 a.2) ⊗ₘ familyOfMap (fun Γ s => f Γ s ≫ g Γ s) L =
        (f a.1 a.2 ⊗ₘ familyOfMap f L) ≫ (g a.1 a.2 ⊗ₘ familyOfMap g L)
      rw [familyOfMap_comp f g L, tensorHom_comp_tensorHom]

theorem foldArgs_eq_map {T : Signature} (A : FreeBindingTerms.Algebra.{u} T) :
    ∀ {arity : List (List T.Srt × T.Srt)} {Γ : Ctx T} (args : Args T arity Γ),
      FreeBindingTerms.foldArgs A args =
        FamilyArgs.map (fun t => FreeBindingTerms.fold A t) (FreeBindingTerms.syntaxToFamily args)
  | _, _, .nil => rfl
  | _, _, .cons _ tail => congrArg (FamilyArgs.cons _) (foldArgs_eq_map A tail)

theorem familyArgs_map_congr {T : Signature} {F G : Ctx T → T.Srt → Type _}
    {f g : {Γ : Ctx T} → {s : T.Srt} → F Γ s → G Γ s}
    (h : ∀ {Γ : Ctx T} {s : T.Srt} (x : F Γ s), f x = g x) :
    ∀ {arity : List (List T.Srt × T.Srt)} {Γ : Ctx T} (args : FamilyArgs T F arity Γ),
      FamilyArgs.map f args = FamilyArgs.map g args
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      change FamilyArgs.cons (f head) (FamilyArgs.map f tail) =
        FamilyArgs.cons (g head) (FamilyArgs.map g tail)
      rw [h head, familyArgs_map_congr h tail]

namespace Model

variable (M : Model S D)

/-! ## The data of the classifying functor -/

/-- The classifying functor with its operator arrows. -/
def classifyingData : PreservingData M.classifyingFunctor where
  toCartesianArities := M.classifyingCartesian
  op := fun {s} o =>
    familyOfMap (fun Γ s => (M.powerIso Γ s).hom) (S.arity o) ≫ M.op o ≫ (M.sortIso s).inv

/-- The model of the classifying functor. -/
abbrev classifyingModel : Model S D := M.classifyingData.toModel

theorem ctxIso_hom_eq : ∀ Γ : Ctx S,
    (M.ctxIso Γ).hom = ctxMap (M := M.classifyingModel) (N := M) (fun γ => (M.sortIso γ).hom) Γ
  | [] => rfl
  | γ :: Γ => by
      change (M.sortIso γ).hom ⊗ₘ (M.ctxIso Γ).hom = (M.sortIso γ).hom ⊗ₘ _
      rw [ctxIso_hom_eq Γ]

theorem ctxMap_sortIso_inv_hom (Γ : Ctx S) :
    ctxMap (M := M) (N := M.classifyingModel) (fun γ => (M.sortIso γ).inv) Γ ≫ (M.ctxIso Γ).hom = 𝟙 _ := by
  rw [ctxIso_hom_eq, ← ctxMap_comp]
  simp only [Iso.inv_hom_id]
  exact ctxMap_id M Γ

theorem tupleEnv_ctxIso {Z : D} : ∀ {Γ : Ctx S} (ρ : M.classifyingModel.Env Z Γ),
    M.classifyingModel.tupleEnv ρ ≫ (M.ctxIso Γ).hom =
      M.tupleEnv (fun γ v => ρ γ v ≫ (M.sortIso γ).hom)
  | [], _ => toUnit_unique _ _
  | γ :: Γ, ρ => by
      change lift _ _ ≫ ((M.sortIso γ).hom ⊗ₘ (M.ctxIso Γ).hom) = lift _ _
      rw [lift_map, tupleEnv_ctxIso (fun γ v => ρ γ (.succ v))]

/-- The image of a context under the classifying functor is its family, arity
by arity. -/
theorem famIso_hom_eq : ∀ L : List (MetaArity S),
    (M.classifyingData.famIso L).hom = familyOfMap (fun Γ s => (M.powerIso Γ s).inv) L
  | [] => toUnit_unique _ _
  | a :: L => by
      change lift (M.classifyingFunctor.map (headArrow a ⟨L⟩))
          (M.classifyingFunctor.map (tailArrow a ⟨L⟩)) ≫
        (M.classifyingFunctor.obj (oneObj a.1 a.2) ◁ (M.classifyingData.famIso L).hom) =
        (M.powerIso a.1 a.2).inv ⊗ₘ familyOfMap (fun Γ s => (M.powerIso Γ s).inv) L
      rw [famIso_hom_eq L]
      change lift (M.assignHom (headArrow a ⟨L⟩)) (M.assignHom (tailArrow a ⟨L⟩)) ≫ _ = _
      rw [assignHom_headArrow, assignHom_tailArrow]
      apply hom_ext
      · rw [Category.assoc, whiskerLeft_fst, lift_fst, tensorHom_fst]
        change _ = fst _ _ ≫ lift (𝟙 _) (toUnit _)
        rw [comp_lift, Category.comp_id]
        congr 1
        exact toUnit_unique _ _
      · rw [Category.assoc, whiskerLeft_snd, lift_snd_assoc, tensorHom_snd]

/-! ## The model of the classifying functor is the model -/

/-- The comparison map to the model of the classifying functor. -/
def toClassifyingHom : M ⟶ M.classifyingModel where
  sort := fun s => (M.sortIso s).inv
  power := fun Γ s => (M.powerIso Γ s).inv
  eval_comm := fun Γ s => by
    change (ctxMap (M := M) (N := M.classifyingModel) (fun γ => (M.sortIso γ).inv) Γ ⊗ₘ
        (M.powerIso Γ s).inv) ≫
      ((M.ctxIso Γ).hom ⊗ₘ (M.powerIso Γ s).hom) ≫ M.eval Γ s ≫ (M.sortIso s).inv = _
    rw [tensorHom_comp_tensorHom_assoc, ctxMap_sortIso_inv_hom, Iso.inv_hom_id, id_tensorHom_id,
      Category.id_comp]
  op_comm := fun o => by
    change familyMap (M := M) (N := M.classifyingModel) (fun Γ s => (M.powerIso Γ s).inv)
        (S.arity o) ≫
      familyOfMap (fun Γ s => (M.powerIso Γ s).hom) (S.arity o) ≫ M.op o ≫ (M.sortIso _).inv = _
    rw [familyMap_eq, ← Category.assoc, ← familyOfMap_comp]
    simp only [Iso.inv_hom_id]
    rw [familyOfMap_id, Category.id_comp]

/-- The comparison map back from the model of the classifying functor. -/
def fromClassifyingHom : M.classifyingModel ⟶ M where
  sort := fun s => (M.sortIso s).hom
  power := fun Γ s => (M.powerIso Γ s).hom
  eval_comm := fun Γ s => by
    change (ctxMap (M := M.classifyingModel) (N := M) (fun γ => (M.sortIso γ).hom) Γ ⊗ₘ
        (M.powerIso Γ s).hom) ≫ M.eval Γ s =
      (((M.ctxIso Γ).hom ⊗ₘ (M.powerIso Γ s).hom) ≫ M.eval Γ s ≫ (M.sortIso s).inv) ≫
        (M.sortIso s).hom
    rw [ctxIso_hom_eq]
    simp
  op_comm := fun o => by
    change familyMap (M := M.classifyingModel) (N := M) (fun Γ s => (M.powerIso Γ s).hom)
        (S.arity o) ≫ M.op o =
      (familyOfMap (fun Γ s => (M.powerIso Γ s).hom) (S.arity o) ≫ M.op o ≫ (M.sortIso _).inv) ≫
        (M.sortIso _).hom
    rw [familyMap_eq]
    simp

/-- **A model is recovered from its classifying functor.** -/
def classifyingModelIso : M ≅ M.classifyingModel where
  hom := M.toClassifyingHom
  inv := M.fromClassifyingHom
  hom_inv_id := by
    apply Hom.ext <;> funext <;> simp [toClassifyingHom, fromClassifyingHom]
  inv_hom_id := by
    apply Hom.ext <;> funext <;> simp [toClassifyingHom, fromClassifyingHom]

/-! ## The classifying functor preserves the structure -/

/-- The meaning of a term under the classifying functor is its transported
interpretation. -/
theorem classifying_meaning {X : Object S} {Γ : Ctx S} {s : S.Srt}
    (t : Term (withMetas S X.arities) Γ s) :
    M.classifyingData.meaning t = transElem M.classifyingModelIso (M.interp X.arities t) := by
  apply ElemOver.ext
  funext Z m ρ
  change lift (M.classifyingModel.tupleEnv ρ)
      (m ≫ (M.classifyingData.famIso X.arities).inv ≫ M.assignHom (termArrow t)) ≫
      (((M.ctxIso Γ).hom ⊗ₘ (M.powerIso Γ s).hom) ≫ M.eval Γ s ≫ (M.sortIso s).inv) =
    (M.interp X.arities t).value Z (m ≫ familyMap (fun Γ s => (M.powerIso Γ s).hom) X.arities)
      (fun γ v => ρ γ v ≫ (M.sortIso γ).hom) ≫ (M.sortIso s).inv
  have famInv : (M.classifyingData.famIso X.arities).inv =
      familyOfMap (fun Γ s => (M.powerIso Γ s).hom) X.arities := by
    symm
    rw [← Iso.hom_comp_eq_id, famIso_hom_eq, ← familyOfMap_comp]
    simp only [Iso.inv_hom_id]
    exact familyOfMap_id _ _
  rw [famInv, lift_map_assoc, tupleEnv_ctxIso, assignHom_termArrow, familyMap_eq,
    M.value_eq_generic]
  change lift _ ((m ≫ _ ≫ lift (M.curry (M.generic X.arities t)) (toUnit _)) ≫ fst _ _) ≫ _ = _
  rw [Category.assoc, Category.assoc, lift_fst]
  have split : lift (M.tupleEnv (fun γ v => ρ γ v ≫ (M.sortIso γ).hom))
      (m ≫ familyOfMap (fun Γ s => (M.powerIso Γ s).hom) X.arities ≫ M.curry (M.generic X.arities t)) =
      lift (M.tupleEnv (fun γ v => ρ γ v ≫ (M.sortIso γ).hom))
        (m ≫ familyOfMap (fun Γ s => (M.powerIso Γ s).hom) X.arities) ≫
        (M.ctx Γ ◁ M.curry (M.generic X.arities t)) := by
    rw [lift_whiskerLeft, Category.assoc]
  rw [split, Category.assoc, ← Category.assoc (M.ctx Γ ◁ _), M.curry_eval, Category.assoc]
  rfl

theorem classifying_meaning_eq_interp {X : Object S} {Γ : Ctx S} {s : S.Srt}
    (t : Term (withMetas S X.arities) Γ s) :
    M.classifyingData.meaning t = M.classifyingModel.interp X.arities t := by
  rw [classifying_meaning, interp_transport]

/-- **The classifying functor of a model preserves the structure.** -/
def classifyingPreserving : Preserving M.classifyingFunctor where
  toPreservingData := M.classifyingData
  meaning_var := fun X Γ γ v => by
    rw [classifying_meaning_eq_interp]
    rfl
  meaning_op := fun X Γ s o args => by
    rw [classifying_meaning_eq_interp]
    change M.classifyingModel.opElem o
      (FreeBindingTerms.foldArgs (M.classifyingModel.kripke X.arities).toRaw args) = _
    rw [foldArgs_eq_map]
    congr 1
    exact familyArgs_map_congr (fun t => (M.classifying_meaning_eq_interp t).symm) _
  meaning_meta := fun X Γ j args => by
    rw [classifying_meaning_eq_interp]
    change M.classifyingModel.metaElem j
      (FreeBindingTerms.foldArgs (M.classifyingModel.kripke X.arities).toRaw args) = _
    rw [foldArgs_eq_map]
    congr 1
    exact familyArgs_map_congr (fun t => (M.classifying_meaning_eq_interp t).symm) _

end Model

end Mettapedia.OSLF.Binding.CategoricalBindingModel
