import Mettapedia.OSLF.Syntax.BindingSignature
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Models of a binding signature in a category with chosen function objects

A model interprets each sort by an object, each context by the product of its
sorts, and each binding arity `Γ ⊢ s` by a chosen function object with its
evaluation and currying. An operator is an arrow out of the product of the
function objects of its arguments. Currying is stated as a universal property,
so the chosen function objects are exponentials.

Any monoidal closed category with chosen finite products carries these function
objects, so every cartesian closed target is admitted. The interpretation of
terms and the classifying functor are constructed separately.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalBindingModel

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

universe u v

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

/-- The product of the sort objects of a context, in order. -/
@[reducible] def contextOf {S : Signature} (sort : S.Srt → D) : Ctx S → D
  | [] => 𝟙_ D
  | γ :: Γ => sort γ ⊗ contextOf sort Γ

@[simp] theorem contextOf_nil {S : Signature} (sort : S.Srt → D) :
    contextOf sort ([] : Ctx S) = 𝟙_ D := rfl

@[simp] theorem contextOf_cons {S : Signature} (sort : S.Srt → D) (γ : S.Srt) (Γ : Ctx S) :
    contextOf sort (γ :: Γ) = sort γ ⊗ contextOf sort Γ := rfl

/-- Projection of a variable out of its context product. -/
def projectVar {S : Signature} (sort : S.Srt → D) :
    ∀ {Γ : Ctx S} {γ : S.Srt}, Var Γ γ → (contextOf sort Γ ⟶ sort γ)
  | _, _, .zero => fst _ _
  | _, _, .succ v => snd _ _ ≫ projectVar sort v

@[simp] theorem projectVar_zero {S : Signature} (sort : S.Srt → D) {Γ : Ctx S} {γ : S.Srt} :
    projectVar sort (Var.zero : Var (γ :: Γ) γ) = fst _ _ := rfl

@[simp] theorem projectVar_succ {S : Signature} (sort : S.Srt → D) {Γ : Ctx S} {γ δ : S.Srt}
    (v : Var Γ γ) : projectVar sort (Var.succ v : Var (δ :: Γ) γ) = snd _ _ ≫ projectVar sort v :=
  rfl

/-- The product of the function objects of a list of arities. -/
@[reducible] def familyOf {S : Signature} (power : Ctx S → S.Srt → D) : List (List S.Srt × S.Srt) → D
  | [] => 𝟙_ D
  | arity :: rest => power arity.1 arity.2 ⊗ familyOf power rest

@[simp] theorem familyOf_nil {S : Signature} (power : Ctx S → S.Srt → D) :
    familyOf power [] = 𝟙_ D := rfl

@[simp] theorem familyOf_cons {S : Signature} (power : Ctx S → S.Srt → D)
    (arity : List S.Srt × S.Srt) (rest : List (List S.Srt × S.Srt)) :
    familyOf power (arity :: rest) = power arity.1 arity.2 ⊗ familyOf power rest := rfl

/-- A model of a binding signature. -/
structure Model (S : Signature) (D : Type u) [Category.{v} D]
    [CartesianMonoidalCategory D] where
  sort : S.Srt → D
  /-- The chosen function object of the arity `Γ ⊢ s`. -/
  power : Ctx S → S.Srt → D
  eval : ∀ (Γ : Ctx S) (s : S.Srt), contextOf sort Γ ⊗ power Γ s ⟶ sort s
  curry : ∀ {Γ : Ctx S} {s : S.Srt} {Z : D}, (contextOf sort Γ ⊗ Z ⟶ sort s) → (Z ⟶ power Γ s)
  curry_eval : ∀ {Γ : Ctx S} {s : S.Srt} {Z : D} (f : contextOf sort Γ ⊗ Z ⟶ sort s),
    (contextOf sort Γ ◁ curry f) ≫ eval Γ s = f
  curry_unique : ∀ {Γ : Ctx S} {s : S.Srt} {Z : D} (f : contextOf sort Γ ⊗ Z ⟶ sort s)
    (g : Z ⟶ power Γ s), (contextOf sort Γ ◁ g) ≫ eval Γ s = f → curry f = g
  op : ∀ {s : S.Srt} (o : S.Op s), familyOf power (S.arity o) ⟶ sort s

namespace Model

variable {S : Signature} (M : Model S D)

/-- The context product of a model. -/
abbrev ctx (Γ : Ctx S) : D := contextOf M.sort Γ

/-- The family product of a model. -/
abbrev family (arities : List (List S.Srt × S.Srt)) : D := familyOf M.power arities

/-- Uncurrying: the arrow a generalized element of a function object names. -/
def uncurry {Γ : Ctx S} {s : S.Srt} {Z : D} (g : Z ⟶ M.power Γ s) :
    M.ctx Γ ⊗ Z ⟶ M.sort s :=
  (M.ctx Γ ◁ g) ≫ M.eval Γ s

theorem curry_uncurry {Γ : Ctx S} {s : S.Srt} {Z : D} (g : Z ⟶ M.power Γ s) :
    M.curry (M.uncurry g) = g :=
  M.curry_unique _ g rfl

theorem uncurry_curry {Γ : Ctx S} {s : S.Srt} {Z : D} (f : M.ctx Γ ⊗ Z ⟶ M.sort s) :
    M.uncurry (M.curry f) = f :=
  M.curry_eval f

/-- Currying is natural in the stage. -/
theorem curry_natural {Γ : Ctx S} {s : S.Srt} {Z Z' : D} (h : Z' ⟶ Z)
    (f : M.ctx Γ ⊗ Z ⟶ M.sort s) :
    M.curry ((M.ctx Γ ◁ h) ≫ f) = h ≫ M.curry f := by
  apply M.curry_unique
  rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, M.curry_eval]

theorem uncurry_natural {Γ : Ctx S} {s : S.Srt} {Z Z' : D} (h : Z' ⟶ Z)
    (g : Z ⟶ M.power Γ s) :
    M.uncurry (h ≫ g) = (M.ctx Γ ◁ h) ≫ M.uncurry g := by
  unfold uncurry
  rw [MonoidalCategory.whiskerLeft_comp, Category.assoc]

/-- Two generalized elements of a function object agree when they evaluate
alike. -/
theorem hom_ext_power {Γ : Ctx S} {s : S.Srt} {Z : D} {g g' : Z ⟶ M.power Γ s}
    (h : M.uncurry g = M.uncurry g') : g = g' := by
  rw [← M.curry_uncurry g, ← M.curry_uncurry g', h]

/-- Projection of a listed arity out of the family product. -/
def familyProj : ∀ (arities : List (List S.Srt × S.Srt)) (i : Fin arities.length),
    M.family arities ⟶ M.power (arities.get i).1 (arities.get i).2
  | _ :: _, ⟨0, _⟩ => fst _ _
  | _ :: rest, ⟨n + 1, bound⟩ => snd _ _ ≫ familyProj rest ⟨n, Nat.lt_of_succ_lt_succ bound⟩

/-- Tupling into the family product. -/
def familyLift {Z : D} : ∀ (arities : List (List S.Srt × S.Srt)),
    ((i : Fin arities.length) → (Z ⟶ M.power (arities.get i).1 (arities.get i).2)) →
      (Z ⟶ M.family arities)
  | [], _ => toUnit Z
  | _ :: rest, components =>
      lift (components ⟨0, Nat.succ_pos _⟩)
        (familyLift rest fun i => components ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

theorem familyLift_proj {Z : D} : ∀ (arities : List (List S.Srt × S.Srt))
    (components : (i : Fin arities.length) → (Z ⟶ M.power (arities.get i).1 (arities.get i).2))
    (i : Fin arities.length),
    M.familyLift arities components ≫ M.familyProj arities i = components i
  | _ :: _, components, ⟨0, _⟩ => lift_fst _ _
  | _ :: rest, components, ⟨n + 1, bound⟩ => by
      change lift _ _ ≫ snd _ _ ≫ M.familyProj rest ⟨n, Nat.lt_of_succ_lt_succ bound⟩ = _
      rw [lift_snd_assoc]
      exact familyLift_proj rest _ ⟨n, Nat.lt_of_succ_lt_succ bound⟩

theorem familyLift_unique {Z : D} : ∀ (arities : List (List S.Srt × S.Srt))
    (components : (i : Fin arities.length) → (Z ⟶ M.power (arities.get i).1 (arities.get i).2))
    (g : Z ⟶ M.family arities),
    (∀ i, g ≫ M.familyProj arities i = components i) → g = M.familyLift arities components
  | [], _, g, _ => toUnit_unique _ _
  | _ :: rest, components, g, agree => by
      show g = lift _ _
      apply hom_ext
      · rw [lift_fst]
        exact agree ⟨0, Nat.succ_pos _⟩
      · rw [lift_snd]
        apply familyLift_unique rest
        intro i
        exact (Category.assoc _ _ _).trans (agree ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

theorem familyLift_comp {Z Z' : D} (h : Z' ⟶ Z) (arities : List (List S.Srt × S.Srt))
    (components : (i : Fin arities.length) → (Z ⟶ M.power (arities.get i).1 (arities.get i).2)) :
    h ≫ M.familyLift arities components = M.familyLift arities fun i => h ≫ components i := by
  apply M.familyLift_unique
  intro i
  rw [Category.assoc, M.familyLift_proj]

theorem familyLift_eta {Z : D} (arities : List (List S.Srt × S.Srt)) (g : Z ⟶ M.family arities) :
    M.familyLift arities (fun i => g ≫ M.familyProj arities i) = g :=
  (M.familyLift_unique arities _ g fun _ => rfl).symm

/-- Environments: a generalized element for each variable of a context. -/
abbrev Env (Z : D) (Γ : Ctx S) : Type v := (γ : S.Srt) → Var Γ γ → (Z ⟶ M.sort γ)

/-- The environment of projections at the context product itself. -/
def projections (Γ : Ctx S) : M.Env (M.ctx Γ) Γ := fun _ v => projectVar M.sort v

/-- Precompose an environment with a change of stage. -/
def restage {Z Z' : D} (h : Z' ⟶ Z) {Γ : Ctx S} (ρ : M.Env Z Γ) : M.Env Z' Γ :=
  fun γ v => h ≫ ρ γ v

/-- Tuple an environment into the context product. -/
def tupleEnv {Z : D} : ∀ {Γ : Ctx S}, M.Env Z Γ → (Z ⟶ M.ctx Γ)
  | [], _ => toUnit Z
  | _ :: _, ρ => lift (ρ _ .zero) (tupleEnv fun γ v => ρ γ (.succ v))

theorem tupleEnv_projectVar {Z : D} : ∀ {Γ : Ctx S} (ρ : M.Env Z Γ) {γ : S.Srt} (v : Var Γ γ),
    M.tupleEnv ρ ≫ projectVar M.sort v = ρ γ v
  | _ :: _, ρ, _, .zero => lift_fst _ _
  | _ :: _, ρ, _, .succ v => by
      change lift _ _ ≫ snd _ _ ≫ projectVar M.sort v = _
      rw [lift_snd_assoc]
      exact tupleEnv_projectVar _ v

theorem tupleEnv_unique {Z : D} : ∀ {Γ : Ctx S} (ρ : M.Env Z Γ) (g : Z ⟶ M.ctx Γ),
    (∀ γ (v : Var Γ γ), g ≫ projectVar M.sort v = ρ γ v) → g = M.tupleEnv ρ
  | [], _, g, _ => toUnit_unique _ _
  | _ :: _, ρ, g, agree => by
      show g = lift _ _
      apply hom_ext
      · rw [lift_fst]
        exact agree _ .zero
      · rw [lift_snd]
        apply tupleEnv_unique
        intro γ v
        exact (Category.assoc _ _ _).trans (agree γ (.succ v))

theorem tupleEnv_projections (Γ : Ctx S) : M.tupleEnv (M.projections Γ) = 𝟙 (M.ctx Γ) :=
  (M.tupleEnv_unique _ _ fun _ _ => Category.id_comp _).symm

theorem tupleEnv_restage {Z Z' : D} (h : Z' ⟶ Z) {Γ : Ctx S} (ρ : M.Env Z Γ) :
    M.tupleEnv (M.restage h ρ) = h ≫ M.tupleEnv ρ := by
  symm
  apply M.tupleEnv_unique
  intro γ v
  rw [Category.assoc, M.tupleEnv_projectVar]
  rfl

/-- Extend an environment beneath a binder list: the new variables are the
projections of the binder context placed in front, the old ones are read
through the second component. -/
def extendEnv {Z : D} : ∀ (binders : List S.Srt) {Γ : Ctx S},
    M.Env Z Γ → M.Env (M.ctx binders ⊗ Z) (binders ++ Γ)
  | [], _, ρ => fun γ v => snd _ _ ≫ ρ γ v
  | _ :: binders, _, ρ => fun γ v =>
      match v with
      | .zero => fst _ _ ≫ fst _ _
      | .succ w => lift (fst _ _ ≫ snd _ _) (snd _ _) ≫ extendEnv binders ρ γ w

/-- The old variables of an extended environment are the restaged originals. -/
theorem extendEnv_old {Z : D} : ∀ (binders : List S.Srt) {Γ : Ctx S} (ρ : M.Env Z Γ)
    {γ : S.Srt} (v : Var Γ γ),
    M.extendEnv binders ρ γ (weakenVar binders v) = snd _ _ ≫ ρ γ v
  | [], _, _, _, _ => rfl
  | _ :: binders, _, ρ, γ, v => by
      change lift (fst _ _ ≫ snd _ _) (snd _ _) ≫ M.extendEnv binders ρ γ (weakenVar binders v) =
        snd _ _ ≫ ρ γ v
      rw [extendEnv_old binders ρ v, lift_snd_assoc]

theorem extendEnv_restage {Z Z' : D} (h : Z' ⟶ Z) : ∀ (binders : List S.Srt) {Γ : Ctx S}
    (ρ : M.Env Z Γ),
    M.extendEnv binders (M.restage h ρ) =
      M.restage (M.ctx binders ◁ h) (M.extendEnv binders ρ)
  | [], _, ρ => by
      funext γ v
      simp only [extendEnv, restage, whiskerLeft_snd_assoc]
  | b :: binders, _, ρ => by
      funext γ v
      cases v with
      | zero => simp [extendEnv, restage]
      | succ w =>
          change lift (fst _ _ ≫ snd _ _) (snd _ _) ≫ M.extendEnv binders (M.restage h ρ) γ w =
            (M.ctx (b :: binders) ◁ h) ≫ lift (fst _ _ ≫ snd _ _) (snd _ _) ≫
              M.extendEnv binders ρ γ w
          rw [extendEnv_restage h binders ρ]
          change lift (fst _ _ ≫ snd _ _) (snd _ _) ≫ (M.ctx binders ◁ h) ≫
              M.extendEnv binders ρ γ w = _
          rw [← Category.assoc, ← Category.assoc]
          congr 1
          apply hom_ext <;> simp

end Model

/-! ## Every monoidal closed target carries the function objects -/

section Closed

variable [MonoidalClosed D]

/-- The model whose function objects are the internal homs of a monoidal closed
category. Operators are supplied separately. -/
def ofClosed {S : Signature} (sort : S.Srt → D)
    (op : ∀ {s : S.Srt} (o : S.Op s),
      familyOf (fun Γ s => (contextOf sort Γ) ⟶[D] sort s) (S.arity o) ⟶ sort s) :
    Model S D where
  sort := sort
  power := fun Γ s => (contextOf sort Γ) ⟶[D] sort s
  eval := fun Γ s => (ihom.ev (contextOf sort Γ)).app (sort s)
  curry := fun f => MonoidalClosed.curry f
  curry_eval := fun f => by
    rw [← MonoidalClosed.uncurry_eq]
    exact MonoidalClosed.uncurry_curry f
  curry_unique := fun f g h => by
    rw [← h, ← MonoidalClosed.uncurry_eq]
    exact MonoidalClosed.curry_uncurry g
  op := op

end Closed

end Mettapedia.OSLF.Binding.CategoricalBindingModel
