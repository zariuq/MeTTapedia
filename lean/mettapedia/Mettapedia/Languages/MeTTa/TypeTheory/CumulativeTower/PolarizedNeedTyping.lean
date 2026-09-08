import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedSyntax
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedNeedComputationTyping

/-!
# Independent native-indexed polarized typing

Native mathematical types remain types of the existing presentation. Value
and computation types add thunking, computation functions, and pairs of a
native index with an index-dependent value. These type families depend on
native variables, not on arbitrary computational closures.

The source judgments are independent of execution. A Need declaration may
name any computation type; a runtime realizing this interface must therefore
distinguish returned values from computation-function answers. Native Sigma
sequencing retains the existing native pair, while `sigmaNative` packages a
native index with a general value, including a thunk. No new native conversion
rule, normalization claim, effect permission, or surface profile is selected.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeed

open ScopedComputation (OperationSignature OperationFormation)

mutual
  inductive VTy (Head : Type) : Nat → Type where
    | native {n : Nat} (type : Tm Head n) : VTy Head n
    | thunk {n : Nat} (type : CTy Head n) : VTy Head n
    | sigmaNative {n : Nat} (domain : Tm Head n) (body : VTy Head (n + 1)) : VTy Head n
    deriving DecidableEq, Repr

  inductive CTy (Head : Type) : Nat → Type where
    | returns {n : Nat} (type : VTy Head n) : CTy Head n
    | nativePi {n : Nat} (domain : Tm Head n) (body : CTy Head (n + 1)) : CTy Head n
    | arrow {n : Nat} (domain : VTy Head n) (body : CTy Head n) : CTy Head n
    deriving DecidableEq, Repr
end

variable {Head Operation Effect : Type} {n m p v w k l : Nat}

mutual
  def VTy.rename {n m : Nat} (ρ : Ren n m) : VTy Head n → VTy Head m
    | .native type => .native (Presentation.rename ρ type)
    | .thunk type => .thunk (CTy.rename ρ type)
    | .sigmaNative A B =>
        .sigmaNative (Presentation.rename ρ A) (VTy.rename (liftRen ρ) B)

  def CTy.rename {n m : Nat} (ρ : Ren n m) : CTy Head n → CTy Head m
    | .returns type => .returns (VTy.rename ρ type)
    | .nativePi A B => .nativePi (Presentation.rename ρ A) (CTy.rename (liftRen ρ) B)
    | .arrow A B => .arrow (VTy.rename ρ A) (CTy.rename ρ B)
end

mutual
  def VTy.substitute {n m : Nat} (σ : Sub Head n m) : VTy Head n → VTy Head m
    | .native type => .native (subst σ type)
    | .thunk type => .thunk (CTy.substitute σ type)
    | .sigmaNative A B => .sigmaNative (subst σ A) (VTy.substitute (liftSub σ) B)

  def CTy.substitute {n m : Nat} (σ : Sub Head n m) : CTy Head n → CTy Head m
    | .returns type => .returns (VTy.substitute σ type)
    | .nativePi A B => .nativePi (subst σ A) (CTy.substitute (liftSub σ) B)
    | .arrow A B => .arrow (VTy.substitute σ A) (CTy.substitute σ B)
end

def VTy.instantiate (argument : Tm Head n) (body : VTy Head (n + 1)) : VTy Head n :=
  body.substitute (subst0 argument)

def CTy.instantiate (argument : Tm Head n) (body : CTy Head (n + 1)) : CTy Head n :=
  body.substitute (subst0 argument)

theorem VTy.rename_ext {ρ ξ : Ren n m} (equal : ∀ index, ρ index = ξ index)
    (type : VTy Head n) : type.rename ρ = type.rename ξ := by rw [funext equal]

theorem CTy.rename_ext {ρ ξ : Ren n m} (equal : ∀ index, ρ index = ξ index)
    (type : CTy Head n) : type.rename ρ = type.rename ξ := by rw [funext equal]

theorem VTy.substitute_ext {σ τ : Sub Head n m} (equal : ∀ index, σ index = τ index)
    (type : VTy Head n) : type.substitute σ = type.substitute τ := by rw [funext equal]

theorem CTy.substitute_ext {σ τ : Sub Head n m} (equal : ∀ index, σ index = τ index)
    (type : CTy Head n) : type.substitute σ = type.substitute τ := by rw [funext equal]

mutual
  @[simp] theorem VTy.rename_id {n : Nat} (type : VTy Head n) : type.rename idRen = type := by
    match type with
    | .native type => simp only [VTy.rename, Presentation.rename_id]
    | .thunk type => simp only [VTy.rename, CTy.rename_id type]
    | .sigmaNative A B => simp only [VTy.rename, Presentation.rename_id, liftRen_id, VTy.rename_id B]
  termination_by structural type

  @[simp] theorem CTy.rename_id {n : Nat} (type : CTy Head n) : type.rename idRen = type := by
    match type with
    | .returns type => simp only [CTy.rename, VTy.rename_id type]
    | .nativePi A B => simp only [CTy.rename, Presentation.rename_id, liftRen_id, CTy.rename_id B]
    | .arrow A B => simp only [CTy.rename, VTy.rename_id A, CTy.rename_id B]
  termination_by structural type
end

mutual
  theorem VTy.rename_comp {n m p : Nat} (ρ : Ren m p) (ξ : Ren n m) (type : VTy Head n) :
      (type.rename ξ).rename ρ = type.rename (fun index => ρ (ξ index)) := by
    match type with
    | .native type => simp only [VTy.rename, Presentation.rename_comp]
    | .thunk type => simp only [VTy.rename, CTy.rename_comp ρ ξ type]
    | .sigmaNative A B =>
        simp only [VTy.rename, Presentation.rename_comp, VTy.rename_comp (liftRen ρ) (liftRen ξ) B]
        congr 1
        exact VTy.rename_ext (fun index => liftRen_comp_apply ρ ξ index) B
  termination_by structural type

  theorem CTy.rename_comp {n m p : Nat} (ρ : Ren m p) (ξ : Ren n m) (type : CTy Head n) :
      (type.rename ξ).rename ρ = type.rename (fun index => ρ (ξ index)) := by
    match type with
    | .returns type => simp only [CTy.rename, VTy.rename_comp ρ ξ type]
    | .nativePi A B =>
        simp only [CTy.rename, Presentation.rename_comp, CTy.rename_comp (liftRen ρ) (liftRen ξ) B]
        congr 1
        exact CTy.rename_ext (fun index => liftRen_comp_apply ρ ξ index) B
    | .arrow A B => simp only [CTy.rename, VTy.rename_comp ρ ξ A, CTy.rename_comp ρ ξ B]
  termination_by structural type
end

mutual
  @[simp] theorem VTy.substitute_ids {n : Nat} (type : VTy Head n) : type.substitute ids = type := by
    match type with
    | .native type => simp only [VTy.substitute, subst_ids]
    | .thunk type => simp only [VTy.substitute, CTy.substitute_ids type]
    | .sigmaNative A B => simp only [VTy.substitute, subst_ids, liftSub_ids, VTy.substitute_ids B]
  termination_by structural type

  @[simp] theorem CTy.substitute_ids {n : Nat} (type : CTy Head n) : type.substitute ids = type := by
    match type with
    | .returns type => simp only [CTy.substitute, VTy.substitute_ids type]
    | .nativePi A B => simp only [CTy.substitute, subst_ids, liftSub_ids, CTy.substitute_ids B]
    | .arrow A B => simp only [CTy.substitute, VTy.substitute_ids A, CTy.substitute_ids B]
  termination_by structural type
end

mutual
  @[simp] theorem VTy.substitute_renSub {n m : Nat} (ρ : Ren n m) (type : VTy Head n) :
      type.substitute (renSub ρ) = type.rename ρ := by
    match type with
    | .native type => simp only [VTy.substitute, VTy.rename, subst_renSub]
    | .thunk type => simp only [VTy.substitute, VTy.rename, CTy.substitute_renSub ρ type]
    | .sigmaNative A B => simp only [VTy.substitute, VTy.rename, subst_renSub,
        liftSub_renSub, VTy.substitute_renSub (liftRen ρ) B]
  termination_by structural type

  @[simp] theorem CTy.substitute_renSub {n m : Nat} (ρ : Ren n m) (type : CTy Head n) :
      type.substitute (renSub ρ) = type.rename ρ := by
    match type with
    | .returns type => simp only [CTy.substitute, CTy.rename, VTy.substitute_renSub ρ type]
    | .nativePi A B => simp only [CTy.substitute, CTy.rename, subst_renSub,
        liftSub_renSub, CTy.substitute_renSub (liftRen ρ) B]
    | .arrow A B => simp only [CTy.substitute, CTy.rename,
        VTy.substitute_renSub ρ A, CTy.substitute_renSub ρ B]
  termination_by structural type
end

mutual
  theorem VTy.rename_substitute {n m p : Nat} (ρ : Ren m p) (σ : Sub Head n m) (type : VTy Head n) :
      (type.substitute σ).rename ρ =
        type.substitute (fun index => Presentation.rename ρ (σ index)) := by
    match type with
    | .native type => simp only [VTy.substitute, VTy.rename, rename_subst]
    | .thunk type => simp only [VTy.substitute, VTy.rename, CTy.rename_substitute ρ σ type]
    | .sigmaNative A B =>
        simp only [VTy.substitute, VTy.rename, rename_subst,
          VTy.rename_substitute (liftRen ρ) (liftSub σ) B]
        congr 1
        exact VTy.substitute_ext (fun index => rename_liftSub ρ σ index) B
  termination_by structural type

  theorem CTy.rename_substitute {n m p : Nat} (ρ : Ren m p) (σ : Sub Head n m) (type : CTy Head n) :
      (type.substitute σ).rename ρ =
        type.substitute (fun index => Presentation.rename ρ (σ index)) := by
    match type with
    | .returns type => simp only [CTy.substitute, CTy.rename, VTy.rename_substitute ρ σ type]
    | .nativePi A B =>
        simp only [CTy.substitute, CTy.rename, rename_subst,
          CTy.rename_substitute (liftRen ρ) (liftSub σ) B]
        congr 1
        exact CTy.substitute_ext (fun index => rename_liftSub ρ σ index) B
    | .arrow A B => simp only [CTy.substitute, CTy.rename,
        VTy.rename_substitute ρ σ A, CTy.rename_substitute ρ σ B]
  termination_by structural type
end

mutual
  theorem VTy.substitute_rename {n m p : Nat} (σ : Sub Head m p) (ρ : Ren n m) (type : VTy Head n) :
      (type.rename ρ).substitute σ = type.substitute (fun index => σ (ρ index)) := by
    match type with
    | .native type => simp only [VTy.substitute, VTy.rename, subst_rename]
    | .thunk type => simp only [VTy.substitute, VTy.rename, CTy.substitute_rename σ ρ type]
    | .sigmaNative A B =>
        simp only [VTy.substitute, VTy.rename, subst_rename,
          VTy.substitute_rename (liftSub σ) (liftRen ρ) B]
        congr 1
        exact VTy.substitute_ext (fun index => liftSub_liftRen_apply σ ρ index) B
  termination_by structural type

  theorem CTy.substitute_rename {n m p : Nat} (σ : Sub Head m p) (ρ : Ren n m) (type : CTy Head n) :
      (type.rename ρ).substitute σ = type.substitute (fun index => σ (ρ index)) := by
    match type with
    | .returns type => simp only [CTy.substitute, CTy.rename, VTy.substitute_rename σ ρ type]
    | .nativePi A B =>
        simp only [CTy.substitute, CTy.rename, subst_rename,
          CTy.substitute_rename (liftSub σ) (liftRen ρ) B]
        congr 1
        exact CTy.substitute_ext (fun index => liftSub_liftRen_apply σ ρ index) B
    | .arrow A B => simp only [CTy.substitute, CTy.rename,
        VTy.substitute_rename σ ρ A, CTy.substitute_rename σ ρ B]
  termination_by structural type
end

mutual
  @[simp] theorem VTy.substitute_comp {n m p : Nat} (τ : Sub Head m p) (σ : Sub Head n m) (type : VTy Head n) :
      (type.substitute σ).substitute τ = type.substitute (subComp τ σ) := by
    match type with
    | .native type => simp only [VTy.substitute, subst_subComp]
    | .thunk type => simp only [VTy.substitute, CTy.substitute_comp τ σ type]
    | .sigmaNative A B =>
        simp only [VTy.substitute, subst_subComp, VTy.substitute_comp (liftSub τ) (liftSub σ) B]
        congr 1
        exact VTy.substitute_ext (fun index => liftSub_comp_apply τ σ index) B
  termination_by structural type

  @[simp] theorem CTy.substitute_comp {n m p : Nat} (τ : Sub Head m p) (σ : Sub Head n m) (type : CTy Head n) :
      (type.substitute σ).substitute τ = type.substitute (subComp τ σ) := by
    match type with
    | .returns type => simp only [CTy.substitute, VTy.substitute_comp τ σ type]
    | .nativePi A B =>
        simp only [CTy.substitute, subst_subComp, CTy.substitute_comp (liftSub τ) (liftSub σ) B]
        congr 1
        exact CTy.substitute_ext (fun index => liftSub_comp_apply τ σ index) B
    | .arrow A B => simp only [CTy.substitute, VTy.substitute_comp τ σ A, CTy.substitute_comp τ σ B]
  termination_by structural type
end

theorem VTy.substitute_instantiate (σ : Sub Head n m) (argument : Tm Head n)
    (type : VTy Head (n + 1)) :
    (type.instantiate argument).substitute σ =
      (type.substitute (liftSub σ)).instantiate (subst σ argument) := by
  simp only [VTy.instantiate, VTy.substitute_comp]
  apply VTy.substitute_ext
  intro index
  refine Fin.cases rfl (fun prior => ?_) index
  exact (inst0_rename_wk (subst σ argument) (σ prior)).symm

theorem CTy.substitute_instantiate (σ : Sub Head n m) (argument : Tm Head n)
    (type : CTy Head (n + 1)) :
    (type.instantiate argument).substitute σ =
      (type.substitute (liftSub σ)).instantiate (subst σ argument) := by
  simp only [CTy.instantiate, CTy.substitute_comp]
  apply CTy.substitute_ext
  intro index
  refine Fin.cases rfl (fun prior => ?_) index
  exact (inst0_rename_wk (subst σ argument) (σ prior)).symm

theorem VTy.substitute_weaken (σ : Sub Head n m) (type : VTy Head n) :
    (type.rename wk).substitute (liftSub σ) = (type.substitute σ).rename wk := by
  rw [VTy.substitute_rename, VTy.rename_substitute]
  rfl

theorem CTy.substitute_weaken (σ : Sub Head n m) (type : CTy Head n) :
    (type.rename wk).substitute (liftSub σ) = (type.substitute σ).rename wk := by
  rw [CTy.substitute_rename, CTy.rename_substitute]
  rfl

theorem VTy.instantiate_weaken (argument : Tm Head n) (type : VTy Head n) :
    (type.rename wk).instantiate argument = type := by
  change (type.rename wk).substitute (subst0 argument) = type
  rw [VTy.substitute_rename]
  exact type.substitute_ids

theorem CTy.instantiate_weaken (argument : Tm Head n) (type : CTy Head n) :
    (type.rename wk).instantiate argument = type := by
  change (type.rename wk).substitute (subst0 argument) = type
  rw [CTy.substitute_rename]
  exact type.substitute_ids

/-- Native type formation retains its actual universe witness. -/
def NativeFormation (R : Rules Head) (Γ : Ctx Head n) (A : Tm Head n) : Prop :=
  ∃ u, R.isUniverse u ∧ FormationSensitive.Typing R Γ A (.head u)

mutual
  inductive ValueFormation (R : Rules Head) : {n : Nat} → Ctx Head n → VTy Head n → Prop where
    | native {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} :
        NativeFormation R Γ A → ValueFormation R Γ (.native A)
    | thunk {n : Nat} {Γ : Ctx Head n} {B : CTy Head n} :
        ComputationFormation R Γ B → ValueFormation R Γ (.thunk B)
    | sigmaNative {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : VTy Head (n + 1)} :
        NativeFormation R Γ A → ValueFormation R (.snoc Γ A) B →
        ValueFormation R Γ (.sigmaNative A B)

  inductive ComputationFormation (R : Rules Head) :
      {n : Nat} → Ctx Head n → CTy Head n → Prop where
    | returns {n : Nat} {Γ : Ctx Head n} {A : VTy Head n} :
        ValueFormation R Γ A → ComputationFormation R Γ (.returns A)
    | nativePi {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : CTy Head (n + 1)} :
        NativeFormation R Γ A → ComputationFormation R (.snoc Γ A) B →
        ComputationFormation R Γ (.nativePi A B)
    | arrow {n : Nat} {Γ : Ctx Head n} {A : VTy Head n} {B : CTy Head n} :
        ValueFormation R Γ A → ComputationFormation R Γ B → ComputationFormation R Γ (.arrow A B)
end

variable {R : Rules Head} {Γ : Ctx Head n} {Δ : Ctx Head m}
  {signature : OperationSignature Head Operation}

theorem NativeFormation.substitute {A : Tm Head n} (formed : NativeFormation R Γ A)
    {σ : Sub Head n m} (environment : FormationSensitive.CtxMor R Γ Δ σ) :
    NativeFormation R Δ (subst σ A) := by
  obtain ⟨u, universeWitness, formed⟩ := formed
  exact ⟨u, universeWitness, formed.substitute environment⟩

mutual
  theorem ValueFormation.substitute {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
      {A : VTy Head n} (formed : ValueFormation R Γ A)
      {σ : Sub Head n m} (environment : FormationSensitive.CtxMor R Γ Δ σ) :
      ValueFormation R Δ (A.substitute σ) := by
    cases formed with
    | native formed => exact .native (formed.substitute environment)
    | thunk formed => exact .thunk (formed.substitute environment)
    | sigmaNative formedA formedB =>
        exact .sigmaNative (formedA.substitute environment) (formedB.substitute (environment.lift _))

  theorem ComputationFormation.substitute {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
      {A : CTy Head n} (formed : ComputationFormation R Γ A)
      {σ : Sub Head n m} (environment : FormationSensitive.CtxMor R Γ Δ σ) :
      ComputationFormation R Δ (A.substitute σ) := by
    cases formed with
    | returns formed => exact .returns (formed.substitute environment)
    | nativePi formedA formedB =>
        exact .nativePi (formedA.substitute environment) (formedB.substitute (environment.lift _))
    | arrow formedA formedB => exact .arrow (formedA.substitute environment) (formedB.substitute environment)
end

def weakenValueTypes (types : Fin v → VTy Head n) : Fin v → VTy Head (n + 1) :=
  fun index => (types index).rename wk

def weakenNeedTypes (types : Fin k → CTy Head n) : Fin k → CTy Head (n + 1) :=
  fun index => (types index).rename wk

def extendValueTypes (A : VTy Head n) (types : Fin v → VTy Head n) :
    Fin (v + 1) → VTy Head n := Fin.cases A types

def extendNeedTypes (A : CTy Head n) (types : Fin k → CTy Head n) :
    Fin (k + 1) → CTy Head n := Fin.cases A types

/-- An independently formed native telescope and all declared nonnative slots. -/
structure ContextFormation (R : Rules Head) (Γ : Ctx Head n)
    (valueTypes : Fin v → VTy Head n) (needTypes : Fin k → CTy Head n) : Prop where
  native : FormationSensitive.ContextFormation R Γ
  values : ∀ index, ValueFormation R Γ (valueTypes index)
  needs : ∀ index, ComputationFormation R Γ (needTypes index)

mutual
  /-- Value admission does not execute its native payload or thunk body. -/
  inductive ValueTyping (R : Rules Head) (signature : OperationSignature Head Operation) :
      {n v k : Nat} → Ctx Head n → (Fin v → VTy Head n) → (Fin k → CTy Head n) →
        Value Head Operation Effect n v k → VTy Head n → Prop where
    | native {n v k : Nat} {Γ : Ctx Head n}
        {valueTypes : Fin v → VTy Head n} {needTypes : Fin k → CTy Head n}
        {term A : Tm Head n} :
        FormationSensitive.Typing R Γ term A →
        ValueTyping R signature Γ valueTypes needTypes (.native term) (.native A)
    | variable {n v k : Nat} {Γ : Ctx Head n}
        {valueTypes : Fin v → VTy Head n} {needTypes : Fin k → CTy Head n} (index : Fin v) :
        ValueTyping R signature Γ valueTypes needTypes (.variable index) (valueTypes index)
    | thunk {n v k : Nat} {Γ : Ctx Head n}
        {valueTypes : Fin v → VTy Head n} {needTypes : Fin k → CTy Head n}
        {body : Computation Head Operation Effect n v k} {B : CTy Head n} :
        ComputationTyping R signature Γ valueTypes needTypes body B →
        ValueTyping R signature Γ valueTypes needTypes (.thunk body) (.thunk B)
    | packNative {n v k : Nat} {Γ : Ctx Head n}
        {valueTypes : Fin v → VTy Head n} {needTypes : Fin k → CTy Head n}
        {index A : Tm Head n} {B : VTy Head (n + 1)} {value : Value Head Operation Effect n v k} :
        NativeFormation R Γ A → ValueFormation R (.snoc Γ A) B →
        FormationSensitive.Typing R Γ index A →
        ValueTyping R signature Γ valueTypes needTypes value (B.instantiate index) →
        ValueTyping R signature Γ valueTypes needTypes (.packNative index value) (.sigmaNative A B)
    | nativeConv {n v k : Nat} {Γ : Ctx Head n}
        {valueTypes : Fin v → VTy Head n} {needTypes : Fin k → CTy Head n}
        {value : Value Head Operation Effect n v k} {A B : Tm Head n} :
        ValueTyping R signature Γ valueTypes needTypes value (.native A) →
        NativeFormation R Γ B → Conv R.headEq A B R.computation →
        ValueTyping R signature Γ valueTypes needTypes value (.native B)

  /-- Computation admission retains independent domains, result families, and
  authored native operation formation. Need coordinates may name functions as
  well as returners; a realization must keep those answer forms distinct. -/
  inductive ComputationTyping (R : Rules Head) (signature : OperationSignature Head Operation) :
      {n v k : Nat} → Ctx Head n → (Fin v → VTy Head n) → (Fin k → CTy Head n) →
        Computation Head Operation Effect n v k → CTy Head n → Prop where
    | returnValue {n v k : Nat} {Γ : Ctx Head n}
        {valueTypes : Fin v → VTy Head n} {needTypes : Fin k → CTy Head n}
        {value : Value Head Operation Effect n v k} {A : VTy Head n} :
        ValueTyping R signature Γ valueTypes needTypes value A →
        ComputationTyping R signature Γ valueTypes needTypes (.returnValue value) (.returns A)
    | bindNative {n v k : Nat} {Γ : Ctx Head n}
        {valueTypes : Fin v → VTy Head n} {needTypes : Fin k → CTy Head n}
        {A : Tm Head n} {B : CTy Head n}
        {first : Computation Head Operation Effect n v k}
        {body : Computation Head Operation Effect (n + 1) v k} :
        NativeFormation R Γ A → ComputationFormation R Γ B →
        ComputationTyping R signature Γ valueTypes needTypes first (.returns (.native A)) →
        ComputationTyping R signature (.snoc Γ A) (weakenValueTypes valueTypes)
          (weakenNeedTypes needTypes) body (B.rename wk) →
        ComputationTyping R signature Γ valueTypes needTypes (.bindNative first body) B
    | bindValue {n v k : Nat} {Γ : Ctx Head n}
        {valueTypes : Fin v → VTy Head n} {needTypes : Fin k → CTy Head n}
        {A : VTy Head n} {B : CTy Head n}
        {first : Computation Head Operation Effect n v k}
        {body : Computation Head Operation Effect n (v + 1) k} :
        ValueFormation R Γ A → ComputationFormation R Γ B →
        ComputationTyping R signature Γ valueTypes needTypes first (.returns A) →
        ComputationTyping R signature Γ (extendValueTypes A valueTypes) needTypes body B →
        ComputationTyping R signature Γ valueTypes needTypes (.bindValue first body) B
    | sequenceSigma {n v k : Nat} {Γ : Ctx Head n}
        {valueTypes : Fin v → VTy Head n} {needTypes : Fin k → CTy Head n}
        {A : Tm Head n} {B : Tm Head (n + 1)}
        {first : Computation Head Operation Effect n v k}
        {body : Computation Head Operation Effect (n + 1) v k} :
        NativeFormation R Γ (.sigma A B) →
        ComputationTyping R signature Γ valueTypes needTypes first (.returns (.native A)) →
        ComputationTyping R signature (.snoc Γ A) (weakenValueTypes valueTypes)
          (weakenNeedTypes needTypes) body (.returns (.native B)) →
        ComputationTyping R signature Γ valueTypes needTypes (.sequenceSigma first body)
          (.returns (.native (.sigma A B)))
    | nativeLambda {n v k : Nat} {Γ : Ctx Head n}
        {valueTypes : Fin v → VTy Head n} {needTypes : Fin k → CTy Head n}
        {A : Tm Head n} {B : CTy Head (n + 1)}
        {body : Computation Head Operation Effect (n + 1) v k} :
        NativeFormation R Γ A → ComputationFormation R (.snoc Γ A) B →
        ComputationTyping R signature (.snoc Γ A) (weakenValueTypes valueTypes)
          (weakenNeedTypes needTypes) body B →
        ComputationTyping R signature Γ valueTypes needTypes (.nativeLambda body) (.nativePi A B)
    | nativeApply {n v k : Nat} {Γ : Ctx Head n}
        {valueTypes : Fin v → VTy Head n} {needTypes : Fin k → CTy Head n}
        {A : Tm Head n} {B : CTy Head (n + 1)} {argument : Tm Head n}
        {function : Computation Head Operation Effect n v k} :
        ComputationTyping R signature Γ valueTypes needTypes function (.nativePi A B) →
        FormationSensitive.Typing R Γ argument A →
        ComputationTyping R signature Γ valueTypes needTypes (.nativeApply function argument)
          (B.instantiate argument)
    | valueLambda {n v k : Nat} {Γ : Ctx Head n}
        {valueTypes : Fin v → VTy Head n} {needTypes : Fin k → CTy Head n}
        {A : VTy Head n} {B : CTy Head n}
        {body : Computation Head Operation Effect n (v + 1) k} :
        ValueFormation R Γ A → ComputationFormation R Γ B →
        ComputationTyping R signature Γ (extendValueTypes A valueTypes) needTypes body B →
        ComputationTyping R signature Γ valueTypes needTypes (.valueLambda body) (.arrow A B)
    | valueApply {n v k : Nat} {Γ : Ctx Head n}
        {valueTypes : Fin v → VTy Head n} {needTypes : Fin k → CTy Head n}
        {A : VTy Head n} {B : CTy Head n}
        {argument : Value Head Operation Effect n v k}
        {function : Computation Head Operation Effect n v k} :
        ComputationTyping R signature Γ valueTypes needTypes function (.arrow A B) →
        ValueTyping R signature Γ valueTypes needTypes argument A →
        ComputationTyping R signature Γ valueTypes needTypes (.valueApply function argument) B
    | forceThunk {n v k : Nat} {Γ : Ctx Head n}
        {valueTypes : Fin v → VTy Head n} {needTypes : Fin k → CTy Head n}
        {B : CTy Head n} {value : Value Head Operation Effect n v k} :
        ValueTyping R signature Γ valueTypes needTypes value (.thunk B) →
        ComputationTyping R signature Γ valueTypes needTypes (.forceThunk value) B
    | unpackNative {n v k : Nat} {Γ : Ctx Head n}
        {valueTypes : Fin v → VTy Head n} {needTypes : Fin k → CTy Head n}
        {A : Tm Head n} {B : VTy Head (n + 1)} {C : CTy Head n}
        {value : Value Head Operation Effect n v k}
        {body : Computation Head Operation Effect (n + 1) (v + 1) k} :
        NativeFormation R Γ A → ValueFormation R (.snoc Γ A) B → ComputationFormation R Γ C →
        ValueTyping R signature Γ valueTypes needTypes value (.sigmaNative A B) →
        ComputationTyping R signature (.snoc Γ A)
          (extendValueTypes B (weakenValueTypes valueTypes)) (weakenNeedTypes needTypes)
          body (C.rename wk) →
        ComputationTyping R signature Γ valueTypes needTypes (.unpackNative value body) C
    | choose {n v k : Nat} {Γ : Ctx Head n}
        {valueTypes : Fin v → VTy Head n} {needTypes : Fin k → CTy Head n}
        {A : CTy Head n} {left right : Computation Head Operation Effect n v k} :
        ComputationTyping R signature Γ valueTypes needTypes left A →
        ComputationTyping R signature Γ valueTypes needTypes right A →
        ComputationTyping R signature Γ valueTypes needTypes (.choose left right) A
    | call {n v k : Nat} {Γ : Ctx Head n}
        {valueTypes : Fin v → VTy Head n} {needTypes : Fin k → CTy Head n}
        {operation : Operation} {argument : Tm Head n} :
        OperationFormation R signature operation →
        FormationSensitive.Typing R Γ argument (liftClosed (signature.input operation)) →
        ComputationTyping R signature Γ valueTypes needTypes (.call operation argument)
          (.returns (.native (signature.result operation argument)))
    | emit {n v k : Nat} {Γ : Ctx Head n}
        {valueTypes : Fin v → VTy Head n} {needTypes : Fin k → CTy Head n}
        {effect : Effect} {next : Computation Head Operation Effect n v k} {A : CTy Head n} :
        ComputationTyping R signature Γ valueTypes needTypes next A →
        ComputationTyping R signature Γ valueTypes needTypes (.emit effect next) A
    | letNeed {n v k : Nat} {Γ : Ctx Head n}
        {valueTypes : Fin v → VTy Head n} {needTypes : Fin k → CTy Head n}
        {A B : CTy Head n} {suspended : Computation Head Operation Effect n v k}
        {body : Computation Head Operation Effect n v (k + 1)} :
        ComputationFormation R Γ A → ComputationFormation R Γ B →
        ComputationTyping R signature Γ valueTypes needTypes suspended A →
        ComputationTyping R signature Γ valueTypes (extendNeedTypes A needTypes) body B →
        ComputationTyping R signature Γ valueTypes needTypes (.letNeed suspended body) B
    | forceNeed {n v k : Nat} {Γ : Ctx Head n}
        {valueTypes : Fin v → VTy Head n} {needTypes : Fin k → CTy Head n} (index : Fin k) :
        ComputationTyping R signature Γ valueTypes needTypes (.forceNeed index) (needTypes index)
    | nativeConv {n v k : Nat} {Γ : Ctx Head n}
        {valueTypes : Fin v → VTy Head n} {needTypes : Fin k → CTy Head n}
        {code : Computation Head Operation Effect n v k} {A B : Tm Head n} :
        ComputationTyping R signature Γ valueTypes needTypes code (.returns (.native A)) →
        NativeFormation R Γ B → Conv R.headEq A B R.computation →
        ComputationTyping R signature Γ valueTypes needTypes code (.returns (.native B))
end

/-- The embedding retains arbitrary existing native derivations, including
their selected conversion relation. Extra value slots are unused, not erased
from the syntax of a new first-class program. -/
theorem ComputationTyping.ofScopedNeed {Γ : Ctx Head n}
    {needTypes : Fin k → Tm Head n} {code : ScopedNeedComputation.Code Head Operation Effect n k}
    {A : Tm Head n} (typing : ScopedNeedComputation.Typing R signature Γ needTypes code A) :
    ∀ {v : Nat} (valueTypes : Fin v → VTy Head n),
      ComputationTyping R signature Γ valueTypes (fun index => .returns (.native (needTypes index)))
        (Computation.ofScopedNeed code) (.returns (.native A)) := by
  induction typing with
  | returnValue admitted =>
      intro v valueTypes
      exact .returnValue (.native admitted)
  | sequence formedA universeA formedB universeB _ _ ihFirst ihBody =>
      intro v valueTypes
      exact .bindNative ⟨_, universeA, formedA⟩ (.returns (.native ⟨_, universeB, formedB⟩))
        (ihFirst valueTypes) (ihBody (weakenValueTypes valueTypes))
  | sequenceSigma formed universeWitness _ _ ihFirst ihBody =>
      intro v valueTypes
      exact .sequenceSigma ⟨_, universeWitness, formed⟩ (ihFirst valueTypes)
        (ihBody (weakenValueTypes valueTypes))
  | choose _ _ ihLeft ihRight =>
      intro v valueTypes
      exact .choose (ihLeft valueTypes) (ihRight valueTypes)
  | call declared argument =>
      intro v valueTypes
      exact .call declared argument
  | emit _ ih =>
      intro v valueTypes
      exact .emit (ih valueTypes)
  | letNeed formedA universeA formedB universeB _ _ ihSuspended ihBody =>
      intro v valueTypes
      apply ComputationTyping.letNeed (.returns (.native ⟨_, universeA, formedA⟩))
        (.returns (.native ⟨_, universeB, formedB⟩)) (ihSuspended valueTypes)
      convert ihBody valueTypes using 1
      funext index
      exact Fin.cases rfl (fun _ => rfl) index
  | force index =>
      intro v valueTypes
      exact .forceNeed index
  | conv _ formed universeWitness conversion ih =>
      intro v valueTypes
      exact .nativeConv (ih valueTypes) ⟨_, universeWitness, formed⟩ conversion

private theorem nativeArgumentEnvironment {A argument : Tm Head n}
    (admitted : FormationSensitive.Typing R Γ argument A) :
    FormationSensitive.CtxMor R (.snoc Γ A) Γ (subst0 argument) := by
  intro index
  refine Fin.cases ?_ ?_ index
  · change FormationSensitive.Typing R Γ argument (inst0 argument (rename wk A))
    rw [inst0_rename_wk]
    exact admitted
  · intro prior
    change FormationSensitive.Typing R Γ (.var prior)
      (inst0 argument (rename wk (Ctx.lookup Γ prior)))
    rw [inst0_rename_wk]
    exact .var prior

theorem ValueFormation.instantiate {A argument : Tm Head n} {B : VTy Head (n + 1)}
    (formed : ValueFormation R (.snoc Γ A) B)
    (admitted : FormationSensitive.Typing R Γ argument A) :
    ValueFormation R Γ (B.instantiate argument) :=
  formed.substitute (nativeArgumentEnvironment admitted)

theorem ComputationFormation.instantiate {A argument : Tm Head n} {B : CTy Head (n + 1)}
    (formed : ComputationFormation R (.snoc Γ A) B)
    (admitted : FormationSensitive.Typing R Γ argument A) :
    ComputationFormation R Γ (B.instantiate argument) :=
  formed.substitute (nativeArgumentEnvironment admitted)

theorem operation_result_formed {operation : Operation} {argument : Tm Head n}
    (declared : OperationFormation R signature operation)
    (admitted : FormationSensitive.Typing R Γ argument (liftClosed (signature.input operation))) :
    NativeFormation R Γ (signature.result operation argument) := by
  obtain ⟨u, universeWitness, formed⟩ := declared.output_formed
  refine ⟨u, universeWitness, formed.substitute ?_⟩
  intro index
  refine Fin.cases ?_ (fun prior => Fin.elim0 prior) index
  change FormationSensitive.Typing R Γ argument
    (subst (fun _ => argument) (rename wk (signature.input operation)))
  have emptyRenaming : (wk : Ren 0 1) = Fin.elim0 := by
    funext index
    exact Fin.elim0 index
  rw [emptyRenaming]
  change FormationSensitive.Typing R Γ argument
    (subst (fun _ => argument) (liftClosed (signature.input operation)))
  rw [subst_liftClosed]
  exact admitted

mutual
  /-- Regularity inherits the native universe qualification; no normalization
  or computation-type equality principle is inferred. -/
  theorem ValueTyping.regularity {n v k : Nat} {Γ : Ctx Head n} {valueTypes : Fin v → VTy Head n}
      {needTypes : Fin k → CTy Head n} {value : Value Head Operation Effect n v k}
      {A : VTy Head n} (typing : ValueTyping R signature Γ valueTypes needTypes value A)
      (universes : FormationSensitive.UniverseRegularity R)
      (context : ContextFormation R Γ valueTypes needTypes) :
      ValueFormation R Γ A := by
    match typing with
    | .native admitted => exact .native (admitted.regularity universes context.native)
    | .variable index => exact context.values index
    | .thunk typed => exact .thunk (typed.regularity universes context)
    | .packNative formedA formedB _ _ => exact .sigmaNative formedA formedB
    | .nativeConv _ formed _ => exact .native formed
  termination_by structural typing

  theorem ComputationTyping.regularity {n v k : Nat} {Γ : Ctx Head n} {valueTypes : Fin v → VTy Head n}
      {needTypes : Fin k → CTy Head n} {code : Computation Head Operation Effect n v k}
      {A : CTy Head n} (typing : ComputationTyping R signature Γ valueTypes needTypes code A)
      (universes : FormationSensitive.UniverseRegularity R)
      (context : ContextFormation R Γ valueTypes needTypes) :
      ComputationFormation R Γ A := by
    match typing with
    | .returnValue typed => exact .returns (typed.regularity universes context)
    | .bindNative _ formed _ _ => exact formed
    | .bindValue _ formed _ _ => exact formed
    | .sequenceSigma formed _ _ => exact .returns (.native formed)
    | .nativeLambda formedA formedB _ => exact .nativePi formedA formedB
    | .nativeApply typed admitted =>
        cases typed.regularity universes context with
        | nativePi _ formed => exact formed.instantiate admitted
    | .valueLambda formedA formedB _ => exact .arrow formedA formedB
    | .valueApply typed _ =>
        cases typed.regularity universes context with
        | arrow _ formed => exact formed
    | .forceThunk typed =>
        cases typed.regularity universes context with
        | thunk formed => exact formed
    | .unpackNative _ _ formed _ _ => exact formed
    | .choose typed _ => exact typed.regularity universes context
    | .call declared admitted => exact .returns (.native (operation_result_formed declared admitted))
    | .emit typed => exact typed.regularity universes context
    | .letNeed _ formed _ _ => exact formed
    | .forceNeed index => exact context.needs index
    | .nativeConv _ formed _ => exact .returns (.native formed)
  termination_by structural typing
end

private theorem nativePayloadOfEqual {n v k : Nat} {Γ : Ctx Head n}
    {valueTypes : Fin v → VTy Head n} {needTypes : Fin k → CTy Head n}
    {value : Value Head Operation Effect n v k} {B : VTy Head n}
    (typing : ValueTyping R signature Γ valueTypes needTypes value B) :
    ∀ {term A : Tm Head n}, value = .native term → B = .native A →
      FormationSensitive.Typing R Γ term A := by
  match typing with
  | .native admitted =>
      intro term A shaped type
      cases shaped
      cases type
      exact admitted
  | .variable _ => intro term A shaped; cases shaped
  | .thunk _ => intro term A shaped; cases shaped
  | .packNative _ _ _ _ => intro term A shaped; cases shaped
  | .nativeConv typed formed conversion =>
      intro term A shaped type
      cases type
      obtain ⟨u, universeWitness, formed⟩ := formed
      exact .conv (nativePayloadOfEqual typed shaped rfl) formed universeWitness conversion
termination_by structural typing

/-- A raw native value cannot acquire a native judgment merely by entering
the polarized value carrier. Native conversion tails retain their evidence. -/
theorem ValueTyping.native_payload {valueTypes : Fin v → VTy Head n}
    {needTypes : Fin k → CTy Head n} {term A : Tm Head n}
    (typing : ValueTyping (Effect := Effect) R signature Γ valueTypes needTypes
      (.native term) (.native A)) :
    FormationSensitive.Typing R Γ term A := nativePayloadOfEqual typing rfl rfl

private theorem nativeReturnOfEqual {n v k : Nat} {Γ : Ctx Head n}
    {valueTypes : Fin v → VTy Head n} {needTypes : Fin k → CTy Head n}
    {code : Computation Head Operation Effect n v k} {B : CTy Head n}
    (typing : ComputationTyping R signature Γ valueTypes needTypes code B) :
    ∀ {term A : Tm Head n}, code = .returnValue (.native term) → B = .returns (.native A) →
      FormationSensitive.Typing R Γ term A := by
  match typing with
  | .returnValue admitted =>
      intro term A shaped type
      cases shaped
      cases type
      exact admitted.native_payload
  | .bindNative _ _ _ _ => intro term A shaped; cases shaped
  | .bindValue _ _ _ _ => intro term A shaped; cases shaped
  | .sequenceSigma _ _ _ => intro term A shaped; cases shaped
  | .nativeLambda _ _ _ => intro term A shaped; cases shaped
  | .nativeApply _ _ => intro term A shaped; cases shaped
  | .valueLambda _ _ _ => intro term A shaped; cases shaped
  | .valueApply _ _ => intro term A shaped; cases shaped
  | .forceThunk _ => intro term A shaped; cases shaped
  | .unpackNative _ _ _ _ _ => intro term A shaped; cases shaped
  | .choose _ _ => intro term A shaped; cases shaped
  | .call _ _ => intro term A shaped; cases shaped
  | .emit _ => intro term A shaped; cases shaped
  | .letNeed _ _ _ _ => intro term A shaped; cases shaped
  | .forceNeed _ => intro term A shaped; cases shaped
  | .nativeConv typed formed conversion =>
      intro term A shaped type
      cases type
      obtain ⟨u, universeWitness, formed⟩ := formed
      exact .conv (nativeReturnOfEqual typed shaped rfl) formed universeWitness conversion
termination_by structural typing

theorem ComputationTyping.native_return {valueTypes : Fin v → VTy Head n}
    {needTypes : Fin k → CTy Head n} {term A : Tm Head n}
    (typing : ComputationTyping (Effect := Effect) R signature Γ valueTypes needTypes
      (.returnValue (.native term)) (.returns (.native A))) :
    FormationSensitive.Typing R Γ term A := nativeReturnOfEqual typing rfl rfl

/-- A first-class thunk consumer is available at every formed computation
type, including native-dependent functions rather than only native returners. -/
def forceArgument : Computation Head Operation Effect n v k :=
  .valueLambda (.forceThunk (.variable 0))

theorem forceArgument_typed {valueTypes : Fin v → VTy Head n}
    {needTypes : Fin k → CTy Head n} {B : CTy Head n} (formed : ComputationFormation R Γ B) :
    ComputationTyping (Effect := Effect) R signature Γ valueTypes needTypes
      forceArgument (.arrow (.thunk B) B) :=
  .valueLambda (.thunk formed) formed (.forceThunk (.variable 0))

#print axioms VTy.substitute_comp
#print axioms CTy.substitute_comp
#print axioms VTy.substitute_instantiate
#print axioms CTy.substitute_instantiate
#print axioms ValueFormation.substitute
#print axioms ComputationFormation.substitute
#print axioms ComputationTyping.ofScopedNeed
#print axioms ValueFormation.instantiate
#print axioms ComputationFormation.instantiate
#print axioms ValueTyping.regularity
#print axioms ComputationTyping.regularity
#print axioms ValueTyping.native_payload
#print axioms ComputationTyping.native_return
#print axioms forceArgument_typed

end PolarizedNeed
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
