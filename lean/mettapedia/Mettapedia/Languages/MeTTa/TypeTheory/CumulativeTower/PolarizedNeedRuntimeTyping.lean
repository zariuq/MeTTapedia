import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedMachine
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedTypedSubstitution

/-!
# Source-backed typing of first-class lexical runtime values

Captured computations retain their actual source derivation and lexical
environments. Native replacements are refined context morphisms; captured
values are recursively admitted; Need references preserve complete cell
identities and declared computation types. Functions retain unopened source
bodies, not a semantic assumption about all future arguments. Consequently
store extension transports their typing before new arguments are supplied.

These are value, closure and opening invariants for the actual candidate
machine. Fault and whole-control preservation belong to subsequent modules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeedMachine

open PrimeNeedReference
open PolarizedNeed
open ScopedComputation (OperationSignature)

variable {Head Operation Effect : Type} {n m v k : Nat}
  {R : Rules Head} {signature : OperationSignature Head Operation} {Δ : Ctx Head m}

abbrev CellTypes (Head : Type) (m : Nat) := CellId → Option (CTy Head m)

def StoreExtends (before after : CellTypes Head m) : Prop :=
  ∀ cell A, before cell = some A → after cell = some A

theorem StoreExtends.refl (types : CellTypes Head m) : StoreExtends types types := fun _ _ h => h

theorem StoreExtends.trans {first middle last : CellTypes Head m}
    (earlier : StoreExtends first middle) (later : StoreExtends middle last) :
    StoreExtends first last := fun cell A known => later cell A (earlier cell A known)

/-- Runtime value admission is independent of execution and cache lookup. -/
inductive RuntimeValueTyping (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m) (types : CellTypes Head m) :
    RuntimeValue Head Operation Effect m → VTy Head m → Prop where
  | native {term A : Tm Head m} : FormationSensitive.Typing R Δ term A →
      RuntimeValueTyping R signature Δ types (.native term) (.native A)
  | thunk {n v k : Nat} {Γ : Ctx Head n} {sv : Fin v → VTy Head n} {sn : Fin k → CTy Head n}
      {code : Computation Head Operation Effect n v k} {B : CTy Head n}
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m}
      {needs : Fin k → CellId} :
      ComputationTyping R signature Γ sv sn code B →
      FormationSensitive.CtxMor R Γ Δ native →
      (∀ i, RuntimeValueTyping R signature Δ types (values i) ((sv i).substitute native)) →
      (∀ i, types (needs i) = some ((sn i).substitute native)) →
      RuntimeValueTyping R signature Δ types (.thunk code native values needs) (.thunk (B.substitute native))
  | packNative {index A : Tm Head m} {B : VTy Head (m + 1)}
      {value : RuntimeValue Head Operation Effect m} :
      NativeFormation R Δ A → ValueFormation R (.snoc Δ A) B →
      FormationSensitive.Typing R Δ index A →
      RuntimeValueTyping R signature Δ types value (B.instantiate index) →
      RuntimeValueTyping R signature Δ types (.packNative index value) (.sigmaNative A B)
  | nativeConv {value : RuntimeValue Head Operation Effect m} {A B : Tm Head m} :
      RuntimeValueTyping R signature Δ types value (.native A) →
      NativeFormation R Δ B → Conv R.headEq A B R.computation →
      RuntimeValueTyping R signature Δ types value (.native B)

/-- Every coordinate is checked against its independently declared source type. -/
structure EnvironmentTyping (R : Rules Head) (signature : OperationSignature Head Operation)
    (Γ : Ctx Head n) (sv : Fin v → VTy Head n) (sn : Fin k → CTy Head n)
    (Δ : Ctx Head m) (types : CellTypes Head m) (nativeValues : Sub Head n m)
    (capturedValues : Fin v → RuntimeValue Head Operation Effect m) (capturedNeeds : Fin k → CellId) : Prop where
  native : FormationSensitive.CtxMor R Γ Δ nativeValues
  values : ∀ i, RuntimeValueTyping R signature Δ types (capturedValues i) ((sv i).substitute nativeValues)
  needs : ∀ i, types (capturedNeeds i) = some ((sn i).substitute nativeValues)

inductive ClosureTyping (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m) (types : CellTypes Head m) :
    Closure Head Operation Effect m → CTy Head m → Prop where
  | captured {n v k : Nat} {Γ : Ctx Head n} {sv : Fin v → VTy Head n} {sn : Fin k → CTy Head n}
      {code : Computation Head Operation Effect n v k} {B : CTy Head n}
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m}
      {needs : Fin k → CellId} :
      ComputationTyping R signature Γ sv sn code B →
      EnvironmentTyping R signature Γ sv sn Δ types native values needs →
      ClosureTyping R signature Δ types ⟨n, v, k, code, native, values, needs⟩ (B.substitute native)
  | nativeConv {closure : Closure Head Operation Effect m} {A B : Tm Head m} :
      ClosureTyping R signature Δ types closure (.returns (.native A)) →
      NativeFormation R Δ B → Conv R.headEq A B R.computation →
      ClosureTyping R signature Δ types closure (.returns (.native B))

inductive NativeBodyTyping (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m) (types : CellTypes Head m) :
    NativeBody Head Operation Effect m → Tm Head m → CTy Head (m + 1) → Prop where
  | captured {n v k : Nat} {Γ : Ctx Head n} {sv : Fin v → VTy Head n} {sn : Fin k → CTy Head n}
      {code : Computation Head Operation Effect (n + 1) v k} {A : Tm Head n} {B : CTy Head (n + 1)}
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m}
      {needs : Fin k → CellId} :
      ComputationTyping R signature (.snoc Γ A) (weakenValueTypes sv) (weakenNeedTypes sn) code B →
      EnvironmentTyping R signature Γ sv sn Δ types native values needs →
      NativeBodyTyping R signature Δ types ⟨n, v, k, code, native, values, needs⟩
        (subst native A) (B.substitute (liftSub native))

inductive ValueBodyTyping (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m) (types : CellTypes Head m) :
    ValueBody Head Operation Effect m → VTy Head m → CTy Head m → Prop where
  | captured {n v k : Nat} {Γ : Ctx Head n} {sv : Fin v → VTy Head n} {sn : Fin k → CTy Head n}
      {code : Computation Head Operation Effect n (v + 1) k} {A : VTy Head n} {B : CTy Head n}
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m}
      {needs : Fin k → CellId} :
      ComputationTyping R signature Γ (extendValueTypes A sv) sn code B →
      EnvironmentTyping R signature Γ sv sn Δ types native values needs →
      ValueBodyTyping R signature Δ types ⟨n, v, k, code, native, values, needs⟩
        (A.substitute native) (B.substitute native)

inductive NeedBodyTyping (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m) (types : CellTypes Head m) :
    NeedBody Head Operation Effect m → CTy Head m → CTy Head m → Prop where
  | captured {n v k : Nat} {Γ : Ctx Head n} {sv : Fin v → VTy Head n} {sn : Fin k → CTy Head n}
      {code : Computation Head Operation Effect n v (k + 1)} {A B : CTy Head n}
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m}
      {needs : Fin k → CellId} :
      ComputationTyping R signature Γ sv (extendNeedTypes A sn) code B →
      EnvironmentTyping R signature Γ sv sn Δ types native values needs →
      NeedBodyTyping R signature Δ types ⟨n, v, k, code, native, values, needs⟩
        (A.substitute native) (B.substitute native)

inductive PairBodyTyping (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m) (types : CellTypes Head m) :
    PairBody Head Operation Effect m → Tm Head m → VTy Head (m + 1) → CTy Head m → Prop where
  | captured {n v k : Nat} {Γ : Ctx Head n} {sv : Fin v → VTy Head n} {sn : Fin k → CTy Head n}
      {code : Computation Head Operation Effect (n + 1) (v + 1) k}
      {A : Tm Head n} {B : VTy Head (n + 1)} {C : CTy Head n}
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m}
      {needs : Fin k → CellId} :
      ComputationTyping R signature (.snoc Γ A)
        (extendValueTypes B (weakenValueTypes sv)) (weakenNeedTypes sn) code (C.rename wk) →
      EnvironmentTyping R signature Γ sv sn Δ types native values needs →
      PairBodyTyping R signature Δ types ⟨n, v, k, code, native, values, needs⟩
        (subst native A) (B.substitute (liftSub native)) (C.substitute native)

inductive AnswerTyping (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m) (types : CellTypes Head m) :
    Answer Head Operation Effect m → CTy Head m → Prop where
  | returned {value : RuntimeValue Head Operation Effect m} {A : VTy Head m} :
      RuntimeValueTyping R signature Δ types value A →
      AnswerTyping R signature Δ types (.returned value) (.returns A)
  | nativeFunction {body : NativeBody Head Operation Effect m} {A : Tm Head m} {B : CTy Head (m + 1)} :
      NativeFormation R Δ A → ComputationFormation R (.snoc Δ A) B →
      NativeBodyTyping R signature Δ types body A B →
      AnswerTyping R signature Δ types (.nativeFunction body) (.nativePi A B)
  | valueFunction {body : ValueBody Head Operation Effect m} {A : VTy Head m} {B : CTy Head m} :
      ValueFormation R Δ A → ComputationFormation R Δ B →
      ValueBodyTyping R signature Δ types body A B →
      AnswerTyping R signature Δ types (.valueFunction body) (.arrow A B)

theorem RuntimeValueTyping.extend {before after : CellTypes Head m}
    {value : RuntimeValue Head Operation Effect m} {A : VTy Head m}
    (typed : RuntimeValueTyping R signature Δ before value A) (extension : StoreExtends before after) :
    RuntimeValueTyping R signature Δ after value A := by
  match typed with
  | .native admitted => exact .native admitted
  | .thunk source envNative values needs =>
      exact .thunk source envNative (fun i => RuntimeValueTyping.extend (values i) extension)
        (fun i => extension _ _ (needs i))
  | .packNative formedA formedB index payload =>
      exact .packNative formedA formedB index (RuntimeValueTyping.extend payload extension)
  | .nativeConv prior formed conversion =>
      exact .nativeConv (RuntimeValueTyping.extend prior extension) formed conversion
termination_by structural typed

theorem EnvironmentTyping.extend {Γ : Ctx Head n} {sv : Fin v → VTy Head n} {sn : Fin k → CTy Head n}
    {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
    {before after : CellTypes Head m}
    (typed : EnvironmentTyping R signature Γ sv sn Δ before native values needs)
    (extension : StoreExtends before after) :
    EnvironmentTyping R signature Γ sv sn Δ after native values needs where
  native := typed.native
  values i := (typed.values i).extend extension
  needs i := extension _ _ (typed.needs i)

theorem ClosureTyping.extend {before after : CellTypes Head m}
    {closure : Closure Head Operation Effect m} {B : CTy Head m}
    (typed : ClosureTyping R signature Δ before closure B) (extension : StoreExtends before after) :
    ClosureTyping R signature Δ after closure B := by
  match typed with
  | .captured source environment => exact .captured source (environment.extend extension)
  | .nativeConv prior formed conversion =>
      exact .nativeConv (ClosureTyping.extend prior extension) formed conversion
termination_by structural typed

theorem NativeBodyTyping.extend {before after : CellTypes Head m}
    {body : NativeBody Head Operation Effect m} {A : Tm Head m} {B : CTy Head (m + 1)}
    (typed : NativeBodyTyping R signature Δ before body A B) (extension : StoreExtends before after) :
    NativeBodyTyping R signature Δ after body A B := by
  cases typed with
  | captured source environment => exact .captured source (environment.extend extension)

theorem ValueBodyTyping.extend {before after : CellTypes Head m}
    {body : ValueBody Head Operation Effect m} {A : VTy Head m} {B : CTy Head m}
    (typed : ValueBodyTyping R signature Δ before body A B) (extension : StoreExtends before after) :
    ValueBodyTyping R signature Δ after body A B := by
  cases typed with
  | captured source environment => exact .captured source (environment.extend extension)

theorem NeedBodyTyping.extend {before after : CellTypes Head m}
    {body : NeedBody Head Operation Effect m} {A B : CTy Head m}
    (typed : NeedBodyTyping R signature Δ before body A B) (extension : StoreExtends before after) :
    NeedBodyTyping R signature Δ after body A B := by
  cases typed with
  | captured source environment => exact .captured source (environment.extend extension)

theorem PairBodyTyping.extend {before after : CellTypes Head m}
    {body : PairBody Head Operation Effect m} {A : Tm Head m} {B : VTy Head (m + 1)} {C : CTy Head m}
    (typed : PairBodyTyping R signature Δ before body A B C) (extension : StoreExtends before after) :
    PairBodyTyping R signature Δ after body A B C := by
  cases typed with
  | captured source environment => exact .captured source (environment.extend extension)

theorem AnswerTyping.extend {before after : CellTypes Head m}
    {answer : Answer Head Operation Effect m} {B : CTy Head m}
    (typed : AnswerTyping R signature Δ before answer B) (extension : StoreExtends before after) :
    AnswerTyping R signature Δ after answer B := by
  cases typed with
  | returned value => exact .returned (value.extend extension)
  | nativeFunction formedA formedB body => exact .nativeFunction formedA formedB (body.extend extension)
  | valueFunction formedA formedB body => exact .valueFunction formedA formedB (body.extend extension)

theorem AnswerTyping.convertNative {types : CellTypes Head m}
    {answer : Answer Head Operation Effect m} {A B : Tm Head m}
    (typed : AnswerTyping R signature Δ types answer (.returns (.native A)))
    (formed : NativeFormation R Δ B) (conversion : Conv R.headEq A B R.computation) :
    AnswerTyping R signature Δ types answer (.returns (.native B)) := by
  cases typed with
  | returned value => exact .returned (.nativeConv value formed conversion)

/-- Capturing source values preserves typing in the actual lexical environment. -/
theorem captureValue_typed {Γ : Ctx Head n} {sv : Fin v → VTy Head n} {sn : Fin k → CTy Head n}
    {source : Value Head Operation Effect n v k} {A : VTy Head n}
    (typed : ValueTyping R signature Γ sv sn source A)
    {types : CellTypes Head m} {native : Sub Head n m}
    {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
    (environment : EnvironmentTyping R signature Γ sv sn Δ types native values needs) :
    RuntimeValueTyping R signature Δ types (captureValue native values needs source) (A.substitute native) := by
  match typed with
  | .native admitted => exact .native (admitted.substitute environment.native)
  | .variable i => exact environment.values i
  | .thunk source => exact .thunk source environment.native environment.values environment.needs
  | .packNative formedA formedB index payload =>
      exact .packNative (formedA.substitute environment.native)
        (formedB.substitute (environment.native.lift _)) (index.substitute environment.native)
        (by simpa only [VTy.substitute_instantiate] using captureValue_typed payload environment)
  | .nativeConv prior formed conversion =>
      exact .nativeConv (captureValue_typed prior environment)
        (formed.substitute environment.native) (conversion.substitute native)
termination_by structural typed

theorem value_substitute_consSub (argument : Tm Head m) (native : Sub Head n m)
    (B : VTy Head (n + 1)) :
    B.substitute (consSub argument native) = (B.substitute (liftSub native)).instantiate argument := by
  simp only [VTy.instantiate, VTy.substitute_comp]
  apply VTy.substitute_ext
  intro i
  refine Fin.cases rfl (fun j => ?_) i
  exact (inst0_rename_wk argument (native j)).symm

theorem computation_substitute_consSub (argument : Tm Head m) (native : Sub Head n m)
    (B : CTy Head (n + 1)) :
    B.substitute (consSub argument native) = (B.substitute (liftSub native)).instantiate argument := by
  simp only [CTy.instantiate, CTy.substitute_comp]
  apply CTy.substitute_ext
  intro i
  refine Fin.cases rfl (fun j => ?_) i
  exact (inst0_rename_wk argument (native j)).symm

theorem value_substitute_consSub_weaken (argument : Tm Head m) (native : Sub Head n m) (B : VTy Head n) :
    (B.rename wk).substitute (consSub argument native) = B.substitute native := by
  rw [VTy.substitute_rename]
  rfl

theorem computation_substitute_consSub_weaken (argument : Tm Head m) (native : Sub Head n m) (B : CTy Head n) :
    (B.rename wk).substitute (consSub argument native) = B.substitute native := by
  rw [CTy.substitute_rename]
  rfl

namespace EnvironmentTyping

variable {Γ : Ctx Head n} {sv : Fin v → VTy Head n} {sn : Fin k → CTy Head n}
  {types : CellTypes Head m} {native : Sub Head n m}
  {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}

theorem extendNative (environment : EnvironmentTyping R signature Γ sv sn Δ types native values needs)
    {A : Tm Head n} {argument : Tm Head m}
    (admitted : FormationSensitive.Typing R Δ argument (subst native A)) :
    EnvironmentTyping R signature (.snoc Γ A) (weakenValueTypes sv) (weakenNeedTypes sn)
      Δ types (consSub argument native) values needs where
  native := ScopedComputation.extendEnvironment environment.native admitted
  values i := by
    simpa only [weakenValueTypes, value_substitute_consSub_weaken] using environment.values i
  needs i := by
    simpa only [weakenNeedTypes, computation_substitute_consSub_weaken] using environment.needs i

theorem extendValue (environment : EnvironmentTyping R signature Γ sv sn Δ types native values needs)
    {A : VTy Head n} {value : RuntimeValue Head Operation Effect m}
    (admitted : RuntimeValueTyping R signature Δ types value (A.substitute native)) :
    EnvironmentTyping R signature Γ (extendValueTypes A sv) sn
      Δ types native (Fin.cases value values) needs where
  native := environment.native
  values i := Fin.cases admitted (fun j => environment.values j) i
  needs := environment.needs

theorem extendNeed (environment : EnvironmentTyping R signature Γ sv sn Δ types native values needs)
    {A : CTy Head n} {cell : CellId} (allocated : types cell = some (A.substitute native)) :
    EnvironmentTyping R signature Γ sv (extendNeedTypes A sn)
      Δ types native values (Fin.cases cell needs) where
  native := environment.native
  values := environment.values
  needs i := Fin.cases allocated (fun j => environment.needs j) i

end EnvironmentTyping

private theorem native_consSub_eq (argument : Tm Head m) (native : Sub Head n m) :
    consSub argument native = Fin.cases argument native := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem NativeBodyTyping.open {types : CellTypes Head m}
    {body : NativeBody Head Operation Effect m} {A : Tm Head m} {B : CTy Head (m + 1)}
    (typed : NativeBodyTyping R signature Δ types body A B) {argument : Tm Head m}
    (admitted : FormationSensitive.Typing R Δ argument A) :
    ClosureTyping R signature Δ types (body.open argument) (B.instantiate argument) := by
  cases typed with
  | captured source environment =>
      have opened := ClosureTyping.captured source (environment.extendNative admitted)
      rw [computation_substitute_consSub] at opened
      simpa only [NativeBody.open, native_consSub_eq] using opened

theorem ValueBodyTyping.open {types : CellTypes Head m}
    {body : ValueBody Head Operation Effect m} {A : VTy Head m} {B : CTy Head m}
    (typed : ValueBodyTyping R signature Δ types body A B) {argument : RuntimeValue Head Operation Effect m}
    (admitted : RuntimeValueTyping R signature Δ types argument A) :
    ClosureTyping R signature Δ types (body.open argument) B := by
  cases typed with
  | captured source environment => exact .captured source (environment.extendValue admitted)

theorem NeedBodyTyping.open {types : CellTypes Head m}
    {body : NeedBody Head Operation Effect m} {A B : CTy Head m}
    (typed : NeedBodyTyping R signature Δ types body A B) {cell : CellId}
    (allocated : types cell = some A) :
    ClosureTyping R signature Δ types (body.open cell) B := by
  cases typed with
  | captured source environment => exact .captured source (environment.extendNeed allocated)

theorem PairBodyTyping.open {types : CellTypes Head m}
    {body : PairBody Head Operation Effect m} {A : Tm Head m} {B : VTy Head (m + 1)} {C : CTy Head m}
    (typed : PairBodyTyping R signature Δ types body A B C) {index : Tm Head m}
    {value : RuntimeValue Head Operation Effect m}
    (indexTyped : FormationSensitive.Typing R Δ index A)
    (valueTyped : RuntimeValueTyping R signature Δ types value (B.instantiate index)) :
    ClosureTyping R signature Δ types (body.open index value) C := by
  cases typed with
  | captured source environment =>
      have opened := (environment.extendNative indexTyped).extendValue
        (by simpa only [value_substitute_consSub] using valueTyped)
      have result := ClosureTyping.captured source opened
      rw [computation_substitute_consSub_weaken] at result
      simpa only [PairBody.open, native_consSub_eq] using result

/-- The observable runtime constructor licensed by each value type. -/
def RuntimeValueCanonical (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m) (types : CellTypes Head m) (value : RuntimeValue Head Operation Effect m) :
    VTy Head m → Prop
  | .native A => ∃ term, value = .native term ∧ FormationSensitive.Typing R Δ term A
  | .thunk B => ∃ (n v k : Nat) (code : Computation Head Operation Effect n v k)
      (native : Sub Head n m) (values : Fin v → RuntimeValue Head Operation Effect m) (needs : Fin k → CellId),
      value = .thunk code native values needs ∧
        ClosureTyping R signature Δ types ⟨n, v, k, code, native, values, needs⟩ B
  | .sigmaNative A B => ∃ index payload, value = .packNative index payload ∧
      FormationSensitive.Typing R Δ index A ∧
      RuntimeValueTyping R signature Δ types payload (B.instantiate index)

theorem RuntimeValueTyping.canonical {types : CellTypes Head m}
    {value : RuntimeValue Head Operation Effect m} {A : VTy Head m}
    (typed : RuntimeValueTyping R signature Δ types value A) :
    RuntimeValueCanonical R signature Δ types value A := by
  match typed with
  | .native admitted => exact ⟨_, rfl, admitted⟩
  | .thunk source envNative values needs =>
      exact ⟨_, _, _, _, _, _, _, rfl, .captured source ⟨envNative, values, needs⟩⟩
  | .packNative _ _ index payload => exact ⟨_, _, rfl, index, payload⟩
  | .nativeConv prior formed conversion =>
      obtain ⟨term, equal, admitted⟩ := RuntimeValueTyping.canonical prior
      obtain ⟨u, isUniverse, typeTyped⟩ := formed
      exact ⟨term, equal, .conv admitted typeTyped isUniverse conversion⟩
termination_by structural typed

theorem RuntimeValueTyping.native_payload {types : CellTypes Head m}
    {value : RuntimeValue Head Operation Effect m} {A : Tm Head m}
    (typed : RuntimeValueTyping R signature Δ types value (.native A)) :
    ∃ term, value = .native term ∧ FormationSensitive.Typing R Δ term A := typed.canonical

theorem RuntimeValueTyping.native_admitted {types : CellTypes Head m} {term A : Tm Head m}
    (typed : RuntimeValueTyping (Effect := Effect) R signature Δ types (.native term) (.native A)) :
    FormationSensitive.Typing R Δ term A := by
  obtain ⟨other, equal, admitted⟩ := typed.native_payload
  cases equal
  exact admitted

theorem RuntimeValueTyping.thunk_payload {types : CellTypes Head m}
    {value : RuntimeValue Head Operation Effect m} {B : CTy Head m}
    (typed : RuntimeValueTyping R signature Δ types value (.thunk B)) :
    ∃ (n v k : Nat) (code : Computation Head Operation Effect n v k)
      (native : Sub Head n m) (values : Fin v → RuntimeValue Head Operation Effect m) (needs : Fin k → CellId),
      value = .thunk code native values needs ∧
        ClosureTyping R signature Δ types ⟨n, v, k, code, native, values, needs⟩ B := typed.canonical

theorem RuntimeValueTyping.pair_payload {types : CellTypes Head m}
    {value : RuntimeValue Head Operation Effect m} {A : Tm Head m} {B : VTy Head (m + 1)}
    (typed : RuntimeValueTyping R signature Δ types value (.sigmaNative A B)) :
    ∃ index payload, value = .packNative index payload ∧
      FormationSensitive.Typing R Δ index A ∧
      RuntimeValueTyping R signature Δ types payload (B.instantiate index) := typed.canonical

theorem AnswerTyping.returned_payload {types : CellTypes Head m}
    {answer : Answer Head Operation Effect m} {A : VTy Head m}
    (typed : AnswerTyping R signature Δ types answer (.returns A)) :
    ∃ value, answer = .returned value ∧ RuntimeValueTyping R signature Δ types value A := by
  cases typed with
  | returned value => exact ⟨_, rfl, value⟩

theorem AnswerTyping.nativeFunction_payload {types : CellTypes Head m}
    {answer : Answer Head Operation Effect m} {A : Tm Head m} {B : CTy Head (m + 1)}
    (typed : AnswerTyping R signature Δ types answer (.nativePi A B)) :
    ∃ body, answer = .nativeFunction body ∧ NativeBodyTyping R signature Δ types body A B := by
  cases typed with
  | nativeFunction _ _ body => exact ⟨_, rfl, body⟩

theorem AnswerTyping.valueFunction_payload {types : CellTypes Head m}
    {answer : Answer Head Operation Effect m} {A : VTy Head m} {B : CTy Head m}
    (typed : AnswerTyping R signature Δ types answer (.arrow A B)) :
    ∃ body, answer = .valueFunction body ∧ ValueBodyTyping R signature Δ types body A B := by
  cases typed with
  | valueFunction _ _ body => exact ⟨_, rfl, body⟩

/-- Source native-function admission supplies both formation and its actual
captured body; no future-argument hypothesis is used. -/
theorem nativeFunction_typed {Γ : Ctx Head n} {sv : Fin v → VTy Head n} {sn : Fin k → CTy Head n}
    {body : Computation Head Operation Effect (n + 1) v k} {A : Tm Head n} {B : CTy Head (n + 1)}
    (source : ComputationTyping R signature Γ sv sn (.nativeLambda body) (.nativePi A B))
    {types : CellTypes Head m} {native : Sub Head n m}
    {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
    (environment : EnvironmentTyping R signature Γ sv sn Δ types native values needs) :
    AnswerTyping R signature Δ types (.nativeFunction ⟨n, v, k, body, native, values, needs⟩)
      (.nativePi (subst native A) (B.substitute (liftSub native))) := by
  cases source with
  | nativeLambda formedA formedB body =>
      exact .nativeFunction (formedA.substitute environment.native)
        (formedB.substitute (environment.native.lift _)) (.captured body environment)

theorem valueFunction_typed {Γ : Ctx Head n} {sv : Fin v → VTy Head n} {sn : Fin k → CTy Head n}
    {body : Computation Head Operation Effect n (v + 1) k} {A : VTy Head n} {B : CTy Head n}
    (source : ComputationTyping R signature Γ sv sn (.valueLambda body) (.arrow A B))
    {types : CellTypes Head m} {native : Sub Head n m}
    {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
    (environment : EnvironmentTyping R signature Γ sv sn Δ types native values needs) :
    AnswerTyping R signature Δ types (.valueFunction ⟨n, v, k, body, native, values, needs⟩)
      (.arrow (A.substitute native) (B.substitute native)) := by
  cases source with
  | valueLambda formedA formedB body =>
      exact .valueFunction (formedA.substitute environment.native)
        (formedB.substitute environment.native) (.captured body environment)

#print axioms RuntimeValueTyping.extend
#print axioms EnvironmentTyping.extend
#print axioms ClosureTyping.extend
#print axioms AnswerTyping.extend
#print axioms captureValue_typed
#print axioms NativeBodyTyping.open
#print axioms ValueBodyTyping.open
#print axioms NeedBodyTyping.open
#print axioms PairBodyTyping.open
#print axioms RuntimeValueTyping.canonical
#print axioms RuntimeValueTyping.native_admitted
#print axioms nativeFunction_typed
#print axioms valueFunction_typed

end PolarizedNeedMachine
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
