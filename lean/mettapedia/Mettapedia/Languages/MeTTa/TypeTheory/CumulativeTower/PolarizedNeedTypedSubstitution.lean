import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedTyping
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedSubstitution

/-!
# Typed simultaneous substitution for the polarized source candidate

The three replacement environments have independent obligations: a native
formation-sensitive context morphism, admitted first-class value replacements,
and exact reindexing of declared Need types. The resulting source theorem
retains dependent native indices and captured closures. Principal opening laws
concern source typing; they do not identify runtime closures, choose a surface
strategy, or establish preservation for the whole machine.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeed

open ScopedComputation (OperationSignature)

variable {Head Operation Effect : Type} {n m v w k l : Nat}
  {R : Rules Head} {signature : OperationSignature Head Operation}

private theorem nativeRenaming {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m}
    (compatible : CtxRen Γ Δ ρ) : FormationSensitive.CtxMor R Γ Δ (renSub ρ) := by
  intro i
  simpa only [renSub, subst_renSub, compatible i] using
    (FormationSensitive.Typing.var (R := R) (Γ := Δ) (ρ i))

theorem NativeFormation.rename {Γ : Ctx Head n} {Δ : Ctx Head m} {A : Tm Head n}
    (formed : NativeFormation R Γ A) {ρ : Ren n m} (compatible : CtxRen Γ Δ ρ) :
    NativeFormation R Δ (Presentation.rename ρ A) := by
  simpa only [subst_renSub] using formed.substitute (nativeRenaming compatible)

theorem ValueFormation.rename {Γ : Ctx Head n} {Δ : Ctx Head m} {A : VTy Head n}
    (formed : ValueFormation R Γ A) {ρ : Ren n m} (compatible : CtxRen Γ Δ ρ) :
    ValueFormation R Δ (A.rename ρ) := by
  simpa only [VTy.substitute_renSub] using formed.substitute (nativeRenaming compatible)

theorem ComputationFormation.rename {Γ : Ctx Head n} {Δ : Ctx Head m} {A : CTy Head n}
    (formed : ComputationFormation R Γ A) {ρ : Ren n m} (compatible : CtxRen Γ Δ ρ) :
    ComputationFormation R Δ (A.rename ρ) := by
  simpa only [CTy.substitute_renSub] using formed.substitute (nativeRenaming compatible)

private theorem value_rename_weaken (ρ : Ren n m) (A : VTy Head n) :
    (A.rename wk).rename (liftRen ρ) = (A.rename ρ).rename wk := by
  simp only [VTy.rename_comp]
  rfl

private theorem computation_rename_weaken (ρ : Ren n m) (A : CTy Head n) :
    (A.rename wk).rename (liftRen ρ) = (A.rename ρ).rename wk := by
  simp only [CTy.rename_comp]
  rfl

private theorem value_rename_instantiate (ρ : Ren n m) (a : Tm Head n)
    (B : VTy Head (n + 1)) :
    (B.instantiate a).rename ρ = (B.rename (liftRen ρ)).instantiate (Presentation.rename ρ a) := by
  simpa only [VTy.substitute_renSub, subst_renSub, liftSub_renSub] using
    VTy.substitute_instantiate (renSub ρ) a B

private theorem computation_rename_instantiate (ρ : Ren n m) (a : Tm Head n)
    (B : CTy Head (n + 1)) :
    (B.instantiate a).rename ρ = (B.rename (liftRen ρ)).instantiate (Presentation.rename ρ a) := by
  simpa only [CTy.substitute_renSub, subst_renSub, liftSub_renSub] using
    CTy.substitute_instantiate (renSub ρ) a B

/-- A renaming respects each independently declared coordinate. -/
structure TypedRenaming (Γ : Ctx Head n) (sourceValues : Fin v → VTy Head n)
    (sourceNeeds : Fin k → CTy Head n) (Δ : Ctx Head m)
    (targetValues : Fin w → VTy Head m) (targetNeeds : Fin l → CTy Head m)
    (ρ : Ren n m) (ν : Ren v w) (θ : Ren k l) : Prop where
  native : CtxRen Γ Δ ρ
  values : ∀ i, targetValues (ν i) = (sourceValues i).rename ρ
  needs : ∀ i, targetNeeds (θ i) = (sourceNeeds i).rename ρ

namespace TypedRenaming

variable {Γ : Ctx Head n} {Δ : Ctx Head m}
  {sv : Fin v → VTy Head n} {sn : Fin k → CTy Head n}
  {tv : Fin w → VTy Head m} {tn : Fin l → CTy Head m}
  {ρ : Ren n m} {ν : Ren v w} {θ : Ren k l}

theorem liftNative (typed : TypedRenaming Γ sv sn Δ tv tn ρ ν θ) (A : Tm Head n) :
    TypedRenaming (.snoc Γ A) (weakenValueTypes sv) (weakenNeedTypes sn)
      (.snoc Δ (Presentation.rename ρ A)) (weakenValueTypes tv) (weakenNeedTypes tn)
      (liftRen ρ) ν θ where
  native := typed.native.snoc A
  values i := by simp only [weakenValueTypes, typed.values, value_rename_weaken]
  needs i := by simp only [weakenNeedTypes, typed.needs, computation_rename_weaken]

theorem liftValue (typed : TypedRenaming Γ sv sn Δ tv tn ρ ν θ) (A : VTy Head n) :
    TypedRenaming Γ (extendValueTypes A sv) sn Δ (extendValueTypes (A.rename ρ) tv) tn
      ρ (liftRen ν) θ where
  native := typed.native
  values i := by
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j; exact typed.values j
  needs := typed.needs

theorem liftNeed (typed : TypedRenaming Γ sv sn Δ tv tn ρ ν θ) (A : CTy Head n) :
    TypedRenaming Γ sv (extendNeedTypes A sn) Δ tv (extendNeedTypes (A.rename ρ) tn)
      ρ ν (liftRen θ) where
  native := typed.native
  values := typed.values
  needs i := by
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j; exact typed.needs j

end TypedRenaming

mutual
  theorem ValueTyping.rename {n v k : Nat} {Γ : Ctx Head n}
      {sv : Fin v → VTy Head n} {sn : Fin k → CTy Head n}
      {value : Value Head Operation Effect n v k} {A : VTy Head n}
      (typing : ValueTyping R signature Γ sv sn value A)
      {m w l : Nat} {Δ : Ctx Head m} {tv : Fin w → VTy Head m} {tn : Fin l → CTy Head m}
      {ρ : Ren n m} {ν : Ren v w} {θ : Ren k l}
      (typed : TypedRenaming Γ sv sn Δ tv tn ρ ν θ) :
      ValueTyping R signature Δ tv tn (value.rename ρ ν θ) (A.rename ρ) := by
    match typing with
    | .native admitted => exact .native (admitted.renameTyping typed.native)
    | .variable i => simpa only [Value.rename, typed.values] using
        (ValueTyping.variable (R := R) (signature := signature) (Γ := Δ)
          (valueTypes := tv) (needTypes := tn) (ν i))
    | .thunk body => exact .thunk (ComputationTyping.rename body typed)
    | .packNative formedA formedB admitted body =>
        exact .packNative (formedA.rename typed.native) (formedB.rename (typed.native.snoc _))
          (admitted.renameTyping typed.native)
          (by simpa only [value_rename_instantiate] using ValueTyping.rename body typed)
    | .nativeConv prior formed conversion =>
        exact .nativeConv (ValueTyping.rename prior typed) (formed.rename typed.native)
          (conversion.renameTerms ρ)
  termination_by structural typing

  theorem ComputationTyping.rename {n v k : Nat} {Γ : Ctx Head n}
      {sv : Fin v → VTy Head n} {sn : Fin k → CTy Head n}
      {code : Computation Head Operation Effect n v k} {A : CTy Head n}
      (typing : ComputationTyping R signature Γ sv sn code A)
      {m w l : Nat} {Δ : Ctx Head m} {tv : Fin w → VTy Head m} {tn : Fin l → CTy Head m}
      {ρ : Ren n m} {ν : Ren v w} {θ : Ren k l}
      (typed : TypedRenaming Γ sv sn Δ tv tn ρ ν θ) :
      ComputationTyping R signature Δ tv tn (code.rename ρ ν θ) (A.rename ρ) := by
    match typing with
    | .returnValue value => exact .returnValue (ValueTyping.rename value typed)
    | .bindNative formedA formedB first body =>
        exact .bindNative (formedA.rename typed.native) (formedB.rename typed.native)
          (ComputationTyping.rename first typed)
          (by simpa only [computation_rename_weaken] using
            ComputationTyping.rename body (typed.liftNative _))
    | .bindValue formedA formedB first body =>
        exact .bindValue (formedA.rename typed.native) (formedB.rename typed.native)
          (ComputationTyping.rename first typed) (ComputationTyping.rename body (typed.liftValue _))
    | .sequenceSigma formed first body =>
        exact .sequenceSigma (formed.rename typed.native) (ComputationTyping.rename first typed)
          (ComputationTyping.rename body (typed.liftNative _))
    | .nativeLambda formedA formedB body =>
        exact .nativeLambda (formedA.rename typed.native) (formedB.rename (typed.native.snoc _))
          (ComputationTyping.rename body (typed.liftNative _))
    | .nativeApply function argument =>
        simpa only [Computation.rename, CTy.rename, computation_rename_instantiate] using
          ComputationTyping.nativeApply (ComputationTyping.rename function typed)
            (argument.renameTyping typed.native)
    | .valueLambda formedA formedB body =>
        exact .valueLambda (formedA.rename typed.native) (formedB.rename typed.native)
          (ComputationTyping.rename body (typed.liftValue _))
    | .valueApply function argument =>
        exact .valueApply (ComputationTyping.rename function typed) (ValueTyping.rename argument typed)
    | .forceThunk value => exact .forceThunk (ValueTyping.rename value typed)
    | .unpackNative formedA formedB formedC value body =>
        exact .unpackNative (formedA.rename typed.native) (formedB.rename (typed.native.snoc _))
          (formedC.rename typed.native) (ValueTyping.rename value typed)
          (by simpa only [computation_rename_weaken] using
            ComputationTyping.rename body ((typed.liftNative _).liftValue _))
    | .choose left right =>
        exact .choose (ComputationTyping.rename left typed) (ComputationTyping.rename right typed)
    | .call declared argument =>
        simpa only [Computation.rename, CTy.rename, VTy.rename, OperationSignature.rename_result] using
          ComputationTyping.call declared
            (by simpa only [rename_liftClosed] using argument.renameTyping typed.native)
    | .emit next => exact .emit (ComputationTyping.rename next typed)
    | .letNeed formedA formedB first body =>
        exact .letNeed (formedA.rename typed.native) (formedB.rename typed.native)
          (ComputationTyping.rename first typed) (ComputationTyping.rename body (typed.liftNeed _))
    | .forceNeed i => simpa only [Computation.rename, typed.needs] using
        (ComputationTyping.forceNeed (R := R) (signature := signature) (Γ := Δ)
          (valueTypes := tv) (needTypes := tn) (θ i))
    | .nativeConv prior formed conversion =>
        exact .nativeConv (ComputationTyping.rename prior typed) (formed.rename typed.native)
          (conversion.renameTerms ρ)
  termination_by structural typing
end

/-- Native replacements carry actual refined derivations; value replacements
carry the independent source judgment. Need names preserve declared types. -/
structure TypedSubstitution (R : Rules Head) (signature : OperationSignature Head Operation)
    (Γ : Ctx Head n) (sourceValues : Fin v → VTy Head n) (sourceNeeds : Fin k → CTy Head n)
    (Δ : Ctx Head m) (targetValues : Fin w → VTy Head m) (targetNeeds : Fin l → CTy Head m)
    (σ : Substitution Head Operation Effect n v k m w l) : Prop where
  native : FormationSensitive.CtxMor R Γ Δ σ.native
  values : ∀ i, ValueTyping R signature Δ targetValues targetNeeds (σ.values i)
    ((sourceValues i).substitute σ.native)
  needs : ∀ i, targetNeeds (σ.needs i) = (sourceNeeds i).substitute σ.native

namespace TypedSubstitution

variable {Γ : Ctx Head n} {Δ : Ctx Head m}
  {sv : Fin v → VTy Head n} {sn : Fin k → CTy Head n}
  {tv : Fin w → VTy Head m} {tn : Fin l → CTy Head m}
  {σ : Substitution Head Operation Effect n v k m w l}

theorem liftNative (typed : TypedSubstitution R signature Γ sv sn Δ tv tn σ) (A : Tm Head n) :
    TypedSubstitution R signature (.snoc Γ A) (weakenValueTypes sv) (weakenNeedTypes sn)
      (.snoc Δ (subst σ.native A)) (weakenValueTypes tv) (weakenNeedTypes tn) σ.liftNative where
  native := typed.native.lift A
  values i := by
    simpa only [Substitution.liftNative, weakenValueTypes, VTy.substitute_weaken] using
      (typed.values i).rename
        (show TypedRenaming Δ tv tn (.snoc Δ (subst σ.native A))
          (weakenValueTypes tv) (weakenNeedTypes tn) wk idRen idRen from
          ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩)
  needs i := by
    simp only [Substitution.liftNative, weakenNeedTypes, typed.needs, CTy.substitute_weaken]

theorem liftValue (typed : TypedSubstitution R signature Γ sv sn Δ tv tn σ) (A : VTy Head n) :
    TypedSubstitution R signature Γ (extendValueTypes A sv) sn
      Δ (extendValueTypes (A.substitute σ.native) tv) tn σ.liftValue where
  native := typed.native
  values i := by
    refine Fin.cases ?_ ?_ i
    · exact .variable 0
    · intro j
      simpa only [Substitution.liftValue, extendValueTypes, Fin.cases_succ, VTy.rename_id] using
        (typed.values j).rename
          (show TypedRenaming Δ tv tn Δ (extendValueTypes (A.substitute σ.native) tv) tn
            idRen wk idRen from
            ⟨by intro x; simp only [idRen, Presentation.rename_id],
              by intro x; simp only [extendValueTypes, wk, Fin.cases_succ, VTy.rename_id],
              by intro x; simp only [idRen, CTy.rename_id]⟩)
  needs := typed.needs

theorem liftNeed (typed : TypedSubstitution R signature Γ sv sn Δ tv tn σ) (A : CTy Head n) :
    TypedSubstitution R signature Γ sv (extendNeedTypes A sn)
      Δ tv (extendNeedTypes (A.substitute σ.native) tn) σ.liftNeed where
  native := typed.native
  values i := by
    simpa only [Substitution.liftNeed, VTy.rename_id] using
      (typed.values i).rename
        (show TypedRenaming Δ tv tn Δ tv (extendNeedTypes (A.substitute σ.native) tn)
          idRen idRen wk from
          ⟨by intro x; simp only [idRen, Presentation.rename_id],
            by intro x; simp only [idRen, VTy.rename_id],
            by intro x; simp only [extendNeedTypes, wk, Fin.cases_succ, CTy.rename_id]⟩)
  needs i := by
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j; exact typed.needs j

end TypedSubstitution

mutual
  /-- Simultaneous substitution preserves independent value admission. -/
  theorem ValueTyping.substitute {n v k : Nat} {Γ : Ctx Head n}
      {sv : Fin v → VTy Head n} {sn : Fin k → CTy Head n}
      {value : Value Head Operation Effect n v k} {A : VTy Head n}
      (typing : ValueTyping R signature Γ sv sn value A)
      {m w l : Nat} {Δ : Ctx Head m} {tv : Fin w → VTy Head m} {tn : Fin l → CTy Head m}
      {σ : Substitution Head Operation Effect n v k m w l}
      (typed : TypedSubstitution R signature Γ sv sn Δ tv tn σ) :
      ValueTyping R signature Δ tv tn (value.substitute σ) (A.substitute σ.native) := by
    match typing with
    | .native admitted => exact .native (admitted.substitute typed.native)
    | .variable i => exact typed.values i
    | .thunk body => exact .thunk (ComputationTyping.substitute body typed)
    | .packNative formedA formedB admitted body =>
        exact .packNative (formedA.substitute typed.native) (formedB.substitute (typed.native.lift _))
          (admitted.substitute typed.native)
          (by simpa only [VTy.substitute_instantiate] using ValueTyping.substitute body typed)
    | .nativeConv prior formed conversion =>
        exact .nativeConv (ValueTyping.substitute prior typed) (formed.substitute typed.native)
          (conversion.substitute σ.native)
  termination_by structural typing

  /-- All source constructors retain their displayed result family under the
  actual three-scope operation, including ordinary and shared suspensions. -/
  theorem ComputationTyping.substitute {n v k : Nat} {Γ : Ctx Head n}
      {sv : Fin v → VTy Head n} {sn : Fin k → CTy Head n}
      {code : Computation Head Operation Effect n v k} {A : CTy Head n}
      (typing : ComputationTyping R signature Γ sv sn code A)
      {m w l : Nat} {Δ : Ctx Head m} {tv : Fin w → VTy Head m} {tn : Fin l → CTy Head m}
      {σ : Substitution Head Operation Effect n v k m w l}
      (typed : TypedSubstitution R signature Γ sv sn Δ tv tn σ) :
      ComputationTyping R signature Δ tv tn (code.substitute σ) (A.substitute σ.native) := by
    match typing with
    | .returnValue value => exact .returnValue (ValueTyping.substitute value typed)
    | .bindNative formedA formedB first body =>
        exact .bindNative (formedA.substitute typed.native) (formedB.substitute typed.native)
          (ComputationTyping.substitute first typed)
          (by simpa only [Substitution.liftNative, CTy.substitute_weaken] using
            ComputationTyping.substitute body (typed.liftNative _))
    | .bindValue formedA formedB first body =>
        exact .bindValue (formedA.substitute typed.native) (formedB.substitute typed.native)
          (ComputationTyping.substitute first typed) (ComputationTyping.substitute body (typed.liftValue _))
    | .sequenceSigma formed first body =>
        exact .sequenceSigma (formed.substitute typed.native) (ComputationTyping.substitute first typed)
          (ComputationTyping.substitute body (typed.liftNative _))
    | .nativeLambda formedA formedB body =>
        exact .nativeLambda (formedA.substitute typed.native) (formedB.substitute (typed.native.lift _))
          (ComputationTyping.substitute body (typed.liftNative _))
    | .nativeApply function argument =>
        simpa only [Computation.substitute, CTy.substitute, CTy.substitute_instantiate] using
          ComputationTyping.nativeApply (ComputationTyping.substitute function typed)
            (argument.substitute typed.native)
    | .valueLambda formedA formedB body =>
        exact .valueLambda (formedA.substitute typed.native) (formedB.substitute typed.native)
          (ComputationTyping.substitute body (typed.liftValue _))
    | .valueApply function argument =>
        exact .valueApply (ComputationTyping.substitute function typed) (ValueTyping.substitute argument typed)
    | .forceThunk value => exact .forceThunk (ValueTyping.substitute value typed)
    | .unpackNative formedA formedB formedC value body =>
        exact .unpackNative (formedA.substitute typed.native) (formedB.substitute (typed.native.lift _))
          (formedC.substitute typed.native) (ValueTyping.substitute value typed)
          (by simpa only [Substitution.liftValue, Substitution.liftNative, CTy.substitute_weaken] using
            ComputationTyping.substitute body ((typed.liftNative _).liftValue _))
    | .choose left right =>
        exact .choose (ComputationTyping.substitute left typed) (ComputationTyping.substitute right typed)
    | .call declared argument =>
        simpa only [Computation.substitute, CTy.substitute, VTy.substitute,
          OperationSignature.substitute_result] using
          ComputationTyping.call declared
            (by simpa only [subst_liftClosed] using argument.substitute typed.native)
    | .emit next => exact .emit (ComputationTyping.substitute next typed)
    | .letNeed formedA formedB first body =>
        exact .letNeed (formedA.substitute typed.native) (formedB.substitute typed.native)
          (ComputationTyping.substitute first typed) (ComputationTyping.substitute body (typed.liftNeed _))
    | .forceNeed i => simpa only [Computation.substitute, typed.needs] using
        (ComputationTyping.forceNeed (R := R) (signature := signature) (Γ := Δ)
          (valueTypes := tv) (needTypes := tn) (σ.needs i))
    | .nativeConv prior formed conversion =>
        exact .nativeConv (ComputationTyping.substitute prior typed) (formed.substitute typed.native)
          (conversion.substitute σ.native)
  termination_by structural typing
end

section Opening

variable {Γ : Ctx Head n} {sv : Fin v → VTy Head n} {sn : Fin k → CTy Head n}

private theorem nativeOpening {A argument : Tm Head n}
    (admitted : FormationSensitive.Typing R Γ argument A) :
    FormationSensitive.CtxMor R (.snoc Γ A) Γ (subst0 argument) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · change FormationSensitive.Typing R Γ argument (inst0 argument (Presentation.rename wk A))
    rw [inst0_rename_wk]
    exact admitted
  · intro j
    change FormationSensitive.Typing R Γ (.var j)
      (inst0 argument (Presentation.rename wk (Ctx.lookup Γ j)))
    rw [inst0_rename_wk]
    exact .var j

theorem TypedSubstitution.openNative {A argument : Tm Head n}
    (admitted : FormationSensitive.Typing R Γ argument A) :
    TypedSubstitution R signature (.snoc Γ A) (weakenValueTypes sv) (weakenNeedTypes sn)
      Γ sv sn (Substitution.openNative (Operation := Operation) (Effect := Effect) argument) where
  native := nativeOpening admitted
  values i := by
    change ValueTyping R signature Γ sv sn (.variable i) ((sv i).rename wk |>.instantiate argument)
    rw [VTy.instantiate_weaken]
    exact .variable i
  needs i := by
    change sn i = ((sn i).rename wk).instantiate argument
    rw [CTy.instantiate_weaken]

theorem TypedSubstitution.openValue {A : VTy Head n} {value : Value Head Operation Effect n v k}
    (admitted : ValueTyping R signature Γ sv sn value A) :
    TypedSubstitution R signature Γ (extendValueTypes A sv) sn Γ sv sn
      (Substitution.openValue value) where
  native i := by
    simpa only [Substitution.openValue, subst_ids, Presentation.ids] using
      (FormationSensitive.Typing.var (R := R) (Γ := Γ) i)
  values i := by
    refine Fin.cases ?_ ?_ i
    · simpa only [Substitution.openValue, extendValueTypes, Fin.cases_zero,
        VTy.substitute_ids] using admitted
    · intro j
      simpa only [Substitution.openValue, extendValueTypes, Fin.cases_succ,
        VTy.substitute_ids] using
        (ValueTyping.variable (R := R) (signature := signature) (Γ := Γ)
          (valueTypes := sv) (needTypes := sn) j)
  needs i := by simp only [Substitution.openValue, idRen, CTy.substitute_ids]

/-- Opening a native binder preserves its actual dependent result type. -/
theorem ComputationTyping.instantiateNative {A argument : Tm Head n}
    {body : Computation Head Operation Effect (n + 1) v k} {B : CTy Head (n + 1)}
    (typing : ComputationTyping R signature (.snoc Γ A) (weakenValueTypes sv)
      (weakenNeedTypes sn) body B)
    (admitted : FormationSensitive.Typing R Γ argument A) :
    ComputationTyping R signature Γ sv sn (body.instantiateNative argument) (B.instantiate argument) :=
  typing.substitute (TypedSubstitution.openNative admitted)

/-- Opening a first-class value binder never inserts that closure into a native
term or a native type. -/
theorem ComputationTyping.instantiateValue {A : VTy Head n} {B : CTy Head n}
    {body : Computation Head Operation Effect n (v + 1) k}
    {value : Value Head Operation Effect n v k}
    (typing : ComputationTyping R signature Γ (extendValueTypes A sv) sn body B)
    (admitted : ValueTyping R signature Γ sv sn value A) :
    ComputationTyping R signature Γ sv sn (body.instantiateValue value) B := by
  simpa only [Computation.instantiateValue, Substitution.openValue, CTy.substitute_ids] using
    typing.substitute (TypedSubstitution.openValue admitted)

/-- The two-coordinate opening retains the selected native index in the
payload's type, while substituting the payload in the separate value scope. -/
theorem ComputationTyping.instantiateNativeValue {A index : Tm Head n}
    {B : VTy Head (n + 1)} {C : CTy Head (n + 1)}
    {body : Computation Head Operation Effect (n + 1) (v + 1) k}
    {value : Value Head Operation Effect n v k}
    (typing : ComputationTyping R signature (.snoc Γ A)
      (extendValueTypes B (weakenValueTypes sv)) (weakenNeedTypes sn) body C)
    (indexTyped : FormationSensitive.Typing R Γ index A)
    (valueTyped : ValueTyping R signature Γ sv sn value (B.instantiate index)) :
    ComputationTyping R signature Γ sv sn (body.instantiateNativeValue index value)
      (C.instantiate index) := by
  have opening : TypedSubstitution R signature (.snoc Γ A)
      (extendValueTypes B (weakenValueTypes sv)) (weakenNeedTypes sn)
      Γ (extendValueTypes (B.instantiate index) sv) sn
      (Substitution.openNative (Operation := Operation) (Effect := Effect) index) := by
    refine ⟨nativeOpening indexTyped, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · exact .variable 0
      · intro j
        change ValueTyping R signature Γ (extendValueTypes (B.instantiate index) sv) sn
          (.variable j.succ) (((sv j).rename wk).instantiate index)
        rw [VTy.instantiate_weaken]
        exact .variable j.succ
    · intro i
      change sn i = ((sn i).rename wk).instantiate index
      rw [CTy.instantiate_weaken]
  exact (typing.substitute opening).instantiateValue valueTyped

/-- The four principal source openings. This relation selects no evaluation
order and performs no allocation or memoized force. -/
inductive PrincipalOpening : Computation Head Operation Effect n v k →
    Computation Head Operation Effect n v k → Prop where
  | nativeApply (body : Computation Head Operation Effect (n + 1) v k) (argument : Tm Head n) :
      PrincipalOpening (.nativeApply (.nativeLambda body) argument) (body.instantiateNative argument)
  | valueApply (body : Computation Head Operation Effect n (v + 1) k)
      (argument : Value Head Operation Effect n v k) :
      PrincipalOpening (.valueApply (.valueLambda body) argument) (body.instantiateValue argument)
  | unpackNative (body : Computation Head Operation Effect (n + 1) (v + 1) k)
      (index : Tm Head n) (value : Value Head Operation Effect n v k) :
      PrincipalOpening (.unpackNative (.packNative index value) body)
        (body.instantiateNativeValue index value)
  | forceThunk (body : Computation Head Operation Effect n v k) :
      PrincipalOpening (.forceThunk (.thunk body)) body

/-- Every principal opening preserves the independently derived displayed
type, including a final native conversion. No post-opening judgment is assumed. -/
theorem ComputationTyping.principalOpening {code result : Computation Head Operation Effect n v k}
    {B : CTy Head n} (typing : ComputationTyping R signature Γ sv sn code B)
    (opening : PrincipalOpening code result) :
    ComputationTyping R signature Γ sv sn result B := by
  match typing with
  | .returnValue _ => cases opening
  | .bindNative _ _ _ _ => cases opening
  | .bindValue _ _ _ _ => cases opening
  | .sequenceSigma _ _ _ => cases opening
  | .nativeLambda _ _ _ => cases opening
  | .nativeApply function admitted =>
      cases opening with
      | nativeApply body argument =>
          cases function with
          | nativeLambda _ _ typedBody => exact typedBody.instantiateNative admitted
  | .valueLambda _ _ _ => cases opening
  | .valueApply function admitted =>
      cases opening with
      | valueApply body argument =>
          cases function with
          | valueLambda _ _ typedBody => exact typedBody.instantiateValue admitted
  | .forceThunk value =>
      cases opening with
      | forceThunk body => cases value with | thunk typedBody => exact typedBody
  | .unpackNative _ _ _ packet typedBody =>
      cases opening with
      | unpackNative body index value =>
          cases packet with
          | packNative _ _ indexTyped valueTyped =>
              simpa only [CTy.instantiate_weaken] using
                typedBody.instantiateNativeValue indexTyped valueTyped
  | .choose _ _ => cases opening
  | .call _ _ => cases opening
  | .emit _ => cases opening
  | .letNeed _ _ _ _ => cases opening
  | .forceNeed _ => cases opening
  | .nativeConv prior formed conversion =>
      exact .nativeConv (ComputationTyping.principalOpening prior opening) formed conversion
termination_by structural typing

theorem ComputationTyping.betaNative {body : Computation Head Operation Effect (n + 1) v k}
    {argument : Tm Head n} {B : CTy Head n}
    (typing : ComputationTyping R signature Γ sv sn (.nativeApply (.nativeLambda body) argument) B) :
    ComputationTyping R signature Γ sv sn (body.instantiateNative argument) B :=
  typing.principalOpening (.nativeApply body argument)

theorem ComputationTyping.betaValue {body : Computation Head Operation Effect n (v + 1) k}
    {argument : Value Head Operation Effect n v k} {B : CTy Head n}
    (typing : ComputationTyping R signature Γ sv sn (.valueApply (.valueLambda body) argument) B) :
    ComputationTyping R signature Γ sv sn (body.instantiateValue argument) B :=
  typing.principalOpening (.valueApply body argument)

theorem ComputationTyping.betaUnpack {body : Computation Head Operation Effect (n + 1) (v + 1) k}
    {index : Tm Head n} {value : Value Head Operation Effect n v k} {C : CTy Head n}
    (typing : ComputationTyping R signature Γ sv sn (.unpackNative (.packNative index value) body) C) :
    ComputationTyping R signature Γ sv sn (body.instantiateNativeValue index value) C :=
  typing.principalOpening (.unpackNative body index value)

theorem ComputationTyping.betaForce {body : Computation Head Operation Effect n v k} {B : CTy Head n}
    (typing : ComputationTyping R signature Γ sv sn (.forceThunk (.thunk body)) B) :
    ComputationTyping R signature Γ sv sn body B :=
  typing.principalOpening (.forceThunk body)

end Opening

#print axioms ValueTyping.rename
#print axioms ComputationTyping.rename
#print axioms ValueTyping.substitute
#print axioms ComputationTyping.substitute
#print axioms ComputationTyping.instantiateNativeValue
#print axioms ComputationTyping.betaNative
#print axioms ComputationTyping.betaValue
#print axioms ComputationTyping.betaUnpack
#print axioms ComputationTyping.betaForce

end PolarizedNeed
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
