import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedSyntax

/-!
# Simultaneous source substitution for native-indexed polarized computations

Native terms, first-class values and Need references have separate replacement
environments. A value replacement may capture every scope, so each binder
weakens all corresponding free references in that replacement. Native terms
still receive only native terms. These are source binding laws, not runtime
closure equality, formation, normalization or profile adoption.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeed

/-- A simultaneous replacement between all three source scopes. -/
structure Substitution (Head Operation Effect : Type) (n v k m w l : Nat) where
  native : Sub Head n m
  values : Fin v → Value Head Operation Effect m w l
  needs : Ren k l

variable {Head Operation Effect : Type}

namespace Substitution

variable {n v k m w l p x q : Nat}

@[ext] theorem ext {σ τ : Substitution Head Operation Effect n v k m w l}
    (native : ∀ i, σ.native i = τ.native i)
    (values : ∀ i, σ.values i = τ.values i)
    (needs : ∀ i, σ.needs i = τ.needs i) : σ = τ := by
  cases σ
  cases τ
  simp only [mk.injEq]
  exact ⟨funext native, funext values, funext needs⟩

def ids : Substitution Head Operation Effect n v k n v k :=
  ⟨Presentation.ids, Value.variable, idRen⟩

def ofRenaming (ρ : Ren n m) (ν : Ren v w) (θ : Ren k l) :
    Substitution Head Operation Effect n v k m w l :=
  ⟨renSub ρ, fun i => .variable (ν i), θ⟩

def liftNative (σ : Substitution Head Operation Effect n v k m w l) :
    Substitution Head Operation Effect (n + 1) v k (m + 1) w l :=
  ⟨liftSub σ.native, fun i => (σ.values i).rename wk idRen idRen, σ.needs⟩

def liftValue (σ : Substitution Head Operation Effect n v k m w l) :
    Substitution Head Operation Effect n (v + 1) k m (w + 1) l :=
  ⟨σ.native, Fin.cases (.variable 0) (fun i => (σ.values i).rename idRen wk idRen), σ.needs⟩

def liftNeed (σ : Substitution Head Operation Effect n v k m w l) :
    Substitution Head Operation Effect n v (k + 1) m w (l + 1) :=
  ⟨σ.native, fun i => (σ.values i).rename idRen idRen wk, liftRen σ.needs⟩

/-- Reindex the result of every replacement. -/
def rename (ρ : Ren m p) (ν : Ren w x) (θ : Ren l q)
    (σ : Substitution Head Operation Effect n v k m w l) :
    Substitution Head Operation Effect n v k p x q :=
  ⟨fun i => Presentation.rename ρ (σ.native i),
    fun i => (σ.values i).rename ρ ν θ, fun i => θ (σ.needs i)⟩

/-- Select replacements along a source renaming. -/
def afterRename (σ : Substitution Head Operation Effect m w l p x q)
    (ρ : Ren n m) (ν : Ren v w) (θ : Ren k l) :
    Substitution Head Operation Effect n v k p x q :=
  ⟨fun i => σ.native (ρ i), fun i => σ.values (ν i), fun i => σ.needs (θ i)⟩

@[simp] theorem ids_native :
    (ids : Substitution Head Operation Effect n v k n v k).native = Presentation.ids := rfl

@[simp] theorem ofRenaming_native (ρ : Ren n m) (ν : Ren v w) (θ : Ren k l) :
    (ofRenaming (Head := Head) (Operation := Operation) (Effect := Effect) ρ ν θ).native =
      renSub ρ := rfl

@[simp] theorem rename_native (ρ : Ren m p) (ν : Ren w x) (θ : Ren l q)
    (σ : Substitution Head Operation Effect n v k m w l) :
    (σ.rename ρ ν θ).native = fun i => Presentation.rename ρ (σ.native i) := rfl

@[simp] theorem afterRename_native (σ : Substitution Head Operation Effect m w l p x q)
    (ρ : Ren n m) (ν : Ren v w) (θ : Ren k l) :
    (σ.afterRename ρ ν θ).native = fun i => σ.native (ρ i) := rfl

@[simp] theorem liftNative_ids :
    (ids : Substitution Head Operation Effect n v k n v k).liftNative = ids := by
  apply ext
  · intro i; exact congrFun liftSub_ids i
  · intro i; rfl
  · intro i; rfl

@[simp] theorem liftValue_ids :
    (ids : Substitution Head Operation Effect n v k n v k).liftValue = ids := by
  apply ext
  · intro i; rfl
  · intro i; exact Fin.cases rfl (fun _ => rfl) i
  · intro i; rfl

@[simp] theorem liftNeed_ids :
    (ids : Substitution Head Operation Effect n v k n v k).liftNeed = ids := by
  apply ext
  · intro i; rfl
  · intro i; rfl
  · intro i; exact congrFun liftRen_id i

@[simp] theorem liftNative_ofRenaming (ρ : Ren n m) (ν : Ren v w) (θ : Ren k l) :
    (ofRenaming (Head := Head) (Operation := Operation) (Effect := Effect) ρ ν θ).liftNative =
      ofRenaming (liftRen ρ) ν θ := by
  apply ext
  · intro i; exact congrFun (liftSub_renSub ρ) i
  · intro i; rfl
  · intro i; rfl

@[simp] theorem liftValue_ofRenaming (ρ : Ren n m) (ν : Ren v w) (θ : Ren k l) :
    (ofRenaming (Head := Head) (Operation := Operation) (Effect := Effect) ρ ν θ).liftValue =
      ofRenaming ρ (liftRen ν) θ := by
  apply ext
  · intro i; rfl
  · intro i; exact Fin.cases rfl (fun _ => rfl) i
  · intro i; rfl

@[simp] theorem liftNeed_ofRenaming (ρ : Ren n m) (ν : Ren v w) (θ : Ren k l) :
    (ofRenaming (Head := Head) (Operation := Operation) (Effect := Effect) ρ ν θ).liftNeed =
      ofRenaming ρ ν (liftRen θ) := by
  rfl

theorem rename_liftNative (ρ : Ren m p) (ν : Ren w x) (θ : Ren l q)
    (σ : Substitution Head Operation Effect n v k m w l) :
    σ.liftNative.rename (liftRen ρ) ν θ = (σ.rename ρ ν θ).liftNative := by
  apply ext
  · intro i; exact rename_liftSub ρ σ.native i
  · intro i
    simp only [rename, liftNative, Value.rename_comp]
    rfl
  · intro i; rfl

theorem rename_liftValue (ρ : Ren m p) (ν : Ren w x) (θ : Ren l q)
    (σ : Substitution Head Operation Effect n v k m w l) :
    σ.liftValue.rename ρ (liftRen ν) θ = (σ.rename ρ ν θ).liftValue := by
  apply ext
  · intro i; rfl
  · intro i
    refine Fin.cases rfl (fun j => ?_) i
    simp only [rename, liftValue, Fin.cases_succ, Value.rename_comp]
    rfl
  · intro i; rfl

theorem rename_liftNeed (ρ : Ren m p) (ν : Ren w x) (θ : Ren l q)
    (σ : Substitution Head Operation Effect n v k m w l) :
    σ.liftNeed.rename ρ ν (liftRen θ) = (σ.rename ρ ν θ).liftNeed := by
  apply ext
  · intro i; rfl
  · intro i
    simp only [rename, liftNeed, Value.rename_comp]
    rfl
  · intro i; exact liftRen_comp_apply θ σ.needs i

theorem afterRename_liftNative (σ : Substitution Head Operation Effect m w l p x q)
    (ρ : Ren n m) (ν : Ren v w) (θ : Ren k l) :
    σ.liftNative.afterRename (liftRen ρ) ν θ = (σ.afterRename ρ ν θ).liftNative := by
  apply ext
  · intro i; exact liftSub_liftRen_apply σ.native ρ i
  · intro i; rfl
  · intro i; rfl

theorem afterRename_liftValue (σ : Substitution Head Operation Effect m w l p x q)
    (ρ : Ren n m) (ν : Ren v w) (θ : Ren k l) :
    σ.liftValue.afterRename ρ (liftRen ν) θ = (σ.afterRename ρ ν θ).liftValue := by
  apply ext
  · intro i; rfl
  · intro i; exact Fin.cases rfl (fun _ => rfl) i
  · intro i; rfl

theorem afterRename_liftNeed (σ : Substitution Head Operation Effect m w l p x q)
    (ρ : Ren n m) (ν : Ren v w) (θ : Ren k l) :
    σ.liftNeed.afterRename ρ ν (liftRen θ) = (σ.afterRename ρ ν θ).liftNeed := by
  apply ext
  · intro i; rfl
  · intro i; rfl
  · intro i; exact liftRen_comp_apply σ.needs θ i

end Substitution

mutual
  def Value.substitute {n v k m w l : Nat}
      (σ : Substitution Head Operation Effect n v k m w l) :
      Value Head Operation Effect n v k → Value Head Operation Effect m w l
    | .native term => .native (subst σ.native term)
    | .variable index => σ.values index
    | .thunk body => .thunk (Computation.substitute σ body)
    | .packNative index value => .packNative (subst σ.native index) (Value.substitute σ value)

  def Computation.substitute {n v k m w l : Nat}
      (σ : Substitution Head Operation Effect n v k m w l) :
      Computation Head Operation Effect n v k → Computation Head Operation Effect m w l
    | .returnValue value => .returnValue (Value.substitute σ value)
    | .bindNative first body =>
        .bindNative (Computation.substitute σ first) (Computation.substitute σ.liftNative body)
    | .bindValue first body =>
        .bindValue (Computation.substitute σ first) (Computation.substitute σ.liftValue body)
    | .sequenceSigma first body =>
        .sequenceSigma (Computation.substitute σ first) (Computation.substitute σ.liftNative body)
    | .nativeLambda body => .nativeLambda (Computation.substitute σ.liftNative body)
    | .nativeApply function argument =>
        .nativeApply (Computation.substitute σ function) (subst σ.native argument)
    | .valueLambda body => .valueLambda (Computation.substitute σ.liftValue body)
    | .valueApply function argument =>
        .valueApply (Computation.substitute σ function) (Value.substitute σ argument)
    | .forceThunk value => .forceThunk (Value.substitute σ value)
    | .unpackNative value body =>
        .unpackNative (Value.substitute σ value)
          (Computation.substitute σ.liftNative.liftValue body)
    | .choose left right => .choose (Computation.substitute σ left) (Computation.substitute σ right)
    | .call operation argument => .call operation (subst σ.native argument)
    | .emit effect next => .emit effect (Computation.substitute σ next)
    | .letNeed suspended body =>
        .letNeed (Computation.substitute σ suspended) (Computation.substitute σ.liftNeed body)
    | .forceNeed reference => .forceNeed (σ.needs reference)
end


mutual
  @[simp] theorem Value.substitute_ids {n v k : Nat} (value : Value Head Operation Effect n v k) :
      value.substitute Substitution.ids = value := by
    match value with
    | .native term => simp only [Value.substitute, Substitution.ids_native, subst_ids]
    | .variable index => rfl
    | .thunk body => simp only [Value.substitute, Computation.substitute_ids body]
    | .packNative index value =>
        simp only [Value.substitute, Substitution.ids_native, subst_ids, Value.substitute_ids value]
  termination_by structural value

  @[simp] theorem Computation.substitute_ids {n v k : Nat} (code : Computation Head Operation Effect n v k) :
      code.substitute Substitution.ids = code := by
    match code with
    | .returnValue value =>
        simp only [Computation.substitute, Value.substitute_ids value]
    | .bindNative first body =>
        simp only [Computation.substitute, Computation.substitute_ids first, Computation.substitute_ids body, Substitution.liftNative_ids]
    | .bindValue first body =>
        simp only [Computation.substitute, Computation.substitute_ids first, Computation.substitute_ids body, Substitution.liftValue_ids]
    | .sequenceSigma first body =>
        simp only [Computation.substitute, Computation.substitute_ids first, Computation.substitute_ids body, Substitution.liftNative_ids]
    | .nativeLambda body =>
        simp only [Computation.substitute, Computation.substitute_ids body, Substitution.liftNative_ids]
    | .nativeApply function argument =>
        simp only [Computation.substitute, Computation.substitute_ids function, Substitution.ids_native, subst_ids]
    | .valueLambda body =>
        simp only [Computation.substitute, Computation.substitute_ids body, Substitution.liftValue_ids]
    | .valueApply function argument =>
        simp only [Computation.substitute, Computation.substitute_ids function, Value.substitute_ids argument]
    | .forceThunk value =>
        simp only [Computation.substitute, Value.substitute_ids value]
    | .unpackNative value body =>
        simp only [Computation.substitute, Value.substitute_ids value, Computation.substitute_ids body, Substitution.liftNative_ids, Substitution.liftValue_ids]
    | .choose left right =>
        simp only [Computation.substitute, Computation.substitute_ids left, Computation.substitute_ids right]
    | .call operation argument =>
        simp only [Computation.substitute, Substitution.ids_native, subst_ids]
    | .emit effect next =>
        simp only [Computation.substitute, Computation.substitute_ids next]
    | .letNeed suspended body =>
        simp only [Computation.substitute, Computation.substitute_ids suspended, Computation.substitute_ids body, Substitution.liftNeed_ids]
    | .forceNeed reference => rfl
  termination_by structural code
end

mutual
  @[simp] theorem Value.substitute_ofRenaming {n v k : Nat} (value : Value Head Operation Effect n v k)
      {m w l : Nat} (ρ : Ren n m) (ν : Ren v w) (θ : Ren k l) :
      value.substitute (Substitution.ofRenaming ρ ν θ) = value.rename ρ ν θ := by
    match value with
    | .native term => simp only [Value.substitute, Value.rename, Substitution.ofRenaming_native, subst_renSub]
    | .variable index => rfl
    | .thunk body => simp only [Value.substitute, Value.rename, Computation.substitute_ofRenaming body]
    | .packNative index value =>
        simp only [Value.substitute, Value.rename, Substitution.ofRenaming_native, subst_renSub, Value.substitute_ofRenaming value]
  termination_by structural value

  @[simp] theorem Computation.substitute_ofRenaming {n v k : Nat} (code : Computation Head Operation Effect n v k)
      {m w l : Nat} (ρ : Ren n m) (ν : Ren v w) (θ : Ren k l) :
      code.substitute (Substitution.ofRenaming ρ ν θ) = code.rename ρ ν θ := by
    match code with
    | .returnValue value =>
        simp only [Computation.substitute, Computation.rename, Value.substitute_ofRenaming value]
    | .bindNative first body =>
        simp only [Computation.substitute, Computation.rename, Computation.substitute_ofRenaming first, Computation.substitute_ofRenaming body, Substitution.liftNative_ofRenaming]
    | .bindValue first body =>
        simp only [Computation.substitute, Computation.rename, Computation.substitute_ofRenaming first, Computation.substitute_ofRenaming body, Substitution.liftValue_ofRenaming]
    | .sequenceSigma first body =>
        simp only [Computation.substitute, Computation.rename, Computation.substitute_ofRenaming first, Computation.substitute_ofRenaming body, Substitution.liftNative_ofRenaming]
    | .nativeLambda body =>
        simp only [Computation.substitute, Computation.rename, Computation.substitute_ofRenaming body, Substitution.liftNative_ofRenaming]
    | .nativeApply function argument =>
        simp only [Computation.substitute, Computation.rename, Computation.substitute_ofRenaming function, Substitution.ofRenaming_native, subst_renSub]
    | .valueLambda body =>
        simp only [Computation.substitute, Computation.rename, Computation.substitute_ofRenaming body, Substitution.liftValue_ofRenaming]
    | .valueApply function argument =>
        simp only [Computation.substitute, Computation.rename, Computation.substitute_ofRenaming function, Value.substitute_ofRenaming argument]
    | .forceThunk value =>
        simp only [Computation.substitute, Computation.rename, Value.substitute_ofRenaming value]
    | .unpackNative value body =>
        simp only [Computation.substitute, Computation.rename, Value.substitute_ofRenaming value, Computation.substitute_ofRenaming body, Substitution.liftNative_ofRenaming, Substitution.liftValue_ofRenaming]
    | .choose left right =>
        simp only [Computation.substitute, Computation.rename, Computation.substitute_ofRenaming left, Computation.substitute_ofRenaming right]
    | .call operation argument =>
        simp only [Computation.substitute, Computation.rename, Substitution.ofRenaming_native, subst_renSub]
    | .emit effect next =>
        simp only [Computation.substitute, Computation.rename, Computation.substitute_ofRenaming next]
    | .letNeed suspended body =>
        simp only [Computation.substitute, Computation.rename, Computation.substitute_ofRenaming suspended, Computation.substitute_ofRenaming body, Substitution.liftNeed_ofRenaming]
    | .forceNeed reference => rfl
  termination_by structural code
end

mutual
  theorem Value.rename_substitute {n v k : Nat} (value : Value Head Operation Effect n v k)
      {m w l p x q : Nat} (σ : Substitution Head Operation Effect n v k m w l)
      (ρ : Ren m p) (ν : Ren w x) (θ : Ren l q) :
      (value.substitute σ).rename ρ ν θ = value.substitute (σ.rename ρ ν θ) := by
    match value with
    | .native term => simp only [Value.substitute, Value.rename, Substitution.rename_native, rename_subst]
    | .variable index => rfl
    | .thunk body => simp only [Value.substitute, Value.rename, Computation.rename_substitute body]
    | .packNative index value =>
        simp only [Value.substitute, Value.rename, Substitution.rename_native, rename_subst, Value.rename_substitute value]
  termination_by structural value

  theorem Computation.rename_substitute {n v k : Nat} (code : Computation Head Operation Effect n v k)
      {m w l p x q : Nat} (σ : Substitution Head Operation Effect n v k m w l)
      (ρ : Ren m p) (ν : Ren w x) (θ : Ren l q) :
      (code.substitute σ).rename ρ ν θ = code.substitute (σ.rename ρ ν θ) := by
    match code with
    | .returnValue value =>
        simp only [Computation.substitute, Computation.rename, Value.rename_substitute value]
    | .bindNative first body =>
        simp only [Computation.substitute, Computation.rename, Computation.rename_substitute first, Computation.rename_substitute body, Substitution.rename_liftNative]
    | .bindValue first body =>
        simp only [Computation.substitute, Computation.rename, Computation.rename_substitute first, Computation.rename_substitute body, Substitution.rename_liftValue]
    | .sequenceSigma first body =>
        simp only [Computation.substitute, Computation.rename, Computation.rename_substitute first, Computation.rename_substitute body, Substitution.rename_liftNative]
    | .nativeLambda body =>
        simp only [Computation.substitute, Computation.rename, Computation.rename_substitute body, Substitution.rename_liftNative]
    | .nativeApply function argument =>
        simp only [Computation.substitute, Computation.rename, Computation.rename_substitute function, Substitution.rename_native, rename_subst]
    | .valueLambda body =>
        simp only [Computation.substitute, Computation.rename, Computation.rename_substitute body, Substitution.rename_liftValue]
    | .valueApply function argument =>
        simp only [Computation.substitute, Computation.rename, Computation.rename_substitute function, Value.rename_substitute argument]
    | .forceThunk value =>
        simp only [Computation.substitute, Computation.rename, Value.rename_substitute value]
    | .unpackNative value body =>
        simp only [Computation.substitute, Computation.rename, Value.rename_substitute value, Computation.rename_substitute body, Substitution.rename_liftNative, Substitution.rename_liftValue]
    | .choose left right =>
        simp only [Computation.substitute, Computation.rename, Computation.rename_substitute left, Computation.rename_substitute right]
    | .call operation argument =>
        simp only [Computation.substitute, Computation.rename, Substitution.rename_native, rename_subst]
    | .emit effect next =>
        simp only [Computation.substitute, Computation.rename, Computation.rename_substitute next]
    | .letNeed suspended body =>
        simp only [Computation.substitute, Computation.rename, Computation.rename_substitute suspended, Computation.rename_substitute body, Substitution.rename_liftNeed]
    | .forceNeed reference => rfl
  termination_by structural code
end

mutual
  theorem Value.substitute_rename {n v k : Nat} (value : Value Head Operation Effect n v k)
      {m w l p x q : Nat} (ρ : Ren n m) (ν : Ren v w) (θ : Ren k l)
      (σ : Substitution Head Operation Effect m w l p x q) :
      (value.rename ρ ν θ).substitute σ = value.substitute (σ.afterRename ρ ν θ) := by
    match value with
    | .native term => simp only [Value.substitute, Value.rename, Substitution.afterRename_native, subst_rename]
    | .variable index => rfl
    | .thunk body => simp only [Value.substitute, Value.rename, Computation.substitute_rename body]
    | .packNative index value =>
        simp only [Value.substitute, Value.rename, Substitution.afterRename_native, subst_rename, Value.substitute_rename value]
  termination_by structural value

  theorem Computation.substitute_rename {n v k : Nat} (code : Computation Head Operation Effect n v k)
      {m w l p x q : Nat} (ρ : Ren n m) (ν : Ren v w) (θ : Ren k l)
      (σ : Substitution Head Operation Effect m w l p x q) :
      (code.rename ρ ν θ).substitute σ = code.substitute (σ.afterRename ρ ν θ) := by
    match code with
    | .returnValue value =>
        simp only [Computation.substitute, Computation.rename, Value.substitute_rename value]
    | .bindNative first body =>
        simp only [Computation.substitute, Computation.rename, Computation.substitute_rename first, Computation.substitute_rename body, Substitution.afterRename_liftNative]
    | .bindValue first body =>
        simp only [Computation.substitute, Computation.rename, Computation.substitute_rename first, Computation.substitute_rename body, Substitution.afterRename_liftValue]
    | .sequenceSigma first body =>
        simp only [Computation.substitute, Computation.rename, Computation.substitute_rename first, Computation.substitute_rename body, Substitution.afterRename_liftNative]
    | .nativeLambda body =>
        simp only [Computation.substitute, Computation.rename, Computation.substitute_rename body, Substitution.afterRename_liftNative]
    | .nativeApply function argument =>
        simp only [Computation.substitute, Computation.rename, Computation.substitute_rename function, Substitution.afterRename_native, subst_rename]
    | .valueLambda body =>
        simp only [Computation.substitute, Computation.rename, Computation.substitute_rename body, Substitution.afterRename_liftValue]
    | .valueApply function argument =>
        simp only [Computation.substitute, Computation.rename, Computation.substitute_rename function, Value.substitute_rename argument]
    | .forceThunk value =>
        simp only [Computation.substitute, Computation.rename, Value.substitute_rename value]
    | .unpackNative value body =>
        simp only [Computation.substitute, Computation.rename, Value.substitute_rename value, Computation.substitute_rename body, Substitution.afterRename_liftNative, Substitution.afterRename_liftValue]
    | .choose left right =>
        simp only [Computation.substitute, Computation.rename, Computation.substitute_rename left, Computation.substitute_rename right]
    | .call operation argument =>
        simp only [Computation.substitute, Computation.rename, Substitution.afterRename_native, subst_rename]
    | .emit effect next =>
        simp only [Computation.substitute, Computation.rename, Computation.substitute_rename next]
    | .letNeed suspended body =>
        simp only [Computation.substitute, Computation.rename, Computation.substitute_rename suspended, Computation.substitute_rename body, Substitution.afterRename_liftNeed]
    | .forceNeed reference => rfl
  termination_by structural code
end

theorem Value.substitute_liftNative_rename {n v k m w l : Nat}
    (value : Value Head Operation Effect n v k)
    (σ : Substitution Head Operation Effect n v k m w l) :
    (value.rename wk idRen idRen).substitute σ.liftNative =
      (value.substitute σ).rename wk idRen idRen := by
  rw [Value.substitute_rename, Value.rename_substitute]
  rfl

theorem Value.substitute_liftValue_rename {n v k m w l : Nat}
    (value : Value Head Operation Effect n v k)
    (σ : Substitution Head Operation Effect n v k m w l) :
    (value.rename idRen wk idRen).substitute σ.liftValue =
      (value.substitute σ).rename idRen wk idRen := by
  rw [Value.substitute_rename, Value.rename_substitute]
  apply congrArg (fun δ => Value.substitute δ value)
  apply Substitution.ext
  · intro i; exact (Presentation.rename_id (σ.native i)).symm
  · intro i; rfl
  · intro i; rfl

theorem Value.substitute_liftNeed_rename {n v k m w l : Nat}
    (value : Value Head Operation Effect n v k)
    (σ : Substitution Head Operation Effect n v k m w l) :
    (value.rename idRen idRen wk).substitute σ.liftNeed =
      (value.substitute σ).rename idRen idRen wk := by
  rw [Value.substitute_rename, Value.rename_substitute]
  apply congrArg (fun δ => Value.substitute δ value)
  apply Substitution.ext
  · intro i; exact (Presentation.rename_id (σ.native i)).symm
  · intro i; rfl
  · intro i; rfl

namespace Substitution

variable {n v k m w l p x q : Nat}

/-- Composition acts on the actual syntax of value replacements. -/
def comp (τ : Substitution Head Operation Effect m w l p x q)
    (σ : Substitution Head Operation Effect n v k m w l) :
    Substitution Head Operation Effect n v k p x q :=
  ⟨subComp τ.native σ.native, fun i => (σ.values i).substitute τ, fun i => τ.needs (σ.needs i)⟩

@[simp] theorem comp_native (τ : Substitution Head Operation Effect m w l p x q)
    (σ : Substitution Head Operation Effect n v k m w l) :
    (τ.comp σ).native = subComp τ.native σ.native := rfl

theorem comp_liftNative (τ : Substitution Head Operation Effect m w l p x q)
    (σ : Substitution Head Operation Effect n v k m w l) :
    τ.liftNative.comp σ.liftNative = (τ.comp σ).liftNative := by
  apply ext
  · intro i; exact liftSub_comp_apply τ.native σ.native i
  · intro i; exact Value.substitute_liftNative_rename (σ.values i) τ
  · intro i; rfl

theorem comp_liftValue (τ : Substitution Head Operation Effect m w l p x q)
    (σ : Substitution Head Operation Effect n v k m w l) :
    τ.liftValue.comp σ.liftValue = (τ.comp σ).liftValue := by
  apply ext
  · intro i; rfl
  · intro i
    exact Fin.cases rfl (fun j => Value.substitute_liftValue_rename (σ.values j) τ) i
  · intro i; rfl

theorem comp_liftNeed (τ : Substitution Head Operation Effect m w l p x q)
    (σ : Substitution Head Operation Effect n v k m w l) :
    τ.liftNeed.comp σ.liftNeed = (τ.comp σ).liftNeed := by
  apply ext
  · intro i; rfl
  · intro i; exact Value.substitute_liftNeed_rename (σ.values i) τ
  · intro i; exact liftRen_comp_apply τ.needs σ.needs i

end Substitution


mutual
  @[simp] theorem Value.substitute_comp {n v k : Nat}
      (value : Value Head Operation Effect n v k) {m w l p x q : Nat}
      (τ : Substitution Head Operation Effect m w l p x q)
      (σ : Substitution Head Operation Effect n v k m w l) :
      (value.substitute σ).substitute τ = value.substitute (τ.comp σ) := by
    match value with
    | .native term => simp only [Value.substitute, Substitution.comp_native, subst_subComp]
    | .variable index => rfl
    | .thunk body => simp only [Value.substitute, Computation.substitute_comp body]
    | .packNative index value =>
        simp only [Value.substitute, Substitution.comp_native, subst_subComp, Value.substitute_comp value]
  termination_by structural value

  @[simp] theorem Computation.substitute_comp {n v k : Nat}
      (code : Computation Head Operation Effect n v k) {m w l p x q : Nat}
      (τ : Substitution Head Operation Effect m w l p x q)
      (σ : Substitution Head Operation Effect n v k m w l) :
      (code.substitute σ).substitute τ = code.substitute (τ.comp σ) := by
    match code with
    | .returnValue value => simp only [Computation.substitute, Value.substitute_comp value]
    | .bindNative first body => simp only [Computation.substitute, Computation.substitute_comp first, Computation.substitute_comp body, Substitution.comp_liftNative]
    | .bindValue first body => simp only [Computation.substitute, Computation.substitute_comp first, Computation.substitute_comp body, Substitution.comp_liftValue]
    | .sequenceSigma first body => simp only [Computation.substitute, Computation.substitute_comp first, Computation.substitute_comp body, Substitution.comp_liftNative]
    | .nativeLambda body => simp only [Computation.substitute, Computation.substitute_comp body, Substitution.comp_liftNative]
    | .nativeApply function argument => simp only [Computation.substitute, Computation.substitute_comp function, Substitution.comp_native, subst_subComp]
    | .valueLambda body => simp only [Computation.substitute, Computation.substitute_comp body, Substitution.comp_liftValue]
    | .valueApply function argument => simp only [Computation.substitute, Computation.substitute_comp function, Value.substitute_comp argument]
    | .forceThunk value => simp only [Computation.substitute, Value.substitute_comp value]
    | .unpackNative value body => simp only [Computation.substitute, Value.substitute_comp value, Computation.substitute_comp body, Substitution.comp_liftNative, Substitution.comp_liftValue]
    | .choose left right => simp only [Computation.substitute, Computation.substitute_comp left, Computation.substitute_comp right]
    | .call operation argument => simp only [Computation.substitute, Substitution.comp_native, subst_subComp]
    | .emit effect next => simp only [Computation.substitute, Computation.substitute_comp next]
    | .letNeed suspended body => simp only [Computation.substitute, Computation.substitute_comp suspended, Computation.substitute_comp body, Substitution.comp_liftNeed]
    | .forceNeed reference => rfl
  termination_by structural code
end

namespace Substitution

variable {n v k m w l p x q : Nat}

@[simp] theorem comp_ids_left (σ : Substitution Head Operation Effect n v k m w l) :
    ids.comp σ = σ := by
  apply ext
  · intro i; exact subst_ids (σ.native i)
  · intro i; exact Value.substitute_ids (σ.values i)
  · intro i; rfl

@[simp] theorem comp_ids_right (σ : Substitution Head Operation Effect n v k m w l) :
    σ.comp ids = σ := by
  rfl

theorem comp_assoc {r y s : Nat} (υ : Substitution Head Operation Effect p x q r y s)
    (τ : Substitution Head Operation Effect m w l p x q)
    (σ : Substitution Head Operation Effect n v k m w l) :
    υ.comp (τ.comp σ) = (υ.comp τ).comp σ := by
  apply ext
  · intro i; exact subst_subComp υ.native τ.native (σ.native i)
  · intro i; exact Value.substitute_comp (σ.values i) υ τ
  · intro i; rfl

def openNative (argument : Tm Head n) :
    Substitution Head Operation Effect (n + 1) v k n v k :=
  ⟨subst0 argument, Value.variable, idRen⟩

def openValue (argument : Value Head Operation Effect n v k) :
    Substitution Head Operation Effect n (v + 1) k n v k :=
  ⟨Presentation.ids, Fin.cases argument Value.variable, idRen⟩

def openNeed (reference : Fin k) :
    Substitution Head Operation Effect n v (k + 1) n v k :=
  ⟨Presentation.ids, Value.variable, Fin.cases reference idRen⟩

theorem liftNative_liftValue (σ : Substitution Head Operation Effect n v k m w l) :
    σ.liftNative.liftValue = σ.liftValue.liftNative := by
  apply ext
  · intro i; rfl
  · intro i
    refine Fin.cases rfl (fun j => ?_) i
    simp only [liftValue, liftNative, Fin.cases_succ, Value.rename_comp]
    rfl
  · intro i; rfl

end Substitution

theorem Value.openNative_rename {n v k : Nat}
    (value : Value Head Operation Effect n v k) (argument : Tm Head n) :
    (value.rename wk idRen idRen).substitute (Substitution.openNative argument) = value := by
  rw [Value.substitute_rename]
  exact Value.substitute_ids value

theorem Value.openValue_rename {n v k : Nat}
    (value argument : Value Head Operation Effect n v k) :
    (value.rename idRen wk idRen).substitute (Substitution.openValue argument) = value := by
  rw [Value.substitute_rename]
  exact Value.substitute_ids value

theorem Value.openNeed_rename {n v k : Nat}
    (value : Value Head Operation Effect n v k) (reference : Fin k) :
    (value.rename idRen idRen wk).substitute (Substitution.openNeed reference) = value := by
  rw [Value.substitute_rename]
  exact Value.substitute_ids value

namespace Substitution

variable {n v k m w l : Nat}

theorem comp_openNative (σ : Substitution Head Operation Effect n v k m w l)
    (argument : Tm Head n) :
    σ.comp (openNative argument) =
      (openNative (subst σ.native argument)).comp σ.liftNative := by
  apply ext
  · intro i
    refine Fin.cases rfl (fun j => ?_) i
    exact (inst0_rename_wk (subst σ.native argument) (σ.native j)).symm
  · intro i; exact (Value.openNative_rename (σ.values i) (subst σ.native argument)).symm
  · intro i; rfl

theorem comp_openValue (σ : Substitution Head Operation Effect n v k m w l)
    (argument : Value Head Operation Effect n v k) :
    σ.comp (openValue argument) = (openValue (argument.substitute σ)).comp σ.liftValue := by
  apply ext
  · intro i; exact (subst_ids (σ.native i)).symm
  · intro i
    exact Fin.cases rfl
      (fun j => (Value.openValue_rename (σ.values j) (argument.substitute σ)).symm) i
  · intro i; rfl

theorem comp_openNeed (σ : Substitution Head Operation Effect n v k m w l)
    (reference : Fin k) :
    σ.comp (openNeed reference) = (openNeed (σ.needs reference)).comp σ.liftNeed := by
  apply ext
  · intro i; exact (subst_ids (σ.native i)).symm
  · intro i; exact (Value.openNeed_rename (σ.values i) (σ.needs reference)).symm
  · intro i; exact Fin.cases rfl (fun _ => rfl) i

end Substitution

namespace Computation

variable {n v k m w l : Nat}

def instantiateNative (argument : Tm Head n)
    (body : Computation Head Operation Effect (n + 1) v k) :
    Computation Head Operation Effect n v k := body.substitute (Substitution.openNative argument)

def instantiateValue (argument : Value Head Operation Effect n v k)
    (body : Computation Head Operation Effect n (v + 1) k) :
    Computation Head Operation Effect n v k := body.substitute (Substitution.openValue argument)

def instantiateNeed (reference : Fin k)
    (body : Computation Head Operation Effect n v (k + 1)) :
    Computation Head Operation Effect n v k := body.substitute (Substitution.openNeed reference)

/-- Open both fields of a native-index/value packet. The supplied value is
already in the outer native scope; it is not captured by the removed binder. -/
def instantiateNativeValue (index : Tm Head n) (value : Value Head Operation Effect n v k)
    (body : Computation Head Operation Effect (n + 1) (v + 1) k) :
    Computation Head Operation Effect n v k :=
  instantiateValue value (instantiateNative index body)

theorem substitute_instantiateNative (σ : Substitution Head Operation Effect n v k m w l)
    (argument : Tm Head n) (body : Computation Head Operation Effect (n + 1) v k) :
    (instantiateNative argument body).substitute σ =
      instantiateNative (subst σ.native argument) (body.substitute σ.liftNative) := by
  simp only [instantiateNative, substitute_comp, Substitution.comp_openNative]

theorem substitute_instantiateValue (σ : Substitution Head Operation Effect n v k m w l)
    (argument : Value Head Operation Effect n v k)
    (body : Computation Head Operation Effect n (v + 1) k) :
    (instantiateValue argument body).substitute σ =
      instantiateValue (argument.substitute σ) (body.substitute σ.liftValue) := by
  simp only [instantiateValue, substitute_comp, Substitution.comp_openValue]

theorem substitute_instantiateNeed (σ : Substitution Head Operation Effect n v k m w l)
    (reference : Fin k) (body : Computation Head Operation Effect n v (k + 1)) :
    (instantiateNeed reference body).substitute σ =
      instantiateNeed (σ.needs reference) (body.substitute σ.liftNeed) := by
  simp only [instantiateNeed, substitute_comp, Substitution.comp_openNeed]

theorem substitute_instantiateNativeValue (σ : Substitution Head Operation Effect n v k m w l)
    (index : Tm Head n) (value : Value Head Operation Effect n v k)
    (body : Computation Head Operation Effect (n + 1) (v + 1) k) :
    (instantiateNativeValue index value body).substitute σ =
      instantiateNativeValue (subst σ.native index) (value.substitute σ)
        (body.substitute σ.liftNative.liftValue) := by
  simp only [instantiateNativeValue, substitute_instantiateValue,
    substitute_instantiateNative, Substitution.liftNative_liftValue]
  rfl

/-- The complete old source is insensitive to the new value environment.
Its native substitution and reference renaming remain the existing operations. -/
theorem substitute_ofScopedNeed {n k : Nat}
    (code : ScopedNeedComputation.Code Head Operation Effect n k) {v m w l : Nat}
    (σ : Substitution Head Operation Effect n v k m w l) :
    (ofScopedNeed code).substitute σ =
      ofScopedNeed ((code.substitute σ.native).renameHandles σ.needs) := by
  induction code generalizing v m w l <;>
    simp_all [ofScopedNeed, substitute, Value.substitute,
      ScopedNeedComputation.Code.substitute, ScopedNeedComputation.Code.renameHandles,
      Substitution.liftNative, Substitution.liftNeed]

end Computation

namespace Examples

/-- One source thunk captures a native term, a first-class value and a Need
reference. Its body is the actual polarized computation grammar. -/
def capturedAt {n v k : Nat} (nativeIndex : Fin n) (valueIndex : Fin v)
    (needIndex : Fin k) : Value Unit Unit Unit n v k :=
  .thunk (.choose (.returnValue (.packNative (.var nativeIndex) (.variable valueIndex)))
    (.forceNeed needIndex))

def captured : Value Unit Unit Unit 1 1 1 := capturedAt 0 0 0

/-- The occurrence to replace crosses both binders of `unpackNative`, then
a fresh Need binder. Its coordinate one is not the newly unpacked value. -/
def crossing : Computation Unit Unit Unit 1 2 1 :=
  .unpackNative (.packNative (.var 0) (.native (.var 0)))
    (.letNeed (.returnValue (.native (.var 0))) (.returnValue (.variable 1)))

def crossedResult (nativeIndex valueIndex needIndex : Fin 2) :
    Computation Unit Unit Unit 1 1 1 :=
  .unpackNative (.packNative (.var 0) (.native (.var 0)))
    (.letNeed (.returnValue (.native (.var 0)))
      (.returnValue (capturedAt nativeIndex valueIndex needIndex)))

theorem opening_retains_all_captured_scopes :
    Computation.instantiateValue captured crossing = crossedResult 1 1 1 := by
  decide

/-- Each wrong result is still a finite, well-scoped source tree. Scopedness
alone does not identify the free binder which the inserted thunk captured. -/
theorem opening_rejects_native_capture :
    Computation.instantiateValue captured crossing ≠ crossedResult 0 1 1 := by
  rw [opening_retains_all_captured_scopes]
  decide

theorem opening_rejects_value_capture :
    Computation.instantiateValue captured crossing ≠ crossedResult 1 0 1 := by
  rw [opening_retains_all_captured_scopes]
  decide

theorem opening_rejects_need_capture :
    Computation.instantiateValue captured crossing ≠ crossedResult 1 1 0 := by
  rw [opening_retains_all_captured_scopes]
  decide

/-- The new native index is substituted into native syntax; the accompanying
closure retains its independently captured outer native variable and handle. -/
def packetBody : Computation Unit Unit Unit 2 2 1 :=
  .returnValue (.packNative (.var 0) (.variable 0))

theorem packet_opening_keeps_outer_capture :
    Computation.instantiateNativeValue (.var 0) captured packetBody =
      .returnValue (.packNative (.var 0) captured) := by
  decide

theorem packet_opening_does_not_replace_closure_by_index :
    Computation.instantiateNativeValue (.var 0) captured packetBody ≠
      .returnValue (.packNative (.var 0) (.native (.var 0))) := by
  rw [packet_opening_keeps_outer_capture]
  decide

end Examples

#print axioms Value.substitute_ids
#print axioms Computation.substitute_ids
#print axioms Value.substitute_ofRenaming
#print axioms Computation.substitute_ofRenaming
#print axioms Value.rename_substitute
#print axioms Computation.rename_substitute
#print axioms Value.substitute_rename
#print axioms Computation.substitute_rename
#print axioms Value.substitute_comp
#print axioms Computation.substitute_comp
#print axioms Substitution.comp_assoc
#print axioms Computation.substitute_instantiateNative
#print axioms Computation.substitute_instantiateValue
#print axioms Computation.substitute_instantiateNeed
#print axioms Computation.substitute_instantiateNativeValue
#print axioms Computation.substitute_ofScopedNeed
#print axioms Examples.opening_retains_all_captured_scopes
#print axioms Examples.opening_rejects_native_capture
#print axioms Examples.opening_rejects_value_capture
#print axioms Examples.opening_rejects_need_capture
#print axioms Examples.packet_opening_keeps_outer_capture
#print axioms Examples.packet_opening_does_not_replace_closure_by_index

end PolarizedNeed
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
