import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedNeedComputation

/-!
# Native-indexed polarized source syntax

Values and computations are mutually reified data. Native mathematical
variables, first-class value variables, and owned suspension references have
separate scopes. An ordinary thunk contains source code, not a Lean function
or a saved world. Computation functions are distinct from native `Tm.lam`.

This is a candidate interface, not a change to a language's surface defaults.
Its dependent indices are native terms. A native-index/value pair can retain
an index-dependent closure; native types do not thereby acquire dependency on
arbitrary closures. Native payloads are represented syntax, not a claim of
normalization or logical admission.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeed

mutual
  inductive Value (Head Operation Effect : Type) : Nat → Nat → Nat → Type where
    | native {n v k : Nat} (term : Tm Head n) : Value Head Operation Effect n v k
    | variable {n v k : Nat} (index : Fin v) : Value Head Operation Effect n v k
    | thunk {n v k : Nat} (body : Computation Head Operation Effect n v k) :
        Value Head Operation Effect n v k
    | packNative {n v k : Nat} (index : Tm Head n)
        (value : Value Head Operation Effect n v k) : Value Head Operation Effect n v k
    deriving Repr, DecidableEq

  inductive Computation (Head Operation Effect : Type) : Nat → Nat → Nat → Type where
    | returnValue {n v k : Nat} (value : Value Head Operation Effect n v k) :
        Computation Head Operation Effect n v k
    | bindNative {n v k : Nat} (first : Computation Head Operation Effect n v k)
        (body : Computation Head Operation Effect (n + 1) v k) :
        Computation Head Operation Effect n v k
    | bindValue {n v k : Nat} (first : Computation Head Operation Effect n v k)
        (body : Computation Head Operation Effect n (v + 1) k) :
        Computation Head Operation Effect n v k
    | sequenceSigma {n v k : Nat} (first : Computation Head Operation Effect n v k)
        (body : Computation Head Operation Effect (n + 1) v k) :
        Computation Head Operation Effect n v k
    | nativeLambda {n v k : Nat} (body : Computation Head Operation Effect (n + 1) v k) :
        Computation Head Operation Effect n v k
    | nativeApply {n v k : Nat} (function : Computation Head Operation Effect n v k)
        (argument : Tm Head n) : Computation Head Operation Effect n v k
    | valueLambda {n v k : Nat} (body : Computation Head Operation Effect n (v + 1) k) :
        Computation Head Operation Effect n v k
    | valueApply {n v k : Nat} (function : Computation Head Operation Effect n v k)
        (argument : Value Head Operation Effect n v k) : Computation Head Operation Effect n v k
    | forceThunk {n v k : Nat} (value : Value Head Operation Effect n v k) :
        Computation Head Operation Effect n v k
    | unpackNative {n v k : Nat} (value : Value Head Operation Effect n v k)
        (body : Computation Head Operation Effect (n + 1) (v + 1) k) :
        Computation Head Operation Effect n v k
    | choose {n v k : Nat} (left right : Computation Head Operation Effect n v k) :
        Computation Head Operation Effect n v k
    | call {n v k : Nat} (operation : Operation) (argument : Tm Head n) :
        Computation Head Operation Effect n v k
    | emit {n v k : Nat} (effect : Effect) (next : Computation Head Operation Effect n v k) :
        Computation Head Operation Effect n v k
    | letNeed {n v k : Nat} (suspended : Computation Head Operation Effect n v k)
        (body : Computation Head Operation Effect n v (k + 1)) :
        Computation Head Operation Effect n v k
    | forceNeed {n v k : Nat} (reference : Fin k) : Computation Head Operation Effect n v k
    deriving Repr, DecidableEq
end

variable {Head Operation Effect : Type}

mutual
  /-- Simultaneous renaming preserves all three binding scopes. -/
  def Value.rename {n v k m w l : Nat} (ρ : Ren n m) (ν : Ren v w) (θ : Ren k l) :
      Value Head Operation Effect n v k → Value Head Operation Effect m w l
    | .native term => .native (Presentation.rename ρ term)
    | .variable index => .variable (ν index)
    | .thunk body => .thunk (Computation.rename ρ ν θ body)
    | .packNative index value =>
        .packNative (Presentation.rename ρ index) (Value.rename ρ ν θ value)

  def Computation.rename {n v k m w l : Nat} (ρ : Ren n m) (ν : Ren v w) (θ : Ren k l) :
      Computation Head Operation Effect n v k → Computation Head Operation Effect m w l
    | .returnValue value => .returnValue (Value.rename ρ ν θ value)
    | .bindNative first body =>
        .bindNative (Computation.rename ρ ν θ first) (Computation.rename (liftRen ρ) ν θ body)
    | .bindValue first body =>
        .bindValue (Computation.rename ρ ν θ first) (Computation.rename ρ (liftRen ν) θ body)
    | .sequenceSigma first body =>
        .sequenceSigma (Computation.rename ρ ν θ first)
          (Computation.rename (liftRen ρ) ν θ body)
    | .nativeLambda body => .nativeLambda (Computation.rename (liftRen ρ) ν θ body)
    | .nativeApply function argument =>
        .nativeApply (Computation.rename ρ ν θ function) (Presentation.rename ρ argument)
    | .valueLambda body => .valueLambda (Computation.rename ρ (liftRen ν) θ body)
    | .valueApply function argument =>
        .valueApply (Computation.rename ρ ν θ function) (Value.rename ρ ν θ argument)
    | .forceThunk value => .forceThunk (Value.rename ρ ν θ value)
    | .unpackNative value body =>
        .unpackNative (Value.rename ρ ν θ value)
          (Computation.rename (liftRen ρ) (liftRen ν) θ body)
    | .choose left right =>
        .choose (Computation.rename ρ ν θ left) (Computation.rename ρ ν θ right)
    | .call operation argument => .call operation (Presentation.rename ρ argument)
    | .emit effect next => .emit effect (Computation.rename ρ ν θ next)
    | .letNeed suspended body =>
        .letNeed (Computation.rename ρ ν θ suspended)
          (Computation.rename ρ ν (liftRen θ) body)
    | .forceNeed reference => .forceNeed (θ reference)
end

mutual
  @[simp] theorem Value.rename_id {n v k : Nat} (value : Value Head Operation Effect n v k) :
      value.rename idRen idRen idRen = value := by
    match value with
    | .native term => simp only [Value.rename, Presentation.rename_id]
    | .variable index => rfl
    | .thunk body => simp only [Value.rename, Computation.rename_id body]
    | .packNative index value => simp only [Value.rename, Presentation.rename_id, Value.rename_id value]
  termination_by structural value

  @[simp] theorem Computation.rename_id {n v k : Nat}
      (code : Computation Head Operation Effect n v k) :
      code.rename idRen idRen idRen = code := by
    match code with
    | .returnValue value => simp only [Computation.rename, Value.rename_id value]
    | .bindNative first body => simp only [Computation.rename, liftRen_id, Computation.rename_id first, Computation.rename_id body]
    | .bindValue first body => simp only [Computation.rename, liftRen_id, Computation.rename_id first, Computation.rename_id body]
    | .sequenceSigma first body => simp only [Computation.rename, liftRen_id, Computation.rename_id first, Computation.rename_id body]
    | .nativeLambda body => simp only [Computation.rename, liftRen_id, Computation.rename_id body]
    | .nativeApply function argument => simp only [Computation.rename, Computation.rename_id function, Presentation.rename_id]
    | .valueLambda body => simp only [Computation.rename, liftRen_id, Computation.rename_id body]
    | .valueApply function argument => simp only [Computation.rename, Computation.rename_id function, Value.rename_id argument]
    | .forceThunk value => simp only [Computation.rename, Value.rename_id value]
    | .unpackNative value body => simp only [Computation.rename, liftRen_id, Value.rename_id value, Computation.rename_id body]
    | .choose left right => simp only [Computation.rename, Computation.rename_id left, Computation.rename_id right]
    | .call operation argument => simp only [Computation.rename, Presentation.rename_id]
    | .emit effect next => simp only [Computation.rename, Computation.rename_id next]
    | .letNeed suspended body => simp only [Computation.rename, liftRen_id, Computation.rename_id suspended, Computation.rename_id body]
    | .forceNeed reference => rfl
  termination_by structural code
end

private theorem liftRen_composition {n m p : Nat} (ρ : Ren m p) (ξ : Ren n m) :
    (fun index => liftRen ρ (liftRen ξ index)) = liftRen (fun index => ρ (ξ index)) := by
  funext index
  exact liftRen_comp_apply ρ ξ index

mutual
  @[simp] theorem Value.rename_comp {n v k m w l p x q : Nat}
      (ρ : Ren m p) (ν : Ren w x) (θ : Ren l q)
      (ξ : Ren n m) (μ : Ren v w) (ψ : Ren k l)
      (value : Value Head Operation Effect n v k) :
      (value.rename ξ μ ψ).rename ρ ν θ =
        value.rename (fun i => ρ (ξ i)) (fun i => ν (μ i)) (fun i => θ (ψ i)) := by
    match value with
    | .native term => simp only [Value.rename, Presentation.rename_comp]
    | .variable index => rfl
    | .thunk body => simp only [Value.rename, Computation.rename_comp ρ ν θ ξ μ ψ body]
    | .packNative index value =>
        simp only [Value.rename, Presentation.rename_comp, Value.rename_comp ρ ν θ ξ μ ψ value]
  termination_by structural value

  @[simp] theorem Computation.rename_comp {n v k m w l p x q : Nat}
      (ρ : Ren m p) (ν : Ren w x) (θ : Ren l q)
      (ξ : Ren n m) (μ : Ren v w) (ψ : Ren k l)
      (code : Computation Head Operation Effect n v k) :
      (code.rename ξ μ ψ).rename ρ ν θ =
        code.rename (fun i => ρ (ξ i)) (fun i => ν (μ i)) (fun i => θ (ψ i)) := by
    match code with
    | .returnValue value => simp only [Computation.rename, Value.rename_comp ρ ν θ ξ μ ψ value]
    | .bindNative first body =>
        simp only [Computation.rename, Computation.rename_comp ρ ν θ ξ μ ψ first,
          Computation.rename_comp (liftRen ρ) ν θ (liftRen ξ) μ ψ body, liftRen_composition]
    | .bindValue first body =>
        simp only [Computation.rename, Computation.rename_comp ρ ν θ ξ μ ψ first,
          Computation.rename_comp ρ (liftRen ν) θ ξ (liftRen μ) ψ body, liftRen_composition]
    | .sequenceSigma first body =>
        simp only [Computation.rename, Computation.rename_comp ρ ν θ ξ μ ψ first,
          Computation.rename_comp (liftRen ρ) ν θ (liftRen ξ) μ ψ body, liftRen_composition]
    | .nativeLambda body =>
        simp only [Computation.rename, Computation.rename_comp (liftRen ρ) ν θ (liftRen ξ) μ ψ body, liftRen_composition]
    | .nativeApply function argument =>
        simp only [Computation.rename, Computation.rename_comp ρ ν θ ξ μ ψ function, Presentation.rename_comp]
    | .valueLambda body =>
        simp only [Computation.rename, Computation.rename_comp ρ (liftRen ν) θ ξ (liftRen μ) ψ body, liftRen_composition]
    | .valueApply function argument =>
        simp only [Computation.rename, Computation.rename_comp ρ ν θ ξ μ ψ function, Value.rename_comp ρ ν θ ξ μ ψ argument]
    | .forceThunk value => simp only [Computation.rename, Value.rename_comp ρ ν θ ξ μ ψ value]
    | .unpackNative value body =>
        simp only [Computation.rename, Value.rename_comp ρ ν θ ξ μ ψ value,
          Computation.rename_comp (liftRen ρ) (liftRen ν) θ (liftRen ξ) (liftRen μ) ψ body,
          liftRen_composition]
    | .choose left right => simp only [Computation.rename, Computation.rename_comp ρ ν θ ξ μ ψ left, Computation.rename_comp ρ ν θ ξ μ ψ right]
    | .call operation argument => simp only [Computation.rename, Presentation.rename_comp]
    | .emit effect next => simp only [Computation.rename, Computation.rename_comp ρ ν θ ξ μ ψ next]
    | .letNeed suspended body =>
        simp only [Computation.rename, Computation.rename_comp ρ ν θ ξ μ ψ suspended,
          Computation.rename_comp ρ ν (liftRen θ) ξ μ (liftRen ψ) body, liftRen_composition]
    | .forceNeed reference => rfl
  termination_by structural code
end

/-- The old native-returning source embeds constructor by constructor. Its
dependent native pairing is not reinterpreted as a closure/index packet. -/
def Computation.ofScopedNeed {n v k : Nat} :
    ScopedNeedComputation.Code Head Operation Effect n k → Computation Head Operation Effect n v k
  | .returnValue term => .returnValue (.native term)
  | .sequence first body => .bindNative (ofScopedNeed first) (ofScopedNeed body)
  | .sequenceSigma first body => .sequenceSigma (ofScopedNeed first) (ofScopedNeed body)
  | .choose left right => .choose (ofScopedNeed left) (ofScopedNeed right)
  | .call operation argument => .call operation argument
  | .emit effect next => .emit effect (ofScopedNeed next)
  | .letNeed suspended body => .letNeed (ofScopedNeed suspended) (ofScopedNeed body)
  | .force reference => .forceNeed reference

/-- Partial source retraction. New first-class constructs are not erased into
old code; they are outside this image. -/
def Computation.toScopedNeed? {n v k : Nat} :
    Computation Head Operation Effect n v k → Option (ScopedNeedComputation.Code Head Operation Effect n k)
  | .returnValue (.native term) => some (.returnValue term)
  | .bindNative first body => do
      return .sequence (← first.toScopedNeed?) (← body.toScopedNeed?)
  | .sequenceSigma first body => do
      return .sequenceSigma (← first.toScopedNeed?) (← body.toScopedNeed?)
  | .choose left right => do return .choose (← left.toScopedNeed?) (← right.toScopedNeed?)
  | .call operation argument => some (.call operation argument)
  | .emit effect next => do return .emit effect (← next.toScopedNeed?)
  | .letNeed suspended body => do return .letNeed (← suspended.toScopedNeed?) (← body.toScopedNeed?)
  | .forceNeed reference => some (.force reference)
  | _ => none

@[simp] theorem Computation.toScopedNeed?_ofScopedNeed {n v k : Nat}
    (code : ScopedNeedComputation.Code Head Operation Effect n k) :
    (ofScopedNeed (v := v) code).toScopedNeed? = some code := by
  induction code <;> simp_all [ofScopedNeed, toScopedNeed?]

theorem Computation.ofScopedNeed_injective {n v k : Nat} :
    Function.Injective (ofScopedNeed (Head := Head) (Operation := Operation) (Effect := Effect)
      (n := n) (v := v) (k := k)) := by
  intro left right equal
  have projected := congrArg toScopedNeed? equal
  simpa only [toScopedNeed?_ofScopedNeed, Option.some.injEq] using projected

theorem Computation.rename_ofScopedNeed {n v k m w l : Nat}
    (ρ : Ren n m) (ν : Ren v w) (θ : Ren k l)
    (code : ScopedNeedComputation.Code Head Operation Effect n k) :
    (ofScopedNeed (v := v) code).rename ρ ν θ =
      ofScopedNeed (v := w) ((code.rename ρ).renameHandles θ) := by
  induction code generalizing m w l <;>
    simp_all [ofScopedNeed, rename, Value.rename,
      ScopedNeedComputation.Code.rename, ScopedNeedComputation.Code.renameHandles]

/-- A genuinely higher-order source term: apply a thunked function to a
thunked argument, with no host-language function standing for its body. -/
def applyThunked {Head Operation Effect : Type} {n v k : Nat} :
    Computation Head Operation Effect n v k :=
  .valueLambda (.valueLambda
    (.valueApply (.forceThunk (.variable 1)) (.variable 0)))

theorem applyThunked_outside_old_image {n v k : Nat}
    (code : ScopedNeedComputation.Code Head Operation Effect n k) :
    Computation.ofScopedNeed (v := v) code ≠ (applyThunked : Computation Head Operation Effect n v k) := by
  intro equal
  have projected := congrArg Computation.toScopedNeed? equal
  simp [applyThunked, Computation.toScopedNeed?] at projected

#print axioms Value.rename_id
#print axioms Computation.rename_id
#print axioms Value.rename_comp
#print axioms Computation.rename_comp
#print axioms Computation.ofScopedNeed_injective
#print axioms Computation.rename_ofScopedNeed
#print axioms applyThunked_outside_old_image

end PolarizedNeed
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
