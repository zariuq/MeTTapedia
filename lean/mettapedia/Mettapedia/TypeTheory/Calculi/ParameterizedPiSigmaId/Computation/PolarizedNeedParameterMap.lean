import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedMachine
import Mettapedia.Machines.BranchLocalNeed.Representation

/-!
# Parameter maps through polarized computations and captured values

Heads and effect labels are mapped throughout actual source syntax, finite
lexical environments, computation-function answers and Need-origin closures.
The existing representation map then transports heaps, caches and receipts.
Native/value/Need variable indices and machine-owned identities stay fixed.
This is parameter instantiation, not a source elaborator or a typing policy.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.PolarizedNeedParameterMap

open Mettapedia.Machines.BranchLocalNeed NeedReference PolarizedNeed PolarizedNeedMachine

variable {H H' O E E' F N : Type} {m : Nat}

mutual
  def value (heads : H → H') (effects : E → E') {n v k : Nat} :
      Value H O E n v k → Value H' O E' n v k
    | .native term => .native (term.mapHead heads)
    | .variable index => .variable index
    | .thunk body => .thunk (code heads effects body)
    | .packNative index inner => .packNative (index.mapHead heads) (value heads effects inner)

  def code (heads : H → H') (effects : E → E') {n v k : Nat} :
      Computation H O E n v k → Computation H' O E' n v k
    | .returnValue inner => .returnValue (value heads effects inner)
    | .bindNative first body => .bindNative (code heads effects first) (code heads effects body)
    | .bindValue first body => .bindValue (code heads effects first) (code heads effects body)
    | .sequenceSigma first body => .sequenceSigma (code heads effects first) (code heads effects body)
    | .nativeLambda body => .nativeLambda (code heads effects body)
    | .nativeApply function argument => .nativeApply (code heads effects function) (argument.mapHead heads)
    | .valueLambda body => .valueLambda (code heads effects body)
    | .valueApply function argument => .valueApply (code heads effects function) (value heads effects argument)
    | .forceThunk inner => .forceThunk (value heads effects inner)
    | .unpackNative inner body => .unpackNative (value heads effects inner) (code heads effects body)
    | .choose left right => .choose (code heads effects left) (code heads effects right)
    | .call operation argument => .call operation (argument.mapHead heads)
    | .emit effect next => .emit (effects effect) (code heads effects next)
    | .letNeed suspended body => .letNeed (code heads effects suspended) (code heads effects body)
    | .forceNeed reference => .forceNeed reference
end

def runtimeValue (heads : H → H') (effects : E → E') :
    RuntimeValue H O E m → RuntimeValue H' O E' m
  | .native term => .native (term.mapHead heads)
  | .thunk body native values needs =>
      .thunk (code heads effects body) (fun i => (native i).mapHead heads)
        (fun i => runtimeValue heads effects (values i)) needs
  | .packNative index inner => .packNative (index.mapHead heads) (runtimeValue heads effects inner)

def captured (heads : H → H') (effects : E → E') {dn dv dk : Nat}
    (body : Captured H O E m dn dv dk) : Captured H' O E' m dn dv dk :=
  ⟨body.n, body.v, body.k, code heads effects body.code,
    fun i => (body.native i).mapHead heads, fun i => runtimeValue heads effects (body.values i), body.needs⟩

def answer (heads : H → H') (effects : E → E') : Answer H O E m → Answer H' O E' m
  | .returned inner => .returned (runtimeValue heads effects inner)
  | .nativeFunction body => .nativeFunction (captured heads effects body)
  | .valueFunction body => .valueFunction (captured heads effects body)

def outcome (heads : H → H') (effects : E → E') : Outcome H O E F N m → Outcome H' O E' F N m
  | .value result => .value (answer heads effects result)
  | .stableFault fault => .stableFault fault
  | .retryableFault reason => .retryableFault reason

def kont (heads : H → H') (effects : E → E') : Kont H O E m → Kont H' O E' m
  | .done => .done
  | .pair first rest => .pair (first.mapHead heads) (kont heads effects rest)
  | .nativeApply argument rest => .nativeApply (argument.mapHead heads) (kont heads effects rest)
  | .valueApply argument rest => .valueApply (runtimeValue heads effects argument) (kont heads effects rest)

def resume (heads : H → H') (effects : E → E') : Resume H O E m → Resume H' O E' m
  | .finish continuation => .finish (kont heads effects continuation)
  | .bindNative body continuation => .bindNative (captured heads effects body) (kont heads effects continuation)
  | .bindValue body continuation => .bindValue (captured heads effects body) (kont heads effects continuation)
  | .bindSigma body continuation => .bindSigma (captured heads effects body) (kont heads effects continuation)
  | .bindNeed body continuation => .bindNeed (captured heads effects body) (kont heads effects continuation)

def state (heads : H → H') (effects : E → E') : Local H O E F N m → Local H' O E' F N m
  | .evaluate body continuation => .evaluate (captured heads effects body) (kont heads effects continuation)
  | .demand cell consumer => .demand cell (resume heads effects consumer)
  | .complete result => .complete (outcome heads effects result)

def mapping (heads : H → H') (effects : E → E') : NeedRepresentation.Mapping
    (Closure H O E m) (Local H O E F N m) (Resume H O E m) Rule (Answer H O E m) F (Fault N) E
    (Closure H' O E' m) (Local H' O E' F N m) (Resume H' O E' m) Rule (Answer H' O E' m) F (Fault N) E' where
  origin := captured heads effects
  state := state heads effects
  resume := resume heads effects
  rule := id
  value := answer heads effects
  stableFault := id
  retryableFault := id
  effect := effects

@[simp] theorem mapping_retry (heads : H → H') (effects : E → E')
    (reason : RetryReason (Fault N)) :
    (mapping (O := O) (F := F) (m := m) heads effects).mapRetry reason = reason := by
  cases reason <;> rfl

@[simp] theorem mapping_outcome (heads : H → H') (effects : E → E')
    (result : Outcome H O E F N m) :
    (mapping heads effects).mapOutcome result = outcome heads effects result := by
  cases result with
  | value inner => rfl
  | stableFault fault => rfl
  | retryableFault reason => exact congrArg Produced.retryableFault (mapping_retry heads effects reason)

@[simp] theorem capture_value (heads : H → H') (effects : E → E') {n v k : Nat}
    (native : Sub H n m) (values : Fin v → RuntimeValue H O E m) (needs : Fin k → CellId)
    (source : Value H O E n v k) :
    captureValue (fun i => (native i).mapHead heads)
      (fun i => runtimeValue heads effects (values i)) needs (value heads effects source) =
    runtimeValue heads effects (captureValue native values needs source) := by
  match source with
  | .native term => simp only [value, captureValue, runtimeValue, Tm.mapHead_subst]
  | .variable index => rfl
  | .thunk body => rfl
  | .packNative index inner =>
      simp only [value, captureValue, runtimeValue, Tm.mapHead_subst, capture_value heads effects native values needs inner]
termination_by structural source

@[simp] theorem captured_native_open (heads : H → H') (effects : E → E')
    (body : NativeBody H O E m) (argument : Tm H m) :
    NativeBody.open (captured heads effects body) (argument.mapHead heads) =
      captured heads effects (body.open argument) := by
  unfold captured NativeBody.open
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

@[simp] theorem captured_value_open (heads : H → H') (effects : E → E')
    (body : ValueBody H O E m) (argument : RuntimeValue H O E m) :
    ValueBody.open (captured heads effects body) (runtimeValue heads effects argument) =
      captured heads effects (body.open argument) := by
  unfold captured ValueBody.open
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

@[simp] theorem captured_need_open (heads : H → H') (effects : E → E')
    (body : NeedBody H O E m) (cell : CellId) :
    NeedBody.open (captured heads effects body) cell = captured heads effects (body.open cell) := rfl

@[simp] theorem captured_pair_open (heads : H → H') (effects : E → E')
    (body : PairBody H O E m) (index : Tm H m) (inner : RuntimeValue H O E m) :
    PairBody.open (captured heads effects body) (index.mapHead heads) (runtimeValue heads effects inner) =
      captured heads effects (body.open index inner) := by
  unfold captured PairBody.open
  congr 1 <;> funext i <;> refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem finish_outcome (heads : H → H') (effects : E → E')
    (result : Outcome H O E F N m) (continuation : Kont H O E m) :
    finish (outcome heads effects result) (kont heads effects continuation) =
      outcome heads effects (finish result continuation) := by
  induction continuation generalizing result with
  | done => rfl
  | pair first rest ih =>
      cases result with
      | value result =>
          cases result with
          | returned inner =>
              cases inner with
              | native term => exact ih (.value (.returned (.native (.pair first term))))
              | thunk body native values needs => rfl
              | packNative index value => rfl
          | nativeFunction body => rfl
          | valueFunction body => rfl
      | stableFault fault => rfl
      | retryableFault reason => rfl
  | nativeApply argument rest ih => cases result <;> rfl
  | valueApply argument rest ih => cases result <;> rfl

theorem deliver_outcome (heads : H → H') (effects : E → E')
    (result : Outcome H O E F N m) (continuation : Kont H O E m) :
    deliver (outcome heads effects result) (kont heads effects continuation) =
      state heads effects (deliver result continuation) := by
  induction continuation generalizing result with
  | done => rfl
  | pair first rest ih =>
      cases result with
      | value result =>
          cases result with
          | returned inner =>
              cases inner with
              | native term => exact ih (.value (.returned (.native (.pair first term))))
              | thunk body native values needs => rfl
              | packNative index value => rfl
          | nativeFunction body => rfl
          | valueFunction body => rfl
      | stableFault fault => rfl
      | retryableFault reason => rfl
  | nativeApply argument rest ih =>
      cases result with
      | value result => cases result <;> simp [outcome, answer, kont, deliver, state, captured_native_open]
      | stableFault fault => rfl
      | retryableFault reason => rfl
  | valueApply argument rest ih =>
      cases result with
      | value result => cases result <;> simp [outcome, answer, kont, deliver, state, captured_value_open]
      | stableFault fault => rfl
      | retryableFault reason => rfl

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.PolarizedNeedParameterMap
