import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedMachine

/-!
# Independent natural semantics of first-class owned suspensions

The proof-relevant source judgments inspect source constructors and heap data,
not machine controls, actions, steps or bounded execution. Lexical capture and
opening reuse the actual source representation. Function applications evaluate
the function and then its captured body; ordinary force uses the current
world. Shared force selects an occurrence, claims its cell and finalizes
against the current owned cache, retaining faults and effects.

These rules include raw polarity mismatches and malformed supplied heaps.
A failed source computation is an outcome, not a false logical judgment.
Finite derivations alone establish neither normalization nor adequacy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeedNaturalSemantics

open PrimeNeedReference PolarizedNeedMachine
open PolarizedNeed (Value Computation)

variable {Head Operation Effect StableFault NativeFault : Type} {n m v k : Nat}

/-- Distinct occurrences are retained even when their source bodies coincide. -/
inductive Selection : Closure Head Operation Effect m → Nat → Rule →
    Closure Head Operation Effect m → Type where
  | entry {n v k : Nat} {code : Computation Head Operation Effect n v k}
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m}
      {needs : Fin k → CellId} (notChoice : ∀ left right, code ≠ .choose left right) :
      Selection ⟨n, v, k, code, native, values, needs⟩ 0 .entry
        ⟨n, v, k, code, native, values, needs⟩
  | left {n v k : Nat} (left right : Computation Head Operation Effect n v k)
      (native : Sub Head n m) (values : Fin v → RuntimeValue Head Operation Effect m) (needs : Fin k → CellId) :
      Selection ⟨n, v, k, .choose left right, native, values, needs⟩ 0 .left
        ⟨n, v, k, left, native, values, needs⟩
  | right {n v k : Nat} (left right : Computation Head Operation Effect n v k)
      (native : Sub Head n m) (values : Fin v → RuntimeValue Head Operation Effect m) (needs : Fin k → CellId) :
      Selection ⟨n, v, k, .choose left right, native, values, needs⟩ 1 .right
        ⟨n, v, k, right, native, values, needs⟩

def enterWorld (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (cell : CellId) (origin : Closure Head Operation Effect m) (position : Nat) (rule : Rule) :
    NeedWorld Head Operation Effect StableFault NativeFault m :=
  let owner := world.nextEvaluator
  let advanced := { world with nextEvaluator := owner + 1 }
  let claimed := (advanced.fork position).setKnownCache cell ⟨origin, .suspended⟩ (.evaluating owner)
  let entered := (claimed.record (.evaluate cell owner)).1
  (entered.record (.chooseRule cell rule)).1

/-- A native pair demands a returned native second component, not a function
answer or a returned ordinary thunk. -/
def pairOutcome (first : Tm Head m) : Outcome Head Operation Effect StableFault NativeFault m →
    Outcome Head Operation Effect StableFault NativeFault m
  | .value (.returned (.native second)) => .value (.returned (.native (.pair first second)))
  | .value _ => .retryableFault (.domain .expectedNativeValue)
  | .stableFault fault => .stableFault fault
  | .retryableFault reason => .retryableFault reason

/-- Source propagation records which fault outcome is being propagated. -/
inductive FaultOutcome : Outcome Head Operation Effect StableFault NativeFault m → Type where
  | stableFault (fault : StableFault) : FaultOutcome (.stableFault fault)
  | retryableFault (reason : RetryReason (Fault NativeFault)) : FaultOutcome (.retryableFault reason)

def retryResult (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (cell : CellId) (reason : RetryReason (Fault NativeFault)) :
    Outcome Head Operation Effect StableFault NativeFault m × NeedWorld Head Operation Effect StableFault NativeFault m :=
  (.retryableFault reason, (world.record (.retry cell reason)).1)

def allocationFailure (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
    Outcome Head Operation Effect StableFault NativeFault m × NeedWorld Head Operation Effect StableFault NativeFault m :=
  retryResult world (world.freshCell 0) (.allocationCollision (world.freshCell 0))

/-- Finalization checks current ownership; retry restores suspension without
rolling back any earlier receipts. -/
def finalize (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (cell : CellId) (owner : EvaluatorId) (outcome : Outcome Head Operation Effect StableFault NativeFault m) :
    Outcome Head Operation Effect StableFault NativeFault m × NeedWorld Head Operation Effect StableFault NativeFault m :=
  match world.heap.lookup cell with
  | none => retryResult world cell (.outOfScope cell)
  | some record =>
      match record.cache with
      | .evaluating actual =>
          if actual = owner then
            let cache : Cache (Answer Head Operation Effect m) StableFault :=
              match outcome with
              | .value answer => .value answer
              | .stableFault fault => .stableFault fault
              | .retryableFault _ => .suspended
            let completed := world.setKnownCache cell record cache
            match outcome with
            | .retryableFault reason => retryResult completed cell reason
            | _ => (outcome, (completed.record (.observe cell outcome)).1)
          else retryResult world cell (.ownershipLost cell owner actual)
      | _ => retryResult world cell (.ownershipLost cell owner 0)

mutual

inductive Eval
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault) :
    Closure Head Operation Effect m → NeedWorld Head Operation Effect StableFault NativeFault m →
      Outcome Head Operation Effect StableFault NativeFault m →
        NeedWorld Head Operation Effect StableFault NativeFault m → Type where
  | returnValue {n v k : Nat} (value : Value Head Operation Effect n v k)
      (native : Sub Head n m) (values : Fin v → RuntimeValue Head Operation Effect m) (needs : Fin k → CellId)
      (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
      Eval primitive ⟨n, v, k, .returnValue value, native, values, needs⟩ world
        (.value (.returned (captureValue native values needs value))) world
  | nativeLambda {n v k : Nat} (body : Computation Head Operation Effect (n + 1) v k)
      (native : Sub Head n m) (values : Fin v → RuntimeValue Head Operation Effect m) (needs : Fin k → CellId)
      (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
      Eval primitive ⟨n, v, k, .nativeLambda body, native, values, needs⟩ world
        (.value (.nativeFunction ⟨n, v, k, body, native, values, needs⟩)) world
  | valueLambda {n v k : Nat} (body : Computation Head Operation Effect n (v + 1) k)
      (native : Sub Head n m) (values : Fin v → RuntimeValue Head Operation Effect m) (needs : Fin k → CellId)
      (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
      Eval primitive ⟨n, v, k, .valueLambda body, native, values, needs⟩ world
        (.value (.valueFunction ⟨n, v, k, body, native, values, needs⟩)) world
  | call {n v k : Nat} (operation : Operation) (argument : Tm Head n)
      (native : Sub Head n m) (values : Fin v → RuntimeValue Head Operation Effect m) (needs : Fin k → CellId)
      (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
      Eval primitive ⟨n, v, k, .call operation argument, native, values, needs⟩ world
        (liftOutcome (primitive operation (subst native argument))) world
  | emit {n v k : Nat} (effect : Effect) {next : Computation Head Operation Effect n v k}
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {outcome : Outcome Head Operation Effect StableFault NativeFault m} :
      Eval primitive ⟨n, v, k, next, native, values, needs⟩ (world.record (.effect effect)).1 outcome final →
      Eval primitive ⟨n, v, k, .emit effect next, native, values, needs⟩ world outcome final
  | forceNeed {n v k : Nat} (reference : Fin k)
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {outcome : Outcome Head Operation Effect StableFault NativeFault m} :
      Force primitive (needs reference) world outcome final →
      Eval primitive ⟨n, v, k, .forceNeed reference, native, values, needs⟩ world outcome final
  | nativeApply {n v k : Nat} {function : Computation Head Operation Effect n v k} (argument : Tm Head n)
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      {world selected final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {body : NativeBody Head Operation Effect m} {outcome : Outcome Head Operation Effect StableFault NativeFault m} :
      Eval primitive ⟨n, v, k, function, native, values, needs⟩ world (.value (.nativeFunction body)) selected →
      Eval primitive (body.open (subst native argument)) selected outcome final →
      Eval primitive ⟨n, v, k, .nativeApply function argument, native, values, needs⟩ world outcome final
  | nativeApplyMismatch {n v k : Nat} {function : Computation Head Operation Effect n v k} (argument : Tm Head n)
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      {world final : NeedWorld Head Operation Effect StableFault NativeFault m} {answer : Answer Head Operation Effect m} :
      Eval primitive ⟨n, v, k, function, native, values, needs⟩ world (.value answer) final →
      (∀ body, answer ≠ .nativeFunction body) →
      Eval primitive ⟨n, v, k, .nativeApply function argument, native, values, needs⟩ world
        (.retryableFault (.domain .expectedNativeFunction)) final
  | nativeApplyFault {n v k : Nat} {function : Computation Head Operation Effect n v k} (argument : Tm Head n)
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {outcome : Outcome Head Operation Effect StableFault NativeFault m} :
      Eval primitive ⟨n, v, k, function, native, values, needs⟩ world outcome final →
      FaultOutcome outcome →
      Eval primitive ⟨n, v, k, .nativeApply function argument, native, values, needs⟩ world outcome final
  | valueApply {n v k : Nat} {function : Computation Head Operation Effect n v k} (argument : Value Head Operation Effect n v k)
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      {world selected final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {body : ValueBody Head Operation Effect m} {outcome : Outcome Head Operation Effect StableFault NativeFault m} :
      Eval primitive ⟨n, v, k, function, native, values, needs⟩ world (.value (.valueFunction body)) selected →
      Eval primitive (body.open (captureValue native values needs argument)) selected outcome final →
      Eval primitive ⟨n, v, k, .valueApply function argument, native, values, needs⟩ world outcome final
  | valueApplyMismatch {n v k : Nat} {function : Computation Head Operation Effect n v k} (argument : Value Head Operation Effect n v k)
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      {world final : NeedWorld Head Operation Effect StableFault NativeFault m} {answer : Answer Head Operation Effect m} :
      Eval primitive ⟨n, v, k, function, native, values, needs⟩ world (.value answer) final →
      (∀ body, answer ≠ .valueFunction body) →
      Eval primitive ⟨n, v, k, .valueApply function argument, native, values, needs⟩ world
        (.retryableFault (.domain .expectedValueFunction)) final
  | valueApplyFault {n v k : Nat} {function : Computation Head Operation Effect n v k} (argument : Value Head Operation Effect n v k)
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {outcome : Outcome Head Operation Effect StableFault NativeFault m} :
      Eval primitive ⟨n, v, k, function, native, values, needs⟩ world outcome final →
      FaultOutcome outcome →
      Eval primitive ⟨n, v, k, .valueApply function argument, native, values, needs⟩ world outcome final
  | forceThunk {n v k p w l : Nat} (value : Value Head Operation Effect n v k)
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      {code : Computation Head Operation Effect p w l} {capturedNative : Sub Head p m}
      {capturedValues : Fin w → RuntimeValue Head Operation Effect m} {capturedNeeds : Fin l → CellId}
      {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {outcome : Outcome Head Operation Effect StableFault NativeFault m} :
      captureValue native values needs value = .thunk code capturedNative capturedValues capturedNeeds →
      Eval primitive ⟨p, w, l, code, capturedNative, capturedValues, capturedNeeds⟩ world outcome final →
      Eval primitive ⟨n, v, k, .forceThunk value, native, values, needs⟩ world outcome final
  | forceThunkMismatch {n v k : Nat} (value : Value Head Operation Effect n v k)
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
      (∀ (p w l : Nat) (code : Computation Head Operation Effect p w l) (capturedNative : Sub Head p m)
        (capturedValues : Fin w → RuntimeValue Head Operation Effect m) (capturedNeeds : Fin l → CellId),
        captureValue native values needs value ≠ .thunk code capturedNative capturedValues capturedNeeds) →
      Eval primitive ⟨n, v, k, .forceThunk value, native, values, needs⟩ world
        (.retryableFault (.domain .expectedThunk)) world
  | unpackNative {n v k : Nat} (value : Value Head Operation Effect n v k)
      {body : Computation Head Operation Effect (n + 1) (v + 1) k}
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      {index : Tm Head m} {payload : RuntimeValue Head Operation Effect m}
      {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {outcome : Outcome Head Operation Effect StableFault NativeFault m} :
      captureValue native values needs value = .packNative index payload →
      Eval primitive (PairBody.open ⟨n, v, k, body, native, values, needs⟩ index payload)
        world outcome final →
      Eval primitive ⟨n, v, k, .unpackNative value body, native, values, needs⟩ world outcome final
  | unpackNativeMismatch {n v k : Nat} (value : Value Head Operation Effect n v k)
      (body : Computation Head Operation Effect (n + 1) (v + 1) k)
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
      (∀ index payload, captureValue native values needs value ≠ .packNative index payload) →
      Eval primitive ⟨n, v, k, .unpackNative value body, native, values, needs⟩ world
        (.retryableFault (.domain .expectedNativePair)) world
  | bindNativeValue {n v k : Nat} {first : Computation Head Operation Effect n v k}
      {body : Computation Head Operation Effect (n + 1) v k}
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      {world allocated selected final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {cell : CellId} {value : Tm Head m} {outcome : Outcome Head Operation Effect StableFault NativeFault m} :
      world.allocate? ⟨n, v, k, first, native, values, needs⟩ = some (allocated, cell) →
      Force primitive cell allocated (.value (.returned (.native value))) selected →
      Eval primitive (NativeBody.open ⟨n, v, k, body, native, values, needs⟩ value)
        selected outcome final →
      Eval primitive ⟨n, v, k, .bindNative first body, native, values, needs⟩ world (outcome) final
  | bindNativeMismatch {n v k : Nat} {first : Computation Head Operation Effect n v k}
      (body : Computation Head Operation Effect (n + 1) v k)
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      {world allocated final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {cell : CellId} {answer : Answer Head Operation Effect m} :
      world.allocate? ⟨n, v, k, first, native, values, needs⟩ = some (allocated, cell) →
      Force primitive cell allocated (.value answer) final →
      (∀ value, answer ≠ .returned (.native value)) →
      Eval primitive ⟨n, v, k, .bindNative first body, native, values, needs⟩ world
        (.retryableFault (.domain .expectedNativeValue)) final
  | bindNativeFault {n v k : Nat} {first : Computation Head Operation Effect n v k}
      (body : Computation Head Operation Effect (n + 1) v k)
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      {world allocated final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {cell : CellId} {outcome : Outcome Head Operation Effect StableFault NativeFault m} :
      world.allocate? ⟨n, v, k, first, native, values, needs⟩ = some (allocated, cell) →
      Force primitive cell allocated outcome final → FaultOutcome outcome →
      Eval primitive ⟨n, v, k, .bindNative first body, native, values, needs⟩ world outcome final
  | bindNativeAllocationFailure {n v k : Nat} {first : Computation Head Operation Effect n v k}
      (body : Computation Head Operation Effect (n + 1) v k)
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      {world : NeedWorld Head Operation Effect StableFault NativeFault m} :
      world.allocate? ⟨n, v, k, first, native, values, needs⟩ = none →
      Eval primitive ⟨n, v, k, .bindNative first body, native, values, needs⟩ world
        (allocationFailure world).1 (allocationFailure world).2
  | bindValueValue {n v k : Nat} {first : Computation Head Operation Effect n v k}
      {body : Computation Head Operation Effect n (v + 1) k}
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      {world allocated selected final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {cell : CellId} {value : RuntimeValue Head Operation Effect m} {outcome : Outcome Head Operation Effect StableFault NativeFault m} :
      world.allocate? ⟨n, v, k, first, native, values, needs⟩ = some (allocated, cell) →
      Force primitive cell allocated (.value (.returned value)) selected →
      Eval primitive (ValueBody.open ⟨n, v, k, body, native, values, needs⟩ value)
        selected outcome final →
      Eval primitive ⟨n, v, k, .bindValue first body, native, values, needs⟩ world (outcome) final
  | bindValueMismatch {n v k : Nat} {first : Computation Head Operation Effect n v k}
      (body : Computation Head Operation Effect n (v + 1) k)
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      {world allocated final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {cell : CellId} {answer : Answer Head Operation Effect m} :
      world.allocate? ⟨n, v, k, first, native, values, needs⟩ = some (allocated, cell) →
      Force primitive cell allocated (.value answer) final →
      (∀ value, answer ≠ .returned value) →
      Eval primitive ⟨n, v, k, .bindValue first body, native, values, needs⟩ world
        (.retryableFault (.domain .expectedReturnedValue)) final
  | bindValueFault {n v k : Nat} {first : Computation Head Operation Effect n v k}
      (body : Computation Head Operation Effect n (v + 1) k)
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      {world allocated final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {cell : CellId} {outcome : Outcome Head Operation Effect StableFault NativeFault m} :
      world.allocate? ⟨n, v, k, first, native, values, needs⟩ = some (allocated, cell) →
      Force primitive cell allocated outcome final → FaultOutcome outcome →
      Eval primitive ⟨n, v, k, .bindValue first body, native, values, needs⟩ world outcome final
  | bindValueAllocationFailure {n v k : Nat} {first : Computation Head Operation Effect n v k}
      (body : Computation Head Operation Effect n (v + 1) k)
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      {world : NeedWorld Head Operation Effect StableFault NativeFault m} :
      world.allocate? ⟨n, v, k, first, native, values, needs⟩ = none →
      Eval primitive ⟨n, v, k, .bindValue first body, native, values, needs⟩ world
        (allocationFailure world).1 (allocationFailure world).2
  | sequenceSigmaValue {n v k : Nat} {first : Computation Head Operation Effect n v k}
      {body : Computation Head Operation Effect (n + 1) v k}
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      {world allocated selected final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {cell : CellId} {value : Tm Head m} {outcome : Outcome Head Operation Effect StableFault NativeFault m} :
      world.allocate? ⟨n, v, k, first, native, values, needs⟩ = some (allocated, cell) →
      Force primitive cell allocated (.value (.returned (.native value))) selected →
      Eval primitive (NativeBody.open ⟨n, v, k, body, native, values, needs⟩ value)
        selected outcome final →
      Eval primitive ⟨n, v, k, .sequenceSigma first body, native, values, needs⟩ world (pairOutcome value outcome) final
  | sequenceSigmaMismatch {n v k : Nat} {first : Computation Head Operation Effect n v k}
      (body : Computation Head Operation Effect (n + 1) v k)
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      {world allocated final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {cell : CellId} {answer : Answer Head Operation Effect m} :
      world.allocate? ⟨n, v, k, first, native, values, needs⟩ = some (allocated, cell) →
      Force primitive cell allocated (.value answer) final →
      (∀ value, answer ≠ .returned (.native value)) →
      Eval primitive ⟨n, v, k, .sequenceSigma first body, native, values, needs⟩ world
        (.retryableFault (.domain .expectedNativeValue)) final
  | sequenceSigmaFault {n v k : Nat} {first : Computation Head Operation Effect n v k}
      (body : Computation Head Operation Effect (n + 1) v k)
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      {world allocated final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {cell : CellId} {outcome : Outcome Head Operation Effect StableFault NativeFault m} :
      world.allocate? ⟨n, v, k, first, native, values, needs⟩ = some (allocated, cell) →
      Force primitive cell allocated outcome final → FaultOutcome outcome →
      Eval primitive ⟨n, v, k, .sequenceSigma first body, native, values, needs⟩ world outcome final
  | sequenceSigmaAllocationFailure {n v k : Nat} {first : Computation Head Operation Effect n v k}
      (body : Computation Head Operation Effect (n + 1) v k)
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      {world : NeedWorld Head Operation Effect StableFault NativeFault m} :
      world.allocate? ⟨n, v, k, first, native, values, needs⟩ = none →
      Eval primitive ⟨n, v, k, .sequenceSigma first body, native, values, needs⟩ world
        (allocationFailure world).1 (allocationFailure world).2
  | choose {n v k : Nat} (left right : Computation Head Operation Effect n v k)
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      {world allocated final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {cell : CellId} {outcome : Outcome Head Operation Effect StableFault NativeFault m} :
      world.allocate? ⟨n, v, k, .choose left right, native, values, needs⟩ = some (allocated, cell) →
      Force primitive cell allocated outcome final →
      Eval primitive ⟨n, v, k, .choose left right, native, values, needs⟩ world outcome final
  | chooseAllocationFailure {n v k : Nat} (left right : Computation Head Operation Effect n v k)
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      {world : NeedWorld Head Operation Effect StableFault NativeFault m} :
      world.allocate? ⟨n, v, k, .choose left right, native, values, needs⟩ = none →
      Eval primitive ⟨n, v, k, .choose left right, native, values, needs⟩ world
        (allocationFailure world).1 (allocationFailure world).2
  | letNeed {n v k : Nat} {suspended : Computation Head Operation Effect n v k}
      {body : Computation Head Operation Effect n v (k + 1)}
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      {world allocated final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {cell : CellId} {outcome : Outcome Head Operation Effect StableFault NativeFault m} :
      world.allocate? ⟨n, v, k, suspended, native, values, needs⟩ = some (allocated, cell) →
      Eval primitive (NeedBody.open ⟨n, v, k, body, native, values, needs⟩ cell)
        allocated outcome final →
      Eval primitive ⟨n, v, k, .letNeed suspended body, native, values, needs⟩ world outcome final
  | letNeedAllocationFailure {n v k : Nat} {suspended : Computation Head Operation Effect n v k}
      (body : Computation Head Operation Effect n v (k + 1))
      {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      {world : NeedWorld Head Operation Effect StableFault NativeFault m} :
      world.allocate? ⟨n, v, k, suspended, native, values, needs⟩ = none →
      Eval primitive ⟨n, v, k, .letNeed suspended body, native, values, needs⟩ world
        (allocationFailure world).1 (allocationFailure world).2

inductive Force
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault) :
    CellId → NeedWorld Head Operation Effect StableFault NativeFault m →
      Outcome Head Operation Effect StableFault NativeFault m →
        NeedWorld Head Operation Effect StableFault NativeFault m → Type where
  | cachedValue {cell : CellId} {origin : Closure Head Operation Effect m} {answer : Answer Head Operation Effect m}
      {world : NeedWorld Head Operation Effect StableFault NativeFault m} :
      world.heap.lookup cell = some ⟨origin, .value answer⟩ →
      Force primitive cell world (.value answer) (world.record (.observe cell (.value answer))).1
  | cachedStable {cell : CellId} {origin : Closure Head Operation Effect m} {fault : StableFault}
      {world : NeedWorld Head Operation Effect StableFault NativeFault m} :
      world.heap.lookup cell = some ⟨origin, .stableFault fault⟩ →
      Force primitive cell world (.stableFault fault) (world.record (.observe cell (.stableFault fault))).1
  | missing {cell : CellId} {world : NeedWorld Head Operation Effect StableFault NativeFault m} :
      world.heap.lookup cell = none →
      Force primitive cell world (.retryableFault (.outOfScope cell)) (retryResult world cell (.outOfScope cell)).2
  | evaluating {cell : CellId} {origin : Closure Head Operation Effect m} {owner : EvaluatorId}
      {world : NeedWorld Head Operation Effect StableFault NativeFault m} :
      world.heap.lookup cell = some ⟨origin, .evaluating owner⟩ →
      Force primitive cell world (.retryableFault (.blackhole cell)) (retryResult world cell (.blackhole cell)).2
  | suspended {cell : CellId} {origin selected : Closure Head Operation Effect m} {position : Nat} {rule : Rule}
      {world bodyFinal : NeedWorld Head Operation Effect StableFault NativeFault m}
      {bodyOutcome : Outcome Head Operation Effect StableFault NativeFault m} :
      world.heap.lookup cell = some ⟨origin, .suspended⟩ →
      Selection origin position rule selected →
      Eval primitive selected (enterWorld world cell origin position rule) bodyOutcome bodyFinal →
      Force primitive cell world (finalize bodyFinal cell world.nextEvaluator bodyOutcome).1
        (finalize bodyFinal cell world.nextEvaluator bodyOutcome).2

end

mutual
/-- A finite source-derivation measure, not a termination measure for programs.
The extra unit permits a proof-layer continuation to retain a pending body. -/
def Eval.weight
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {closure : Closure Head Operation Effect m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (derivation : Eval primitive closure world outcome final) : Nat :=
  match derivation with
  | .emit _ body => 2 + body.weight
  | .forceNeed _ forced => 2 + forced.weight
  | .nativeApply _ function body => 2 + function.weight + body.weight
  | .nativeApplyMismatch _ function _ => 2 + function.weight
  | .nativeApplyFault _ function _ => 2 + function.weight
  | .valueApply _ function body => 2 + function.weight + body.weight
  | .valueApplyMismatch _ function _ => 2 + function.weight
  | .valueApplyFault _ function _ => 2 + function.weight
  | .forceThunk _ _ body => 2 + body.weight
  | .unpackNative _ _ body => 2 + body.weight
  | .bindNativeValue _ forced body => 2 + forced.weight + body.weight
  | .bindNativeMismatch _ _ forced _ => 2 + forced.weight
  | .bindNativeFault _ _ forced _ => 2 + forced.weight
  | .bindValueValue _ forced body => 2 + forced.weight + body.weight
  | .bindValueMismatch _ _ forced _ => 2 + forced.weight
  | .bindValueFault _ _ forced _ => 2 + forced.weight
  | .sequenceSigmaValue _ forced body => 2 + forced.weight + body.weight
  | .sequenceSigmaMismatch _ _ forced _ => 2 + forced.weight
  | .sequenceSigmaFault _ _ forced _ => 2 + forced.weight
  | .choose _ _ _ forced => 2 + forced.weight
  | .letNeed _ body => 2 + body.weight
  | _ => 2
termination_by structural derivation

def Force.weight
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {cell : CellId} {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (derivation : Force primitive cell world outcome final) : Nat :=
  match derivation with
  | .suspended _ _ body => 2 + body.weight
  | _ => 2
termination_by structural derivation
end

/-- Every captured source has a selectable occurrence, including all first-class
constructors. A raw source closure cannot produce an empty rule catalog. -/
theorem selection_nonempty (origin : Closure Head Operation Effect m) :
    ∃ position rule selected, Nonempty (Selection origin position rule selected) := by
  rcases origin with ⟨n, v, k, code, native, values, needs⟩
  cases code with
  | choose left right => exact ⟨0, .left, _, ⟨.left left right native values needs⟩⟩
  | _ => exact ⟨0, .entry, _, ⟨.entry (by intro left right equal; cases equal)⟩⟩

theorem finalize_owned_value {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {origin : Closure Head Operation Effect m} {owner : EvaluatorId}
    (owned : world.heap.lookup cell = some ⟨origin, .evaluating owner⟩)
    (answer : Answer Head Operation Effect m) :
    finalize world cell owner (.value answer) =
      (.value answer, ((world.setKnownCache cell ⟨origin, .evaluating owner⟩ (.value answer)).record
        (.observe cell (.value answer))).1) := by
  simp only [finalize, owned, ↓reduceIte]

theorem finalize_owned_stable {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {origin : Closure Head Operation Effect m} {owner : EvaluatorId}
    (owned : world.heap.lookup cell = some ⟨origin, .evaluating owner⟩) (fault : StableFault) :
    finalize world cell owner (.stableFault fault) =
      (.stableFault fault,
        ((world.setKnownCache cell ⟨origin, .evaluating owner⟩ (.stableFault fault)).record
          (.observe cell (.stableFault fault))).1) := by
  simp only [finalize, owned, ↓reduceIte]

theorem finalize_owned_retry {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {origin : Closure Head Operation Effect m} {owner : EvaluatorId}
    (owned : world.heap.lookup cell = some ⟨origin, .evaluating owner⟩)
    (reason : RetryReason (Fault NativeFault)) :
    finalize world cell owner (.retryableFault reason) =
      retryResult (world.setKnownCache cell ⟨origin, .evaluating owner⟩ .suspended) cell reason := by
  simp only [finalize, owned, ↓reduceIte]

theorem finalize_wrong_owner {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {origin : Closure Head Operation Effect m} {actual owner : EvaluatorId}
    (present : world.heap.lookup cell = some ⟨origin, .evaluating actual⟩)
    (different : actual ≠ owner) (outcome : Outcome Head Operation Effect StableFault NativeFault m) :
    finalize world cell owner outcome = retryResult world cell (.ownershipLost cell owner actual) := by
  simp only [finalize, present, different, ↓reduceIte]

/-- A cached answer is retained in full, including function bodies and their
lexical environments. No source branch can be selected again. -/
theorem Force.cachedValue_exact
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {origin : Closure Head Operation Effect m} {answer : Answer Head Operation Effect m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (derivation : Force primitive cell world outcome final)
    (cached : world.heap.lookup cell = some ⟨origin, .value answer⟩) :
    outcome = .value answer ∧ final = (world.record (.observe cell (.value answer))).1 := by
  cases derivation with
  | cachedValue present => cases cached.symm.trans present; exact ⟨rfl, rfl⟩
  | cachedStable present => cases cached.symm.trans present
  | missing absent => cases cached.symm.trans absent
  | evaluating present => cases cached.symm.trans present
  | suspended present _ _ => cases cached.symm.trans present

theorem FaultOutcome.not_value {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (fault : FaultOutcome outcome) (answer : Answer Head Operation Effect m) :
    outcome ≠ .value answer := by cases fault <;> intro impossible <;> cases impossible

theorem FaultOutcome.pairOutcome {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (fault : FaultOutcome outcome) (first : Tm Head m) : pairOutcome first outcome = outcome := by
  cases fault <;> rfl

namespace Examples

/-- The suspended function returns its older captured native variable, not the
new argument. Its effect happens in the forcing world. -/
def capturedThunk (effect : Effect) (first : Tm Head m) : RuntimeValue Head Operation Effect m :=
  .thunk (n := 1) (v := 0) (k := 0)
    (.emit effect (.nativeLambda (.returnValue (.native (.var 1)))))
    (fun _ => first) Fin.elim0 Fin.elim0

def thunkApplication (effect : Effect) (first argument : Tm Head m) : Closure Head Operation Effect m :=
  ⟨1, 1, 0, .nativeApply (.forceThunk (.variable 0)) (.var 0),
    (fun _ => argument), (fun _ => capturedThunk effect first), Fin.elim0⟩

theorem captured_thunk_application
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (effect : Effect) (first argument : Tm Head m)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
    Nonempty (Eval primitive (thunkApplication effect first argument) world
      (.value (.returned (.native first))) (world.record (.effect effect)).1) := by
  constructor
  refine Eval.nativeApply (.var 0)
    (selected := (world.record (.effect effect)).1)
    (body := ⟨1, 0, 0, .returnValue (.native (.var 1)), (fun _ => first), Fin.elim0, Fin.elim0⟩) ?_ ?_
  · exact Eval.forceThunk (.variable 0) rfl
      (Eval.emit effect (Eval.nativeLambda _ _ _ _ _))
  · exact Eval.returnValue (.native (.var 1)) _ _ _ _

/-- Captured lexical identity is observable even when the caller supplies a
different argument; ordinary forcing does not replace the captured environment. -/
theorem captured_thunk_not_argument
    (first argument : Tm Head m) (different : first ≠ argument) :
    (Produced.value (Answer.returned (RuntimeValue.native first)) :
      Outcome Head Operation Effect StableFault NativeFault m) ≠
        .value (.returned (.native argument)) := by
  intro same
  cases same
  exact different rfl

/-- Raw malformed forcing has a source fault derivation, independently of any
bounded machine test or typing assumption. -/
theorem native_is_not_a_thunk
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (value : Tm Head m) (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
    Nonempty (Eval primitive
      ⟨1, 0, 0, .forceThunk (.native (.var 0)), (fun _ => value), Fin.elim0, Fin.elim0⟩
      world (.retryableFault (.domain .expectedThunk)) world) := by
  exact ⟨Eval.forceThunkMismatch (.native (.var 0)) world
    (by intro p w l code capturedNative capturedValues capturedNeeds impossible; cases impossible)⟩

/-- Equal branch bodies still have two distinct selection occurrences. -/
theorem duplicate_selection (code : Computation Head Operation Effect n v k)
    (native : Sub Head n m) (values : Fin v → RuntimeValue Head Operation Effect m) (needs : Fin k → CellId) :
    Nonempty (Selection ⟨n, v, k, .choose code code, native, values, needs⟩ 0 .left
      ⟨n, v, k, code, native, values, needs⟩) ∧
    Nonempty (Selection ⟨n, v, k, .choose code code, native, values, needs⟩ 1 .right
      ⟨n, v, k, code, native, values, needs⟩) :=
  ⟨⟨.left code code native values needs⟩, ⟨.right code code native values needs⟩⟩

theorem duplicate_entry_worlds_distinct
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (cell : CellId) (origin : Closure Head Operation Effect m) :
    enterWorld world cell origin 0 .left ≠ enterWorld world cell origin 1 .right := by
  intro same
  have paths := congrArg (fun world => world.path) same
  simp only [enterWorld, World.record, World.setKnownCache, World.fork] at paths
  have last := List.append_cancel_left paths
  cases last

end Examples

#print axioms selection_nonempty
#print axioms Eval.weight
#print axioms Force.weight
#print axioms finalize_owned_value
#print axioms finalize_owned_stable
#print axioms finalize_owned_retry
#print axioms finalize_wrong_owner
#print axioms Force.cachedValue_exact
#print axioms Examples.captured_thunk_application
#print axioms Examples.captured_thunk_not_argument
#print axioms Examples.native_is_not_a_thunk
#print axioms Examples.duplicate_entry_worlds_distinct

end PolarizedNeedNaturalSemantics
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
