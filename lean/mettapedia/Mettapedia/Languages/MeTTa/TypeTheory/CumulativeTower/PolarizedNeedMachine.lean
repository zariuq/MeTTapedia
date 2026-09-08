import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedSyntax
import Mettapedia.Languages.MeTTa.PrimeNeedLocalSteps
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedNeedMachine

/-!
# First-class native-indexed computations on the owned Need protocol

Runtime values contain reified lexical code and finite environments. They
contain neither a host-language function body nor a saved world. Ordinary
force and computation application enter that code through a silent local
step, retaining the consumer's current world and outer protocol stack.

The cached answer carrier distinguishes returned values from native-argument
and value-argument computation functions. Sharing construction of a thunk
does not share its later executions. Raw polarity mismatches are explicit
machine faults, not logical counterexamples. This module defines a candidate
execution; source typing and execution preservation are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeedMachine

open PrimeNeedReference
open PolarizedNeed (Value Computation)

/-- Finite environments contain values, not semantic functions implementing
source computation. A thunk has no world or continuation field. -/
inductive RuntimeValue (Head Operation Effect : Type) (m : Nat) where
  | native (term : Tm Head m)
  | thunk {n v k : Nat} (code : Computation Head Operation Effect n v k)
      (native : Sub Head n m) (values : Fin v → RuntimeValue Head Operation Effect m)
      (needs : Fin k → CellId)
  | packNative (index : Tm Head m) (value : RuntimeValue Head Operation Effect m)

/-- A lexical body with explicit, still-unopened binders. -/
structure Captured (Head Operation Effect : Type) (m dn dv dk : Nat) where
  n : Nat
  v : Nat
  k : Nat
  code : Computation Head Operation Effect (n + dn) (v + dv) (k + dk)
  native : Sub Head n m
  values : Fin v → RuntimeValue Head Operation Effect m
  needs : Fin k → CellId

abbrev Closure (Head Operation Effect : Type) (m : Nat) := Captured Head Operation Effect m 0 0 0
abbrev NativeBody (Head Operation Effect : Type) (m : Nat) := Captured Head Operation Effect m 1 0 0
abbrev ValueBody (Head Operation Effect : Type) (m : Nat) := Captured Head Operation Effect m 0 1 0
abbrev NeedBody (Head Operation Effect : Type) (m : Nat) := Captured Head Operation Effect m 0 0 1
abbrev PairBody (Head Operation Effect : Type) (m : Nat) := Captured Head Operation Effect m 1 1 0

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}

def NativeBody.open (body : NativeBody Head Operation Effect m) (argument : Tm Head m) :
    Closure Head Operation Effect m :=
  ⟨body.n + 1, body.v, body.k, body.code, Fin.cases argument body.native, body.values, body.needs⟩

def ValueBody.open (body : ValueBody Head Operation Effect m)
    (argument : RuntimeValue Head Operation Effect m) : Closure Head Operation Effect m :=
  ⟨body.n, body.v + 1, body.k, body.code, body.native, Fin.cases argument body.values, body.needs⟩

def NeedBody.open (body : NeedBody Head Operation Effect m) (cell : CellId) :
    Closure Head Operation Effect m :=
  ⟨body.n, body.v, body.k + 1, body.code, body.native, body.values, Fin.cases cell body.needs⟩

def PairBody.open (body : PairBody Head Operation Effect m) (index : Tm Head m)
    (value : RuntimeValue Head Operation Effect m) : Closure Head Operation Effect m :=
  ⟨body.n + 1, body.v + 1, body.k, body.code,
    Fin.cases index body.native, Fin.cases value body.values, body.needs⟩

/-- A computation function is a weak-head computation answer, not a returned
value. It becomes a first-class value through an ordinary thunk. -/
inductive Answer (Head Operation Effect : Type) (m : Nat) where
  | returned (value : RuntimeValue Head Operation Effect m)
  | nativeFunction (body : NativeBody Head Operation Effect m)
  | valueFunction (body : ValueBody Head Operation Effect m)

inductive Fault (NativeFault : Type) where
  | native (fault : NativeFault)
  | allocationResumeDemanded
  | expectedNativeValue
  | expectedReturnedValue
  | expectedNativeFunction
  | expectedValueFunction
  | expectedThunk
  | expectedNativePair
  | localTransitionRequired
  deriving DecidableEq, Repr

abbrev Outcome (Head Operation Effect StableFault NativeFault : Type) (m : Nat) :=
  Produced (Answer Head Operation Effect m) StableFault (Fault NativeFault)

def liftRetry : RetryReason NativeFault → RetryReason (Fault NativeFault)
  | .domain fault => .domain (.native fault)
  | .blackhole cell => .blackhole cell
  | .outOfScope cell => .outOfScope cell
  | .noRule cell => .noRule cell
  | .ownershipLost cell expected actual => .ownershipLost cell expected actual
  | .allocationCollision cell => .allocationCollision cell

def liftOutcome : Produced (Tm Head m) StableFault NativeFault →
    Outcome Head Operation Effect StableFault NativeFault m
  | .value value => .value (.returned (.native value))
  | .stableFault fault => .stableFault fault
  | .retryableFault reason => .retryableFault (liftRetry reason)

def captureValue {n v k : Nat} (native : Sub Head n m)
    (values : Fin v → RuntimeValue Head Operation Effect m) (needs : Fin k → CellId) :
    Value Head Operation Effect n v k → RuntimeValue Head Operation Effect m
  | .native term => .native (subst native term)
  | .variable index => values index
  | .thunk code => .thunk code native values needs
  | .packNative index value => .packNative (subst native index) (captureValue native values needs value)

inductive Kont (Head Operation Effect : Type) (m : Nat) where
  | done
  | pair (first : Tm Head m) (rest : Kont Head Operation Effect m)
  | nativeApply (argument : Tm Head m) (rest : Kont Head Operation Effect m)
  | valueApply (argument : RuntimeValue Head Operation Effect m) (rest : Kont Head Operation Effect m)

inductive Resume (Head Operation Effect : Type) (m : Nat) where
  | finish (kont : Kont Head Operation Effect m)
  | bindNative (body : NativeBody Head Operation Effect m) (kont : Kont Head Operation Effect m)
  | bindValue (body : ValueBody Head Operation Effect m) (kont : Kont Head Operation Effect m)
  | bindSigma (body : NativeBody Head Operation Effect m) (kont : Kont Head Operation Effect m)
  | bindNeed (body : NeedBody Head Operation Effect m) (kont : Kont Head Operation Effect m)

inductive Local (Head Operation Effect StableFault NativeFault : Type) (m : Nat) where
  | evaluate (closure : Closure Head Operation Effect m) (kont : Kont Head Operation Effect m)
  | demand (cell : CellId) (resume : Resume Head Operation Effect m)
  | complete (outcome : Outcome Head Operation Effect StableFault NativeFault m)

/-- Return-only continuation processing is sufficient for unchanged source
returns and primitives. Applications of computation functions use local
transitions or `deliver` after a protocol demand. -/
def finish (outcome : Outcome Head Operation Effect StableFault NativeFault m) :
    Kont Head Operation Effect m → Outcome Head Operation Effect StableFault NativeFault m
  | .done => outcome
  | .pair first rest =>
      match outcome with
      | .value (.returned (.native second)) => finish (.value (.returned (.native (.pair first second)))) rest
      | .value _ => .retryableFault (.domain .expectedNativeValue)
      | .stableFault fault => .stableFault fault
      | .retryableFault reason => .retryableFault reason
  | .nativeApply _ _ =>
      match outcome with
      | .value _ => .retryableFault (.domain .expectedNativeFunction)
      | .stableFault fault => .stableFault fault
      | .retryableFault reason => .retryableFault reason
  | .valueApply _ _ =>
      match outcome with
      | .value _ => .retryableFault (.domain .expectedValueFunction)
      | .stableFault fault => .stableFault fault
      | .retryableFault reason => .retryableFault reason

/-- A cached computation function resumes at its current consumer, using only
its saved lexical environment. Faults never invoke a function body. -/
def deliver (outcome : Outcome Head Operation Effect StableFault NativeFault m) :
    Kont Head Operation Effect m → Local Head Operation Effect StableFault NativeFault m
  | .done => .complete outcome
  | .pair first rest =>
      match outcome with
      | .value (.returned (.native second)) => deliver (.value (.returned (.native (.pair first second)))) rest
      | .value _ => .complete (.retryableFault (.domain .expectedNativeValue))
      | .stableFault fault => .complete (.stableFault fault)
      | .retryableFault reason => .complete (.retryableFault reason)
  | .nativeApply argument rest =>
      match outcome with
      | .value (.nativeFunction body) => .evaluate (body.open argument) rest
      | .value _ => .complete (.retryableFault (.domain .expectedNativeFunction))
      | .stableFault fault => .complete (.stableFault fault)
      | .retryableFault reason => .complete (.retryableFault reason)
  | .valueApply argument rest =>
      match outcome with
      | .value (.valueFunction body) => .evaluate (body.open argument) rest
      | .value _ => .complete (.retryableFault (.domain .expectedValueFunction))
      | .stableFault fault => .complete (.stableFault fault)
      | .retryableFault reason => .complete (.retryableFault reason)

abbrev Rule := ScopedNeedMachine.Rule

abbrev NeedSpec (Head Operation Effect StableFault NativeFault : Type) (m : Nat) :=
  Spec (Closure Head Operation Effect m) (Local Head Operation Effect StableFault NativeFault m)
    (Resume Head Operation Effect m) Rule (Answer Head Operation Effect m) StableFault (Fault NativeFault) Effect

abbrev NeedExtension (Head Operation Effect StableFault NativeFault : Type) (m : Nat) :=
  PrimeNeedLocalSteps.Extension (Closure Head Operation Effect m)
    (Local Head Operation Effect StableFault NativeFault m)
    (Resume Head Operation Effect m) Rule (Answer Head Operation Effect m) StableFault (Fault NativeFault) Effect

abbrev NeedWorld (Head Operation Effect StableFault NativeFault : Type) (m : Nat) :=
  World (Closure Head Operation Effect m) Rule (Answer Head Operation Effect m) StableFault (Fault NativeFault) Effect

abbrev NeedMachine (Head Operation Effect StableFault NativeFault : Type) (m : Nat) :=
  Machine (Closure Head Operation Effect m) (Local Head Operation Effect StableFault NativeFault m)
    (Resume Head Operation Effect m) Rule (Answer Head Operation Effect m) StableFault (Fault NativeFault) Effect

def alternatives (origin : Closure Head Operation Effect m) :
    List (Rule × Local Head Operation Effect StableFault NativeFault m) :=
  match origin with
  | ⟨n, v, k, .choose left right, native, values, needs⟩ =>
      [(.left, .evaluate ⟨n, v, k, left, native, values, needs⟩ .done),
       (.right, .evaluate ⟨n, v, k, right, native, values, needs⟩ .done)]
  | origin => [(.entry, .evaluate origin .done)]

def action (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault) :
    Local Head Operation Effect StableFault NativeFault m →
      Action (Closure Head Operation Effect m) (Local Head Operation Effect StableFault NativeFault m)
        (Resume Head Operation Effect m) (Answer Head Operation Effect m) StableFault (Fault NativeFault) Effect
  | .evaluate ⟨n, v, k, code, native, values, needs⟩ kont =>
      match code with
      | .returnValue value => .done (finish (.value (.returned (captureValue native values needs value))) kont)
      | .bindNative first body =>
          .allocate ⟨n, v, k, first, native, values, needs⟩
            (.bindNative ⟨n, v, k, body, native, values, needs⟩ kont)
      | .bindValue first body =>
          .allocate ⟨n, v, k, first, native, values, needs⟩
            (.bindValue ⟨n, v, k, body, native, values, needs⟩ kont)
      | .sequenceSigma first body =>
          .allocate ⟨n, v, k, first, native, values, needs⟩
            (.bindSigma ⟨n, v, k, body, native, values, needs⟩ kont)
      | .nativeLambda body => .done (finish (.value (.nativeFunction ⟨n, v, k, body, native, values, needs⟩)) kont)
      | .valueLambda body => .done (finish (.value (.valueFunction ⟨n, v, k, body, native, values, needs⟩)) kont)
      | .nativeApply _ _ | .valueApply _ _ | .forceThunk _ | .unpackNative _ _ =>
          .done (.retryableFault (.domain .localTransitionRequired))
      | .choose left right =>
          .allocate ⟨n, v, k, .choose left right, native, values, needs⟩ (.finish kont)
      | .call operation argument => .done (finish (liftOutcome (primitive operation (subst native argument))) kont)
      | .emit effect next => .perform effect (.evaluate ⟨n, v, k, next, native, values, needs⟩ kont)
      | .letNeed suspended body =>
          .allocate ⟨n, v, k, suspended, native, values, needs⟩
            (.bindNeed ⟨n, v, k, body, native, values, needs⟩ kont)
      | .forceNeed reference => .demand (needs reference) (.finish kont)
  | .demand cell resume => .demand cell resume
  | .complete outcome => .done outcome

def localStep : Local Head Operation Effect StableFault NativeFault m →
    Option (Local Head Operation Effect StableFault NativeFault m)
  | .evaluate ⟨n, v, k, .nativeApply function argument, native, values, needs⟩ kont =>
      some (.evaluate ⟨n, v, k, function, native, values, needs⟩ (.nativeApply (subst native argument) kont))
  | .evaluate ⟨n, v, k, .valueApply function argument, native, values, needs⟩ kont =>
      some (.evaluate ⟨n, v, k, function, native, values, needs⟩
        (.valueApply (captureValue native values needs argument) kont))
  | .evaluate ⟨n, v, k, .nativeLambda body, native, values, needs⟩ (.nativeApply argument rest) =>
      some (.evaluate (NativeBody.open ⟨n, v, k, body, native, values, needs⟩ argument) rest)
  | .evaluate ⟨n, v, k, .valueLambda body, native, values, needs⟩ (.valueApply argument rest) =>
      some (.evaluate (ValueBody.open ⟨n, v, k, body, native, values, needs⟩ argument) rest)
  | .evaluate ⟨_, _, _, .forceThunk value, native, values, needs⟩ kont =>
      match captureValue native values needs value with
      | .thunk code native values needs => some (.evaluate ⟨_, _, _, code, native, values, needs⟩ kont)
      | _ => some (.complete (.retryableFault (.domain .expectedThunk)))
  | .evaluate ⟨n, v, k, .unpackNative value body, native, values, needs⟩ kont =>
      match captureValue native values needs value with
      | .packNative index value =>
          some (.evaluate (PairBody.open ⟨n, v, k, body, native, values, needs⟩ index value) kont)
      | _ => some (.complete (.retryableFault (.domain .expectedNativePair)))
  | _ => none

def afterAllocation (resume : Resume Head Operation Effect m) (cell : CellId) :
    Local Head Operation Effect StableFault NativeFault m :=
  match resume with
  | .bindNeed body kont => .evaluate (body.open cell) kont
  | resume => .demand cell resume

def afterDemand (resume : Resume Head Operation Effect m)
    (outcome : Outcome Head Operation Effect StableFault NativeFault m) :
    Local Head Operation Effect StableFault NativeFault m :=
  match resume, outcome with
  | .finish kont, outcome => deliver outcome kont
  | .bindNative body kont, .value (.returned (.native value)) => .evaluate (body.open value) kont
  | .bindSigma body kont, .value (.returned (.native value)) => .evaluate (body.open value) (.pair value kont)
  | .bindValue body kont, .value (.returned value) => .evaluate (body.open value) kont
  | .bindNative _ _, .value _ | .bindSigma _ _, .value _ =>
      .complete (.retryableFault (.domain .expectedNativeValue))
  | .bindValue _ _, .value _ => .complete (.retryableFault (.domain .expectedReturnedValue))
  | .bindNative _ _, .stableFault fault | .bindValue _ _, .stableFault fault | .bindSigma _ _, .stableFault fault =>
      .complete (.stableFault fault)
  | .bindNative _ _, .retryableFault reason | .bindValue _ _, .retryableFault reason | .bindSigma _ _, .retryableFault reason =>
      .complete (.retryableFault reason)
  | .bindNeed _ _, _ => .complete (.retryableFault (.domain .allocationResumeDemanded))

def reference (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault) :
    NeedSpec Head Operation Effect StableFault NativeFault m where
  alternatives := alternatives
  action := action primitive
  afterDemand := afterDemand
  afterAllocation := afterAllocation

def extension (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault) :
    NeedExtension Head Operation Effect StableFault NativeFault m :=
  ⟨reference primitive, localStep⟩

theorem ordinary_force_local {n v k : Nat} (code : Computation Head Operation Effect n v k)
    (native : Sub Head n m) (values : Fin v → RuntimeValue Head Operation Effect m)
    (needs : Fin k → CellId) (kont : Kont Head Operation Effect m) :
    localStep (StableFault := StableFault) (NativeFault := NativeFault)
      (.evaluate ⟨n, v, k, .forceThunk (.thunk code), native, values, needs⟩ kont) =
      some (.evaluate ⟨n, v, k, code, native, values, needs⟩ kont) := rfl

theorem native_application_local {n v k : Nat}
    (body : Computation Head Operation Effect (n + 1) v k) (argument : Tm Head m)
    (native : Sub Head n m) (values : Fin v → RuntimeValue Head Operation Effect m)
    (needs : Fin k → CellId) (kont : Kont Head Operation Effect m) :
    localStep (StableFault := StableFault) (NativeFault := NativeFault)
      (.evaluate ⟨n, v, k, .nativeLambda body, native, values, needs⟩ (.nativeApply argument kont)) =
      some (.evaluate ⟨n + 1, v, k, body, Fin.cases argument native, values, needs⟩ kont) := rfl

theorem value_application_local {n v k : Nat}
    (body : Computation Head Operation Effect n (v + 1) k)
    (argument : RuntimeValue Head Operation Effect m)
    (native : Sub Head n m) (values : Fin v → RuntimeValue Head Operation Effect m)
    (needs : Fin k → CellId) (kont : Kont Head Operation Effect m) :
    localStep (StableFault := StableFault) (NativeFault := NativeFault)
      (.evaluate ⟨n, v, k, .valueLambda body, native, values, needs⟩ (.valueApply argument kont)) =
      some (.evaluate ⟨n, v + 1, k, body, native, Fin.cases argument values, needs⟩ kont) := rfl

theorem silent_step_preserves_world
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (machine : NeedMachine Head Operation Effect StableFault NativeFault m)
    {state next : Local Head Operation Effect StableFault NativeFault m}
    {stack : List (Frame (Resume Head Operation Effect m))}
    {successor : NeedMachine Head Operation Effect StableFault NativeFault m}
    (control : machine.control = .run state stack) (selected : localStep state = some next)
    (member : successor ∈ PrimeNeedLocalSteps.step (extension primitive) machine) :
    successor.world = machine.world ∧ successor.control = .run next stack ∧
      successor.work = machine.work.bump 0 0 0 0 :=
  PrimeNeedLocalSteps.local_successor_exact (extension primitive) machine control selected member

theorem cached_answer_step
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (machine : NeedMachine Head Operation Effect StableFault NativeFault m)
    {cell : CellId} {stack : List (Frame (Resume Head Operation Effect m))}
    {origin : Closure Head Operation Effect m} {answer : Answer Head Operation Effect m}
    (control : machine.control = .force cell stack)
    (cached : machine.world.heap.lookup cell = some ⟨origin, .value answer⟩) :
    PrimeNeedLocalSteps.step (extension primitive) machine =
      [finished machine (recorded machine.world (.observe cell (.value answer)))
        (.returned (.value answer) stack) 1 0 1 0] :=
  PrimeNeedLocalSteps.force_cached_value_step (extension primitive) machine control cached

#print axioms ordinary_force_local
#print axioms native_application_local
#print axioms value_application_local
#print axioms silent_step_preserves_world
#print axioms cached_answer_step

end PolarizedNeedMachine
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
