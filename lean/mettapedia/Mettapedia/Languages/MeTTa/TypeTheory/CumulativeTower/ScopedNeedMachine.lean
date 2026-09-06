import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedNeedComputation
import Mettapedia.Languages.MeTTa.PrimeNeedCacheLaws

/-!
# Scoped suspension code on the owned Need machine

Closures retain native substitutions and suspension references separately.
Their origins contain no consumer continuation. The existing Need machine
owns allocation, first force, call-time choice, commit and cached observation;
this module supplies its language-local actions, not a second heap evaluator.

`letNeed` allocates without forcing. Sequence allocates and immediately
demands, whereas `sequenceSigma` retains the first native value until the
second computation completes. Effects are receipt events in the existing
machine: there is no implicit mutable-state handler or cached state restore.
Primitive calls have an explicit total outcome interface, including stable
and retryable failures. This is a nonrecursive scoped suspension fragment,
not yet the full first-class value/computation type grammar of CBPV.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace ScopedNeedMachine

open PrimeNeedReference
open ScopedNeedComputation (Code)

variable {Head Operation Effect NativeFault StableFault : Type} {m : Nat}

/-- A suspended producer captures only its lexical environments. -/
structure Closure (Head Operation Effect : Type) (m : Nat) where
  n : Nat
  k : Nat
  code : Code Head Operation Effect n k
  values : Sub Head n m
  needs : Fin k → CellId

/-- A consumer awaiting a native value, with its binder still closed. -/
structure ValueBody (Head Operation Effect : Type) (m : Nat) where
  n : Nat
  k : Nat
  code : Code Head Operation Effect (n + 1) k
  values : Sub Head n m
  needs : Fin k → CellId

def ValueBody.open (body : ValueBody Head Operation Effect m) (value : Tm Head m) :
    Closure Head Operation Effect m :=
  ⟨body.n + 1, body.k, body.code, Fin.cases value body.values, body.needs⟩

/-- An allocation body binds a cell reference, not a native mathematical term. -/
structure NeedBody (Head Operation Effect : Type) (m : Nat) where
  n : Nat
  k : Nat
  code : Code Head Operation Effect n (k + 1)
  values : Sub Head n m
  needs : Fin k → CellId

def NeedBody.open (body : NeedBody Head Operation Effect m) (cell : CellId) :
    Closure Head Operation Effect m :=
  ⟨body.n, body.k + 1, body.code, body.values, Fin.cases cell body.needs⟩

/-- Native pairing occurs before the enclosing producer's commit. -/
inductive Kont (Head : Type) (m : Nat) where
  | done
  | pair (first : Tm Head m) (rest : Kont Head m)

/-- A raw protocol misuse is not a logical refusal or a native primitive fault. -/
inductive Fault (NativeFault : Type) where
  | native (fault : NativeFault)
  | allocationResumeDemanded
  deriving DecidableEq, Repr

abbrev Outcome (Head StableFault NativeFault : Type) (m : Nat) :=
  Produced (Tm Head m) StableFault (Fault NativeFault)

def liftRetry : RetryReason NativeFault → RetryReason (Fault NativeFault)
  | .domain fault => .domain (.native fault)
  | .blackhole cell => .blackhole cell
  | .outOfScope cell => .outOfScope cell
  | .noRule cell => .noRule cell
  | .ownershipLost cell expected actual => .ownershipLost cell expected actual
  | .allocationCollision cell => .allocationCollision cell

def liftOutcome : Produced (Tm Head m) StableFault NativeFault →
    Outcome Head StableFault NativeFault m
  | .value value => .value value
  | .stableFault fault => .stableFault fault
  | .retryableFault reason => .retryableFault (liftRetry reason)

/-- Faults do not run the native-value continuation. -/
def finish (outcome : Outcome Head StableFault NativeFault m) :
    Kont Head m → Outcome Head StableFault NativeFault m
  | .done => outcome
  | .pair first rest =>
      match outcome with
      | .value second => finish (.value (.pair first second)) rest
      | .stableFault fault => .stableFault fault
      | .retryableFault reason => .retryableFault reason

inductive Resume (Head Operation Effect : Type) (m : Nat) where
  | finish (kont : Kont Head m)
  | bindValue (body : ValueBody Head Operation Effect m) (kont : Kont Head m)
  | bindSigma (body : ValueBody Head Operation Effect m) (kont : Kont Head m)
  | bindNeed (body : NeedBody Head Operation Effect m) (kont : Kont Head m)

inductive Local (Head Operation Effect StableFault NativeFault : Type) (m : Nat) where
  | evaluate (closure : Closure Head Operation Effect m) (kont : Kont Head m)
  | demand (cell : CellId) (resume : Resume Head Operation Effect m)
  | complete (outcome : Outcome Head StableFault NativeFault m)

inductive Rule where
  | entry
  | left
  | right
  deriving DecidableEq, Repr

abbrev NeedSpec (Head Operation Effect StableFault NativeFault : Type) (m : Nat) :=
  Spec (Closure Head Operation Effect m)
    (Local Head Operation Effect StableFault NativeFault m)
    (Resume Head Operation Effect m) Rule (Tm Head m) StableFault (Fault NativeFault) Effect

abbrev NeedWorld (Head Operation Effect StableFault NativeFault : Type) (m : Nat) :=
  World (Closure Head Operation Effect m) Rule (Tm Head m) StableFault (Fault NativeFault) Effect

abbrev NeedMachine (Head Operation Effect StableFault NativeFault : Type) (m : Nat) :=
  Machine (Closure Head Operation Effect m)
    (Local Head Operation Effect StableFault NativeFault m)
    (Resume Head Operation Effect m) Rule (Tm Head m) StableFault (Fault NativeFault) Effect

/-- Every producer starts with an empty local continuation. Exact list position
retains the two choice occurrences even when their source code is equal. -/
def alternatives (origin : Closure Head Operation Effect m) :
    List (Rule × Local Head Operation Effect StableFault NativeFault m) :=
  match origin with
  | ⟨n, k, .choose left right, values, needs⟩ =>
      [(.left, .evaluate ⟨n, k, left, values, needs⟩ .done),
       (.right, .evaluate ⟨n, k, right, values, needs⟩ .done)]
  | origin => [(.entry, .evaluate origin .done)]

def action (primitive : Operation → Tm Head m →
    Produced (Tm Head m) StableFault NativeFault) :
    Local Head Operation Effect StableFault NativeFault m →
      Action (Closure Head Operation Effect m)
        (Local Head Operation Effect StableFault NativeFault m)
        (Resume Head Operation Effect m) (Tm Head m) StableFault (Fault NativeFault) Effect
  | .evaluate ⟨n, k, code, values, needs⟩ kont =>
      match code with
      | .returnValue term => .done (finish (.value (subst values term)) kont)
      | .sequence first body =>
          .allocate ⟨n, k, first, values, needs⟩ (.bindValue ⟨n, k, body, values, needs⟩ kont)
      | .sequenceSigma first body =>
          .allocate ⟨n, k, first, values, needs⟩ (.bindSigma ⟨n, k, body, values, needs⟩ kont)
      | .choose left right =>
          .allocate ⟨n, k, .choose left right, values, needs⟩ (.finish kont)
      | .call operation argument =>
          .done (finish (liftOutcome (primitive operation (subst values argument))) kont)
      | .emit effect next => .perform effect (.evaluate ⟨n, k, next, values, needs⟩ kont)
      | .letNeed suspended body =>
          .allocate ⟨n, k, suspended, values, needs⟩ (.bindNeed ⟨n, k, body, values, needs⟩ kont)
      | .force reference => .demand (needs reference) (.finish kont)
  | .demand cell resume => .demand cell resume
  | .complete outcome => .done outcome

def afterAllocation (resume : Resume Head Operation Effect m) (cell : CellId) :
    Local Head Operation Effect StableFault NativeFault m :=
  match resume with
  | .bindNeed body kont => .evaluate (body.open cell) kont
  | resume => .demand cell resume

def afterDemand (resume : Resume Head Operation Effect m)
    (outcome : Outcome Head StableFault NativeFault m) :
    Local Head Operation Effect StableFault NativeFault m :=
  match resume, outcome with
  | .finish kont, outcome => .complete (finish outcome kont)
  | .bindValue body kont, .value value => .evaluate (body.open value) kont
  | .bindSigma body kont, .value value => .evaluate (body.open value) (.pair value kont)
  | .bindValue _ _, .stableFault fault | .bindSigma _ _, .stableFault fault =>
      .complete (.stableFault fault)
  | .bindValue _ _, .retryableFault reason | .bindSigma _ _, .retryableFault reason =>
      .complete (.retryableFault reason)
  | .bindNeed _ _, _ => .complete (.retryableFault (.domain .allocationResumeDemanded))

/-- The source-to-machine interpretation changes no Need protocol rule. -/
def spec (primitive : Operation → Tm Head m →
    Produced (Tm Head m) StableFault NativeFault) :
    NeedSpec Head Operation Effect StableFault NativeFault m where
  alternatives := alternatives
  action := action primitive
  afterDemand := afterDemand
  afterAllocation := afterAllocation

@[simp] theorem finish_done (outcome : Outcome Head StableFault NativeFault m) :
    finish outcome .done = outcome := rfl

@[simp] theorem finish_stableFault (fault : StableFault) (kont : Kont Head m) :
    finish (NativeFault := NativeFault) (.stableFault fault) kont = .stableFault fault := by
  cases kont <;> rfl

@[simp] theorem finish_retryableFault (reason : RetryReason (Fault NativeFault))
    (kont : Kont Head m) :
    finish (StableFault := StableFault) (.retryableFault reason) kont = .retryableFault reason := by
  cases kont <;> rfl

/-- Cached force observes the raw native term with no primitive call or effect
replay. Its continuation remains the current consumer's stack. -/
theorem cached_force_step
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (machine : NeedMachine Head Operation Effect StableFault NativeFault m)
    {cell : CellId} {stack : List (Frame (Resume Head Operation Effect m))}
    {origin : Closure Head Operation Effect m} {value : Tm Head m}
    (control : machine.control = .force cell stack)
    (cached : machine.world.heap.lookup cell = some ⟨origin, .value value⟩) :
    step (spec primitive) machine =
      [finished machine (recorded machine.world (.observe cell (.value value)))
        (.returned (.value value) stack) 1 0 1 0] :=
  PrimeNeedCacheLaws.force_cached_value_step (spec primitive) machine control cached

#print axioms finish_stableFault
#print axioms finish_retryableFault
#print axioms cached_force_step

end ScopedNeedMachine
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
