import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedNeedMachine

/-!
# Natural semantics of separately scoped suspension code

Source evaluation and forcing are mutually inductive, proof-relevant
judgments. Their rules inspect source constructors and heap entries directly.
They do not invoke machine transitions, runtime continuations or bounded
frontiers. Closures and native binder opening reuse the scoped syntax's
capture representation; allocation, ownership and receipts reuse the shared
world data operations.

Choice retains a selected occurrence even when both branches have identical
source. A forced suspension evaluates its selected source in the entered world
and finalizes its owned cache. Retry restores suspension but retains receipts.
Malformed supplied heaps can cause allocation, scope or ownership faults;
these cases remain explicit rather than being confused with a false judgment.
Finite natural derivations make no termination or source--machine adequacy
claim by themselves.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace ScopedNeedNaturalSemantics

open PrimeNeedReference ScopedNeedMachine
open ScopedNeedComputation (Code)

variable {Head Operation Effect StableFault NativeFault : Type} {n m k : Nat}

/-- Choice occurrence is independent source evidence, not a machine successor
index manufactured by running the operational semantics. -/
inductive Selection : Closure Head Operation Effect m → Nat → ScopedNeedMachine.Rule →
    Closure Head Operation Effect m → Type where
  | entry {n k : Nat} {code : Code Head Operation Effect n k}
      {values : Sub Head n m} {needs : Fin k → CellId}
      (notChoice : ∀ left right, code ≠ .choose left right) :
      Selection ⟨n, k, code, values, needs⟩ 0 .entry ⟨n, k, code, values, needs⟩
  | left {n k : Nat} (left right : Code Head Operation Effect n k)
      (values : Sub Head n m) (needs : Fin k → CellId) :
      Selection ⟨n, k, .choose left right, values, needs⟩ 0 .left ⟨n, k, left, values, needs⟩
  | right {n k : Nat} (left right : Code Head Operation Effect n k)
      (values : Sub Head n m) (needs : Fin k → CellId) :
      Selection ⟨n, k, .choose left right, values, needs⟩ 1 .right ⟨n, k, right, values, needs⟩

/-- Enter an owned producer occurrence. Administrative singleton selection
also extends the world path by zero, as part of the protocol observation. -/
def enterWorld (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (cell : CellId) (origin : Closure Head Operation Effect m)
    (position : Nat) (rule : ScopedNeedMachine.Rule) :
    NeedWorld Head Operation Effect StableFault NativeFault m :=
  let owner := world.nextEvaluator
  let advanced := { world with nextEvaluator := owner + 1 }
  let claimed := (advanced.fork position).setKnownCache cell ⟨origin, .suspended⟩ (.evaluating owner)
  let entered := (claimed.record (.evaluate cell owner)).1
  (entered.record (.chooseRule cell rule)).1

/-- Only native values are paired; failure status is not turned into data. -/
def pairOutcome (first : Tm Head m) : Outcome Head StableFault NativeFault m →
    Outcome Head StableFault NativeFault m
  | .value second => .value (.pair first second)
  | .stableFault fault => .stableFault fault
  | .retryableFault reason => .retryableFault reason

def retryResult (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (cell : CellId) (reason : RetryReason (ScopedNeedMachine.Fault NativeFault)) :
    Outcome Head StableFault NativeFault m × NeedWorld Head Operation Effect StableFault NativeFault m :=
  (.retryableFault reason, (world.record (.retry cell reason)).1)

/-- Source-level owned finalization inspects the current heap, not the heap
snapshot at entry. Lost ownership cannot overwrite another cell result. -/
def finalize (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (cell : CellId) (owner : EvaluatorId) (outcome : Outcome Head StableFault NativeFault m) :
    Outcome Head StableFault NativeFault m × NeedWorld Head Operation Effect StableFault NativeFault m :=
  match world.heap.lookup cell with
  | none => retryResult world cell (.outOfScope cell)
  | some record =>
      match record.cache with
      | .evaluating actual =>
          if actual = owner then
            let cache : Cache (Tm Head m) StableFault :=
              match outcome with
              | .value value => .value value
              | .stableFault fault => .stableFault fault
              | .retryableFault _ => .suspended
            let completed := world.setKnownCache cell record cache
            match outcome with
            | .retryableFault reason => retryResult completed cell reason
            | _ => (outcome, (completed.record (.observe cell outcome)).1)
          else retryResult world cell (.ownershipLost cell owner actual)
      | _ => retryResult world cell (.ownershipLost cell owner 0)

mutual

/-- Natural source evaluation. Neither successful execution nor runtime
typing is a premise: each constructor supplies source and world evidence. -/
inductive Eval
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault) :
    Closure Head Operation Effect m → NeedWorld Head Operation Effect StableFault NativeFault m →
      Outcome Head StableFault NativeFault m → NeedWorld Head Operation Effect StableFault NativeFault m →
        Type where
  | returnValue {n k : Nat} (term : Tm Head n) (values : Sub Head n m) (needs : Fin k → CellId)
      (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
      Eval primitive ⟨n, k, .returnValue term, values, needs⟩ world (.value (subst values term)) world
  | call {n k : Nat} (operation : Operation) (argument : Tm Head n)
      (values : Sub Head n m) (needs : Fin k → CellId)
      (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
      Eval primitive ⟨n, k, .call operation argument, values, needs⟩ world
        (liftOutcome (primitive operation (subst values argument))) world
  | emit {n k : Nat} (effect : Effect) {next : Code Head Operation Effect n k}
      {values : Sub Head n m} {needs : Fin k → CellId}
      {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {outcome : Outcome Head StableFault NativeFault m} :
      Eval primitive ⟨n, k, next, values, needs⟩ (world.record (.effect effect)).1 outcome final →
      Eval primitive ⟨n, k, .emit effect next, values, needs⟩ world outcome final
  | force {n k : Nat} (reference : Fin k) {values : Sub Head n m} {needs : Fin k → CellId}
      {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {outcome : Outcome Head StableFault NativeFault m} :
      Force primitive (needs reference) world outcome final →
      Eval primitive ⟨n, k, .force reference, values, needs⟩ world outcome final
  | sequenceValue {n k : Nat} {first : Code Head Operation Effect n k}
      {body : Code Head Operation Effect (n + 1) k} {values : Sub Head n m} {needs : Fin k → CellId}
      {world allocated selected final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {cell : CellId} {value : Tm Head m} {outcome : Outcome Head StableFault NativeFault m} :
      world.allocate? ⟨n, k, first, values, needs⟩ = some (allocated, cell) →
      Force primitive cell allocated (.value value) selected →
      Eval primitive ((⟨n, k, body, values, needs⟩ : ValueBody Head Operation Effect m).open value)
        selected outcome final →
      Eval primitive ⟨n, k, .sequence first body, values, needs⟩ world outcome final
  | sequenceStable {n k : Nat} {first : Code Head Operation Effect n k}
      (body : Code Head Operation Effect (n + 1) k) {values : Sub Head n m} {needs : Fin k → CellId}
      {world allocated final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {cell : CellId} {fault : StableFault} :
      world.allocate? ⟨n, k, first, values, needs⟩ = some (allocated, cell) →
      Force primitive cell allocated (.stableFault fault) final →
      Eval primitive ⟨n, k, .sequence first body, values, needs⟩ world (.stableFault fault) final
  | sequenceRetry {n k : Nat} {first : Code Head Operation Effect n k}
      (body : Code Head Operation Effect (n + 1) k) {values : Sub Head n m} {needs : Fin k → CellId}
      {world allocated final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {cell : CellId} {reason : RetryReason (ScopedNeedMachine.Fault NativeFault)} :
      world.allocate? ⟨n, k, first, values, needs⟩ = some (allocated, cell) →
      Force primitive cell allocated (.retryableFault reason) final →
      Eval primitive ⟨n, k, .sequence first body, values, needs⟩ world (.retryableFault reason) final
  | sequenceSigmaValue {n k : Nat} {first : Code Head Operation Effect n k}
      {body : Code Head Operation Effect (n + 1) k} {values : Sub Head n m} {needs : Fin k → CellId}
      {world allocated selected final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {cell : CellId} {value : Tm Head m} {outcome : Outcome Head StableFault NativeFault m} :
      world.allocate? ⟨n, k, first, values, needs⟩ = some (allocated, cell) →
      Force primitive cell allocated (.value value) selected →
      Eval primitive ((⟨n, k, body, values, needs⟩ : ValueBody Head Operation Effect m).open value)
        selected outcome final →
      Eval primitive ⟨n, k, .sequenceSigma first body, values, needs⟩ world (pairOutcome value outcome) final
  | sequenceSigmaStable {n k : Nat} {first : Code Head Operation Effect n k}
      (body : Code Head Operation Effect (n + 1) k) {values : Sub Head n m} {needs : Fin k → CellId}
      {world allocated final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {cell : CellId} {fault : StableFault} :
      world.allocate? ⟨n, k, first, values, needs⟩ = some (allocated, cell) →
      Force primitive cell allocated (.stableFault fault) final →
      Eval primitive ⟨n, k, .sequenceSigma first body, values, needs⟩ world (.stableFault fault) final
  | sequenceSigmaRetry {n k : Nat} {first : Code Head Operation Effect n k}
      (body : Code Head Operation Effect (n + 1) k) {values : Sub Head n m} {needs : Fin k → CellId}
      {world allocated final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {cell : CellId} {reason : RetryReason (ScopedNeedMachine.Fault NativeFault)} :
      world.allocate? ⟨n, k, first, values, needs⟩ = some (allocated, cell) →
      Force primitive cell allocated (.retryableFault reason) final →
      Eval primitive ⟨n, k, .sequenceSigma first body, values, needs⟩ world (.retryableFault reason) final
  | choose {n k : Nat} (left right : Code Head Operation Effect n k)
      {values : Sub Head n m} {needs : Fin k → CellId}
      {world allocated final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {cell : CellId} {outcome : Outcome Head StableFault NativeFault m} :
      world.allocate? ⟨n, k, .choose left right, values, needs⟩ = some (allocated, cell) →
      Force primitive cell allocated outcome final →
      Eval primitive ⟨n, k, .choose left right, values, needs⟩ world outcome final
  | letNeed {n k : Nat} {suspended : Code Head Operation Effect n k}
      {body : Code Head Operation Effect n (k + 1)} {values : Sub Head n m} {needs : Fin k → CellId}
      {world allocated final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {cell : CellId} {outcome : Outcome Head StableFault NativeFault m} :
      world.allocate? ⟨n, k, suspended, values, needs⟩ = some (allocated, cell) →
      Eval primitive ((⟨n, k, body, values, needs⟩ : NeedBody Head Operation Effect m).open cell)
        allocated outcome final →
      Eval primitive ⟨n, k, .letNeed suspended body, values, needs⟩ world outcome final
  | sequenceAllocationFailure {n k : Nat} {first : Code Head Operation Effect n k}
      (body : Code Head Operation Effect (n + 1) k) {values : Sub Head n m} {needs : Fin k → CellId}
      {world : NeedWorld Head Operation Effect StableFault NativeFault m} :
      world.allocate? ⟨n, k, first, values, needs⟩ = none →
      Eval primitive ⟨n, k, .sequence first body, values, needs⟩ world
        (retryResult world (world.freshCell 0) (.allocationCollision (world.freshCell 0))).1
        (retryResult world (world.freshCell 0) (.allocationCollision (world.freshCell 0))).2
  | sequenceSigmaAllocationFailure {n k : Nat} {first : Code Head Operation Effect n k}
      (body : Code Head Operation Effect (n + 1) k) {values : Sub Head n m} {needs : Fin k → CellId}
      {world : NeedWorld Head Operation Effect StableFault NativeFault m} :
      world.allocate? ⟨n, k, first, values, needs⟩ = none →
      Eval primitive ⟨n, k, .sequenceSigma first body, values, needs⟩ world
        (retryResult world (world.freshCell 0) (.allocationCollision (world.freshCell 0))).1
        (retryResult world (world.freshCell 0) (.allocationCollision (world.freshCell 0))).2
  | chooseAllocationFailure {n k : Nat} (left right : Code Head Operation Effect n k)
      {values : Sub Head n m} {needs : Fin k → CellId}
      {world : NeedWorld Head Operation Effect StableFault NativeFault m} :
      world.allocate? ⟨n, k, .choose left right, values, needs⟩ = none →
      Eval primitive ⟨n, k, .choose left right, values, needs⟩ world
        (retryResult world (world.freshCell 0) (.allocationCollision (world.freshCell 0))).1
        (retryResult world (world.freshCell 0) (.allocationCollision (world.freshCell 0))).2
  | letNeedAllocationFailure {n k : Nat} {suspended : Code Head Operation Effect n k}
      (body : Code Head Operation Effect n (k + 1)) {values : Sub Head n m} {needs : Fin k → CellId}
      {world : NeedWorld Head Operation Effect StableFault NativeFault m} :
      world.allocate? ⟨n, k, suspended, values, needs⟩ = none →
      Eval primitive ⟨n, k, .letNeed suspended body, values, needs⟩ world
        (retryResult world (world.freshCell 0) (.allocationCollision (world.freshCell 0))).1
        (retryResult world (world.freshCell 0) (.allocationCollision (world.freshCell 0))).2

/-- Force shares the selected cell's cache. A suspended producer contributes
both the selected source occurrence and its complete evaluation derivation. -/
inductive Force
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault) :
    CellId → NeedWorld Head Operation Effect StableFault NativeFault m →
      Outcome Head StableFault NativeFault m → NeedWorld Head Operation Effect StableFault NativeFault m →
        Type where
  | cachedValue {cell : CellId} {origin : Closure Head Operation Effect m} {value : Tm Head m}
      {world : NeedWorld Head Operation Effect StableFault NativeFault m} :
      world.heap.lookup cell = some ⟨origin, .value value⟩ →
      Force primitive cell world (.value value) (world.record (.observe cell (.value value))).1
  | cachedStable {cell : CellId} {origin : Closure Head Operation Effect m} {fault : StableFault}
      {world : NeedWorld Head Operation Effect StableFault NativeFault m} :
      world.heap.lookup cell = some ⟨origin, .stableFault fault⟩ →
      Force primitive cell world (.stableFault fault) (world.record (.observe cell (.stableFault fault))).1
  | missing {cell : CellId} {world : NeedWorld Head Operation Effect StableFault NativeFault m} :
      world.heap.lookup cell = none →
      Force primitive cell world (.retryableFault (.outOfScope cell))
        (retryResult world cell (.outOfScope cell)).2
  | evaluating {cell : CellId} {origin : Closure Head Operation Effect m} {owner : EvaluatorId}
      {world : NeedWorld Head Operation Effect StableFault NativeFault m} :
      world.heap.lookup cell = some ⟨origin, .evaluating owner⟩ →
      Force primitive cell world (.retryableFault (.blackhole cell))
        (retryResult world cell (.blackhole cell)).2
  | suspended {cell : CellId} {origin selected : Closure Head Operation Effect m}
      {position : Nat} {rule : ScopedNeedMachine.Rule}
      {world bodyFinal : NeedWorld Head Operation Effect StableFault NativeFault m}
      {bodyOutcome : Outcome Head StableFault NativeFault m} :
      world.heap.lookup cell = some ⟨origin, .suspended⟩ →
      Selection origin position rule selected →
      Eval primitive selected (enterWorld world cell origin position rule) bodyOutcome bodyFinal →
      Force primitive cell world
        (finalize bodyFinal cell world.nextEvaluator bodyOutcome).1
        (finalize bodyFinal cell world.nextEvaluator bodyOutcome).2

end

/-- Every captured source has a selectable occurrence. -/
theorem selection_nonempty (origin : Closure Head Operation Effect m) :
    ∃ position rule selected, Nonempty (Selection origin position rule selected) := by
  rcases origin with ⟨n, k, code, values, needs⟩
  cases code with
  | choose left right => exact ⟨0, .left, _, ⟨.left left right values needs⟩⟩
  | _ => exact ⟨0, .entry, _, ⟨.entry (by intro left right equal; cases equal)⟩⟩

theorem finalize_owned_value {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {origin : Closure Head Operation Effect m} {owner : EvaluatorId}
    (owned : world.heap.lookup cell = some ⟨origin, .evaluating owner⟩) (value : Tm Head m) :
    finalize world cell owner (.value value) =
      (.value value, ((world.setKnownCache cell ⟨origin, .evaluating owner⟩ (.value value)).record
        (.observe cell (.value value))).1) := by
  simp only [finalize, owned, ↓reduceIte]

theorem finalize_owned_retry {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {origin : Closure Head Operation Effect m} {owner : EvaluatorId}
    (owned : world.heap.lookup cell = some ⟨origin, .evaluating owner⟩)
    (reason : RetryReason (ScopedNeedMachine.Fault NativeFault)) :
    finalize world cell owner (.retryableFault reason) =
      retryResult (world.setKnownCache cell ⟨origin, .evaluating owner⟩ .suspended) cell reason := by
  simp only [finalize, owned, ↓reduceIte]

/-- Once a value is cached, every natural force derivation returns that value
and appends exactly its observation. No source branch can be selected again. -/
theorem Force.cachedValue_exact
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {origin : Closure Head Operation Effect m} {value : Tm Head m}
    {outcome : Outcome Head StableFault NativeFault m}
    (derivation : Force primitive cell world outcome final)
    (cached : world.heap.lookup cell = some ⟨origin, .value value⟩) :
    outcome = .value value ∧ final = (world.record (.observe cell (.value value))).1 := by
  cases derivation with
  | cachedValue present => cases cached.symm.trans present; exact ⟨rfl, rfl⟩
  | cachedStable present => cases cached.symm.trans present
  | missing absent => cases cached.symm.trans absent
  | evaluating present => cases cached.symm.trans present
  | suspended present _ _ => cases cached.symm.trans present

theorem finalize_wrong_owner {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {origin : Closure Head Operation Effect m} {actual owner : EvaluatorId}
    (present : world.heap.lookup cell = some ⟨origin, .evaluating actual⟩)
    (different : actual ≠ owner) (outcome : Outcome Head StableFault NativeFault m) :
    finalize world cell owner outcome = retryResult world cell (.ownershipLost cell owner actual) := by
  simp only [finalize, present, different, ↓reduceIte]

namespace Examples

inductive ExampleOperation where
  | retain
  | stable
  | retry
  deriving DecidableEq, Repr

def primitive : ExampleOperation → Tm Nat 0 → Produced (Tm Nat 0) Nat Nat
  | .retain, term => .value term
  | .stable, _ => .stableFault 11
  | .retry, _ => .retryableFault (.domain 13)

abbrev ExampleWorld := NeedWorld Nat ExampleOperation Nat Nat Nat 0
abbrev ExampleClosure := Closure Nat ExampleOperation Nat 0

def emptyWorld : ExampleWorld :=
  { lineage := 0, path := [], heap := .empty, receipts := .empty,
    nextCell := 0, nextEvaluator := 0 }

def cell : CellId := ⟨0, [], 0, 0⟩

/-- The fixture is the explicit data produced by real world allocation. -/
def allocatedWorld (origin : ExampleClosure) : ExampleWorld :=
  let heap : Heap ExampleClosure (Tm Nat 0) Nat :=
    { current := Function.update (fun _ => none) cell (some ⟨origin, .suspended⟩),
      spine := [.allocate cell origin] }
  ({ emptyWorld with heap := heap, nextCell := 1 }.record (.allocate cell origin)).1

theorem allocatedWorld_exact (origin : ExampleClosure) :
    emptyWorld.allocate? origin = some (allocatedWorld origin, cell) := rfl

def leafCode : Code Nat ExampleOperation Nat 0 0 := .emit 7 (.returnValue (.head 10))

def duplicateChoice : ExampleClosure := ⟨0, 0, .choose leafCode leafCode, ids, Fin.elim0⟩

def leftEntered : ExampleWorld := enterWorld (allocatedWorld duplicateChoice) cell duplicateChoice 0 .left
def rightEntered : ExampleWorld := enterWorld (allocatedWorld duplicateChoice) cell duplicateChoice 1 .right
def leftBodyFinal : ExampleWorld := (leftEntered.record (.effect 7)).1
def rightBodyFinal : ExampleWorld := (rightEntered.record (.effect 7)).1
def leftFinal : ExampleWorld := (finalize leftBodyFinal cell 0 (.value (.head 10))).2
def rightFinal : ExampleWorld := (finalize rightBodyFinal cell 0 (.value (.head 10))).2

/-- Equal authored branches still supply different source selection evidence. -/
def duplicateLeft : Selection duplicateChoice 0 .left ⟨0, 0, leafCode, ids, Fin.elim0⟩ :=
  .left leafCode leafCode ids Fin.elim0

def duplicateRight : Selection duplicateChoice 1 .right ⟨0, 0, leafCode, ids, Fin.elim0⟩ :=
  .right leafCode leafCode ids Fin.elim0

def forceLeft : Force primitive cell (allocatedWorld duplicateChoice) (.value (.head 10)) leftFinal :=
  .suspended rfl duplicateLeft (.emit 7 (.returnValue _ _ _ _))

def forceRight : Force primitive cell (allocatedWorld duplicateChoice) (.value (.head 10)) rightFinal :=
  .suspended rfl duplicateRight (.emit 7 (.returnValue _ _ _ _))

def evalLeft : Eval primitive duplicateChoice emptyWorld (.value (.head 10)) leftFinal :=
  .choose leafCode leafCode (allocatedWorld_exact duplicateChoice) forceLeft

def evalRight : Eval primitive duplicateChoice emptyWorld (.value (.head 10)) rightFinal :=
  .choose leafCode leafCode (allocatedWorld_exact duplicateChoice) forceRight

theorem duplicate_occurrence_worlds_differ : leftFinal ≠ rightFinal := by
  intro equal
  have paths : [0] = ([1] : WorldPath) := congrArg World.path equal
  cases paths

def effects (world : ExampleWorld) : List Nat :=
  world.receipts.nodes.reverse.filterMap fun node =>
    match node.payload with
    | .effect effect => some effect
    | _ => none

def reusedWorld : ExampleWorld := (leftFinal.record (.observe cell (.value (.head 10)))).1

def forceAgain : Force primitive cell leftFinal (.value (.head 10)) reusedWorld :=
  .cachedValue (origin := duplicateChoice) rfl

theorem reuse_keeps_single_effect : effects leftFinal = [7] ∧ effects reusedWorld = [7] :=
  ⟨rfl, rfl⟩

/-- The source forcing relation itself rejects resampling a completed cell. -/
theorem cached_other_value_impossible (final : ExampleWorld) :
    ¬ Nonempty (Force primitive cell leftFinal (.value (.head 20)) final) := by
  rintro ⟨derivation⟩
  have equal := (derivation.cachedValue_exact (origin := duplicateChoice) (value := .head 10) rfl).1
  cases equal

def retryOrigin : ExampleClosure :=
  ⟨0, 0, .emit 17 (.call .retry (.head 0)), ids, Fin.elim0⟩

def retryEntered : ExampleWorld := enterWorld (allocatedWorld retryOrigin) cell retryOrigin 0 .entry
def retryBodyFinal : ExampleWorld := (retryEntered.record (.effect 17)).1
def retryOutcome : Outcome Nat Nat Nat 0 := .retryableFault (.domain (.native 13))
def retryFinal : ExampleWorld := (finalize retryBodyFinal cell 0 retryOutcome).2

def forceRetry : Force primitive cell (allocatedWorld retryOrigin) retryOutcome retryFinal :=
  .suspended rfl (.entry (by intro left right equal; cases equal))
    (.emit 17 (.call ExampleOperation.retry (.head 0) ids Fin.elim0 _))

theorem retry_restores_suspension_and_keeps_effect :
    retryFinal.heap.lookup cell = some ⟨retryOrigin, .suspended⟩ ∧ effects retryFinal = [17] :=
  ⟨rfl, rfl⟩

/-- An invalid supplied allocation counter collides with a real occupied cell. -/
def collidingWorld : ExampleWorld := { allocatedWorld duplicateChoice with nextCell := 0 }

def collisionFinal : ExampleWorld :=
  (retryResult collidingWorld cell (.allocationCollision cell)).2

def allocationFailure :
    Eval primitive
      (⟨0, 0, .letNeed (.choose leafCode leafCode) (.returnValue (.head 99)), ids, Fin.elim0⟩ :
        ExampleClosure)
      collidingWorld (.retryableFault (.allocationCollision cell)) collisionFinal :=
  .letNeedAllocationFailure _ rfl

theorem collision_does_not_overwrite_origin :
    collisionFinal.heap.lookup cell = some ⟨duplicateChoice, .suspended⟩ := rfl

end Examples

#print axioms selection_nonempty
#print axioms finalize_owned_value
#print axioms finalize_owned_retry
#print axioms Force.cachedValue_exact
#print axioms finalize_wrong_owner
#print axioms Examples.evalLeft
#print axioms Examples.evalRight
#print axioms Examples.duplicate_occurrence_worlds_differ
#print axioms Examples.forceAgain
#print axioms Examples.reuse_keeps_single_effect
#print axioms Examples.cached_other_value_impossible
#print axioms Examples.forceRetry
#print axioms Examples.retry_restores_suspension_and_keeps_effect
#print axioms Examples.allocationFailure
#print axioms Examples.collision_does_not_overwrite_origin

end ScopedNeedNaturalSemantics
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
