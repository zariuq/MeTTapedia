import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedMachine
import Mettapedia.Languages.MeTTa.PrimeNeedRepresentation

/-!
# Exact preservation of the native scoped Need machine

Old native-term closures embed with an empty runtime-value environment. Cached
native results become returned native values; existing faults and continuations
retain their meanings. The new local transition does not intercept any embedded
old local state. Consequently actual transitions and bounded frontier lists
commute exactly, including complete worlds, receipts, branch occurrences and
work. This is a conservative operational image, not a typing theorem for the
new first-class constructs or an adoption of the candidate evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeedEmbedding

open PrimeNeedReference

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}

def closure (origin : ScopedNeedMachine.Closure Head Operation Effect m) :
    PolarizedNeedMachine.Closure Head Operation Effect m :=
  ⟨origin.n, 0, origin.k, PolarizedNeed.Computation.ofScopedNeed origin.code,
    origin.values, Fin.elim0, origin.needs⟩

def nativeBody (body : ScopedNeedMachine.ValueBody Head Operation Effect m) :
    PolarizedNeedMachine.NativeBody Head Operation Effect m :=
  ⟨body.n, 0, body.k, PolarizedNeed.Computation.ofScopedNeed body.code,
    body.values, Fin.elim0, body.needs⟩

def needBody (body : ScopedNeedMachine.NeedBody Head Operation Effect m) :
    PolarizedNeedMachine.NeedBody Head Operation Effect m :=
  ⟨body.n, 0, body.k, PolarizedNeed.Computation.ofScopedNeed body.code,
    body.values, Fin.elim0, body.needs⟩

def kont : ScopedNeedMachine.Kont Head m → PolarizedNeedMachine.Kont Head Operation Effect m
  | .done => .done
  | .pair first rest => .pair first (kont rest)

def fault : ScopedNeedMachine.Fault NativeFault → PolarizedNeedMachine.Fault NativeFault
  | .native error => .native error
  | .allocationResumeDemanded => .allocationResumeDemanded

def retry : RetryReason (ScopedNeedMachine.Fault NativeFault) →
    RetryReason (PolarizedNeedMachine.Fault NativeFault)
  | .domain error => .domain (fault error)
  | .blackhole cell => .blackhole cell
  | .outOfScope cell => .outOfScope cell
  | .noRule cell => .noRule cell
  | .ownershipLost cell expected actual => .ownershipLost cell expected actual
  | .allocationCollision cell => .allocationCollision cell

def outcome : ScopedNeedMachine.Outcome Head StableFault NativeFault m →
    PolarizedNeedMachine.Outcome Head Operation Effect StableFault NativeFault m
  | .value term => .value (.returned (.native term))
  | .stableFault error => .stableFault error
  | .retryableFault reason => .retryableFault (retry reason)

def resume : ScopedNeedMachine.Resume Head Operation Effect m →
    PolarizedNeedMachine.Resume Head Operation Effect m
  | .finish continuation => .finish (kont continuation)
  | .bindValue body continuation => .bindNative (nativeBody body) (kont continuation)
  | .bindSigma body continuation => .bindSigma (nativeBody body) (kont continuation)
  | .bindNeed body continuation => .bindNeed (needBody body) (kont continuation)

def state : ScopedNeedMachine.Local Head Operation Effect StableFault NativeFault m →
    PolarizedNeedMachine.Local Head Operation Effect StableFault NativeFault m
  | .evaluate origin continuation => .evaluate (closure origin) (kont continuation)
  | .demand cell consumer => .demand cell (resume consumer)
  | .complete result => .complete (outcome result)

/-- The heap, receipt graph and control-stack maps are the generic protocol
representation maps, not a separate implementation of the heap. -/
def representation : PrimeNeedRepresentation.Mapping
    (ScopedNeedMachine.Closure Head Operation Effect m)
    (ScopedNeedMachine.Local Head Operation Effect StableFault NativeFault m)
    (ScopedNeedMachine.Resume Head Operation Effect m) ScopedNeedMachine.Rule
    (Tm Head m) StableFault (ScopedNeedMachine.Fault NativeFault) Effect
    (PolarizedNeedMachine.Closure Head Operation Effect m)
    (PolarizedNeedMachine.Local Head Operation Effect StableFault NativeFault m)
    (PolarizedNeedMachine.Resume Head Operation Effect m) PolarizedNeedMachine.Rule
    (PolarizedNeedMachine.Answer Head Operation Effect m) StableFault
    (PolarizedNeedMachine.Fault NativeFault) Effect where
  origin := closure
  state := state
  resume := resume
  rule := id
  value := fun term => .returned (.native term)
  stableFault := id
  retryableFault := fault
  effect := id

@[simp] theorem representation_retry (reason : RetryReason (ScopedNeedMachine.Fault NativeFault)) :
    (representation (Head := Head) (Operation := Operation) (Effect := Effect)
      (StableFault := StableFault) (m := m)).mapRetry reason = retry reason := by
  cases reason <;> rfl

@[simp] theorem representation_outcome (result : ScopedNeedMachine.Outcome Head StableFault NativeFault m) :
    (representation (Operation := Operation) (Effect := Effect)).mapOutcome result = outcome result := by
  cases result with
  | value term => rfl
  | stableFault error => rfl
  | retryableFault reason =>
      exact congrArg Produced.retryableFault (representation_retry (Head := Head)
        (Operation := Operation) (Effect := Effect) (StableFault := StableFault) (m := m) reason)

theorem representation_outcome_eq :
    (representation (Head := Head) (Operation := Operation) (Effect := Effect)
      (StableFault := StableFault) (NativeFault := NativeFault) (m := m)).mapOutcome = outcome :=
  funext representation_outcome

@[simp] theorem nativeBody_open (body : ScopedNeedMachine.ValueBody Head Operation Effect m)
    (term : Tm Head m) :
    (nativeBody body).open term = closure (body.open term) := rfl

@[simp] theorem needBody_open (body : ScopedNeedMachine.NeedBody Head Operation Effect m) (cell : CellId) :
    (needBody body).open cell = closure (body.open cell) := rfl

/-- Native pairing and fault short-circuiting agree for every old continuation,
including arbitrarily nested pending dependent pairs. -/
theorem finish_outcome (result : ScopedNeedMachine.Outcome Head StableFault NativeFault m)
    (continuation : ScopedNeedMachine.Kont Head m) :
    PolarizedNeedMachine.finish (outcome (Operation := Operation) (Effect := Effect) result)
      (kont continuation) = outcome (ScopedNeedMachine.finish result continuation) := by
  induction continuation generalizing result with
  | done => rfl
  | pair first rest ih =>
      cases result with
      | value second => exact ih (.value (.pair first second))
      | stableFault error => rfl
      | retryableFault reason => rfl

/-- Delivering an old cached outcome never opens a new computation function. -/
theorem deliver_outcome (result : ScopedNeedMachine.Outcome Head StableFault NativeFault m)
    (continuation : ScopedNeedMachine.Kont Head m) :
    PolarizedNeedMachine.deliver (outcome (Operation := Operation) (Effect := Effect) result)
      (kont continuation) = .complete (outcome (ScopedNeedMachine.finish result continuation)) := by
  induction continuation generalizing result with
  | done => rfl
  | pair first rest ih =>
      cases result with
      | value second => exact ih (.value (.pair first second))
      | stableFault error => rfl
      | retryableFault reason => rfl

theorem liftOutcome_outcome (result : Produced (Tm Head m) StableFault NativeFault) :
    outcome (ScopedNeedMachine.liftOutcome result) =
      PolarizedNeedMachine.liftOutcome (Operation := Operation) (Effect := Effect) result := by
  cases result with
  | value term => rfl
  | stableFault error => rfl
  | retryableFault reason => cases reason <;> rfl

theorem alternatives_closure (origin : ScopedNeedMachine.Closure Head Operation Effect m) :
    PolarizedNeedMachine.alternatives (StableFault := StableFault) (NativeFault := NativeFault)
      (closure origin) =
    (ScopedNeedMachine.alternatives origin).map (fun pair => (pair.1, state pair.2)) := by
  rcases origin with ⟨n, k, code, values, needs⟩
  cases code <;> rfl

theorem afterAllocation_resume (consumer : ScopedNeedMachine.Resume Head Operation Effect m) (cell : CellId) :
    PolarizedNeedMachine.afterAllocation (StableFault := StableFault) (NativeFault := NativeFault)
      (resume consumer) cell = state (ScopedNeedMachine.afterAllocation consumer cell) := by
  cases consumer <;> rfl

theorem afterDemand_resume (consumer : ScopedNeedMachine.Resume Head Operation Effect m)
    (result : ScopedNeedMachine.Outcome Head StableFault NativeFault m) :
    PolarizedNeedMachine.afterDemand (resume consumer) (outcome result) =
      state (ScopedNeedMachine.afterDemand consumer result) := by
  cases consumer with
  | finish continuation => exact deliver_outcome result continuation
  | bindValue body continuation => cases result <;> rfl
  | bindSigma body continuation => cases result <;> rfl
  | bindNeed body continuation => cases result <;> rfl

theorem action_state
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (source : ScopedNeedMachine.Local Head Operation Effect StableFault NativeFault m) :
    PolarizedNeedMachine.action primitive (state source) =
      representation.mapAction (ScopedNeedMachine.action primitive source) := by
  cases source with
  | demand cell consumer => rfl
  | complete result =>
      simp only [state, ScopedNeedMachine.action, PolarizedNeedMachine.action,
        PrimeNeedRepresentation.Mapping.mapAction, representation_outcome]
  | evaluate origin continuation =>
      rcases origin with ⟨n, k, code, values, needs⟩
      cases code <;>
        simp only [state, closure, PolarizedNeed.Computation.ofScopedNeed,
          ScopedNeedMachine.action, PolarizedNeedMachine.action, PolarizedNeedMachine.captureValue,
          PrimeNeedRepresentation.Mapping.mapAction, representation_outcome,
          finish_outcome, ← liftOutcome_outcome]
      all_goals first
        | rfl
        | exact congrArg Action.done (finish_outcome (.value _) continuation)

theorem compatible
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault) :
    PrimeNeedRepresentation.Compatible (representation (Effect := Effect)) (ScopedNeedMachine.spec primitive)
      (PolarizedNeedMachine.reference primitive) where
  alternatives := alternatives_closure
  action := action_state primitive
  afterDemand := by
    intro consumer result
    change PolarizedNeedMachine.afterDemand (resume consumer) (representation.mapOutcome result) =
      state (ScopedNeedMachine.afterDemand consumer result)
    rw [representation_outcome]
    exact afterDemand_resume consumer result
  afterAllocation := afterAllocation_resume

/-- Every old source constructor remains outside the new local-interception
domain, even when evaluated beneath pending old native-pair continuations. -/
theorem localStep_state (source : ScopedNeedMachine.Local Head Operation Effect StableFault NativeFault m) :
    PolarizedNeedMachine.localStep (state source) = none := by
  cases source with
  | demand cell consumer => rfl
  | complete result => rfl
  | evaluate origin continuation =>
      rcases origin with ⟨n, k, code, values, needs⟩
      cases code <;> rfl

theorem extension_step_eq_reference
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (machine : ScopedNeedMachine.NeedMachine Head Operation Effect StableFault NativeFault m) :
    PrimeNeedLocalSteps.step (PolarizedNeedMachine.extension primitive) (representation.mapMachine machine) =
      PrimeNeedReference.step (PolarizedNeedMachine.reference primitive) (representation.mapMachine machine) := by
  cases control : machine.control <;>
    simp only [PrimeNeedLocalSteps.step, PrimeNeedRepresentation.Mapping.mapMachine_control,
      control, PrimeNeedRepresentation.Mapping.mapControl, representation,
      PolarizedNeedMachine.extension, localStep_state]

/-- No administrative transition or receipt is inserted into old executions. -/
theorem step_map
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (machine : ScopedNeedMachine.NeedMachine Head Operation Effect StableFault NativeFault m) :
    (PrimeNeedReference.step (ScopedNeedMachine.spec primitive) machine).map representation.mapMachine =
      PrimeNeedLocalSteps.step (PolarizedNeedMachine.extension primitive) (representation.mapMachine machine) := by
  rw [extension_step_eq_reference]
  exact (compatible primitive).step_map machine

theorem advance_map
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (machine : ScopedNeedMachine.NeedMachine Head Operation Effect StableFault NativeFault m) :
    (PrimeNeedReference.advance (ScopedNeedMachine.spec primitive) machine).map representation.mapMachine =
      PrimeNeedLocalSteps.advance (PolarizedNeedMachine.extension primitive) (representation.mapMachine machine) := by
  unfold PrimeNeedReference.advance PrimeNeedLocalSteps.advance
  rw [← step_map]
  cases PrimeNeedReference.step (ScopedNeedMachine.spec primitive) machine <;> rfl

/-- Full ordered bounded frontiers, including unfinished and failed machines,
are exactly the represented old frontiers at the same fuel. -/
theorem runFrontier_map
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (fuel : Nat)
    (machines : List (ScopedNeedMachine.NeedMachine Head Operation Effect StableFault NativeFault m)) :
    (PrimeNeedReference.runFrontier (ScopedNeedMachine.spec primitive) fuel machines).map
      representation.mapMachine =
    PrimeNeedLocalSteps.runFrontier (PolarizedNeedMachine.extension primitive) fuel
      (machines.map representation.mapMachine) := by
  induction fuel generalizing machines with
  | zero => rfl
  | succ fuel ih =>
      simp only [PrimeNeedReference.runFrontier, PrimeNeedLocalSteps.runFrontier,
        List.all_map, Function.comp_def, PrimeNeedRepresentation.Compatible.isHalted_map]
      split
      · rfl
      · rw [ih, List.map_flatMap, List.flatMap_map]
        simp only [advance_map]

theorem answers_map
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (fuel : Nat)
    (machine : ScopedNeedMachine.NeedMachine Head Operation Effect StableFault NativeFault m) :
    (PrimeNeedReference.answers (ScopedNeedMachine.spec primitive) fuel machine).map outcome =
      PrimeNeedLocalSteps.answers (PolarizedNeedMachine.extension primitive) fuel
        (representation.mapMachine machine) := by
  unfold PrimeNeedReference.answers PrimeNeedLocalSteps.answers
  change _ = (PrimeNeedLocalSteps.runFrontier (PolarizedNeedMachine.extension primitive) fuel
    ([machine].map representation.mapMachine)).filterMap haltedOutcome
  rw [← runFrontier_map]
  simp only [List.filterMap_map, List.map_filterMap, Function.comp_def,
    PrimeNeedRepresentation.Compatible.haltedOutcome_map, representation_outcome_eq]

/-- This projection checks old syntax rather than deleting new constructs.
Native and Need lexical environments remain present in the reconstructed source. -/
def toScopedClosure? (origin : PolarizedNeedMachine.Closure Head Operation Effect m) :
    Option (ScopedNeedMachine.Closure Head Operation Effect m) :=
  origin.code.toScopedNeed?.map fun code =>
    ⟨origin.n, origin.k, code, origin.native, origin.needs⟩

@[simp] theorem toScopedClosure?_closure (origin : ScopedNeedMachine.Closure Head Operation Effect m) :
    toScopedClosure? (closure origin) = some origin := by
  cases origin
  simp only [toScopedClosure?, closure, PolarizedNeed.Computation.toScopedNeed?_ofScopedNeed,
    Option.map_some]

theorem closure_injective :
    Function.Injective (closure (Head := Head) (Operation := Operation) (Effect := Effect) (m := m)) := by
  intro left right equal
  have projected := congrArg toScopedClosure? equal
  simpa only [toScopedClosure?_closure, Option.some.injEq] using projected

theorem fault_injective : Function.Injective (fault (NativeFault := NativeFault)) := by
  intro left right equal
  cases left <;> cases right <;> simp_all [fault]

theorem retry_injective : Function.Injective (retry (NativeFault := NativeFault)) := by
  intro left right equal
  cases left <;> cases right <;> simp_all [retry, fault_injective.eq_iff]

theorem outcome_injective :
    Function.Injective (outcome (Head := Head) (Operation := Operation) (Effect := Effect)
      (StableFault := StableFault) (NativeFault := NativeFault) (m := m)) := by
  intro left right equal
  cases left <;> cases right <;> simp_all [outcome, retry_injective.eq_iff]

/-- Native answers and both old fault classes reflect, not merely preserve,
bounded execution membership. The stronger frontier law also retains order. -/
theorem answer_mem_iff
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (fuel : Nat)
    (machine : ScopedNeedMachine.NeedMachine Head Operation Effect StableFault NativeFault m)
    (result : ScopedNeedMachine.Outcome Head StableFault NativeFault m) :
    outcome result ∈ PrimeNeedLocalSteps.answers (PolarizedNeedMachine.extension primitive) fuel
        (representation.mapMachine machine) ↔
      result ∈ PrimeNeedReference.answers (ScopedNeedMachine.spec primitive) fuel machine := by
  rw [← answers_map, List.mem_map]
  constructor
  · rintro ⟨original, member, equal⟩
    exact outcome_injective equal ▸ member
  · intro member
    exact ⟨result, member, rfl⟩

theorem outcome_not_thunk_fault (result : ScopedNeedMachine.Outcome Head StableFault NativeFault m) :
    outcome (Operation := Operation) (Effect := Effect) result ≠
      .retryableFault (.domain .expectedThunk) := by
  cases result with
  | value term => simp [outcome]
  | stableFault error => simp [outcome]
  | retryableFault reason =>
      cases reason with
      | domain error => cases error <;> simp [outcome, retry, fault]
      | _ => simp [outcome, retry]

/-- Raw old programs, including failed programs and arbitrary represented
heaps, cannot acquire a new thunk-polarity fault through the embedding. -/
theorem no_new_thunk_fault
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (fuel : Nat)
    (machine : ScopedNeedMachine.NeedMachine Head Operation Effect StableFault NativeFault m) :
    .retryableFault (.domain .expectedThunk) ∉
      PrimeNeedLocalSteps.answers (PolarizedNeedMachine.extension primitive) fuel
        (representation.mapMachine machine) := by
  rw [← answers_map, List.mem_map]
  rintro ⟨result, _, equal⟩
  exact outcome_not_thunk_fault result equal

/-- The actual cached-force successor preserves the chosen native payload and
adds exactly its ordinary observation receipt. It does not force a thunk. -/
theorem cached_native_step
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (machine : ScopedNeedMachine.NeedMachine Head Operation Effect StableFault NativeFault m)
    {cell : CellId} {stack : List (Frame (ScopedNeedMachine.Resume Head Operation Effect m))}
    {origin : ScopedNeedMachine.Closure Head Operation Effect m} {term : Tm Head m}
    (control : machine.control = .force cell stack)
    (cached : machine.world.heap.lookup cell = some ⟨origin, .value term⟩) :
    PrimeNeedLocalSteps.step (PolarizedNeedMachine.extension primitive) (representation.mapMachine machine) =
      [finished (representation.mapMachine machine)
        (recorded (representation.mapWorld machine.world) (.observe cell (.value (.returned (.native term)))))
        (.returned (.value (.returned (.native term)))
          (stack.map (representation (StableFault := StableFault) (NativeFault := NativeFault)).mapFrame))
        1 0 1 0] := by
  rw [← step_map, ScopedNeedMachine.cached_force_step primitive machine control cached]
  rfl

/-- A genuine ordinary thunk force is outside the old local-state image.
The witness is its actual nonempty local transition, not a renamed source tag. -/
theorem thunk_force_outside_state_image {n v k : Nat}
    (code : PolarizedNeed.Computation Head Operation Effect n v k)
    (native : Sub Head n m) (values : Fin v → PolarizedNeedMachine.RuntimeValue Head Operation Effect m)
    (needs : Fin k → CellId) (continuation : PolarizedNeedMachine.Kont Head Operation Effect m)
    (source : ScopedNeedMachine.Local Head Operation Effect StableFault NativeFault m) :
    state source ≠ .evaluate ⟨n, v, k, .forceThunk (.thunk code), native, values, needs⟩ continuation := by
  intro equal
  have transition := congrArg PolarizedNeedMachine.localStep equal
  rw [localStep_state, PolarizedNeedMachine.ordinary_force_local] at transition
  cases transition

#print axioms finish_outcome
#print axioms deliver_outcome
#print axioms compatible
#print axioms localStep_state
#print axioms step_map
#print axioms runFrontier_map
#print axioms answers_map
#print axioms closure_injective
#print axioms outcome_injective
#print axioms answer_mem_iff
#print axioms no_new_thunk_fault
#print axioms cached_native_step
#print axioms thunk_force_outside_state_image

end PolarizedNeedEmbedding
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
