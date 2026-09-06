import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedMachine

/-!
# Executed first-class closure and sharing discriminators

These controls execute source constructors through the candidate local-step
extension of the owned Need machine. Outcome views retain native answers and
faults but classify closure values; full closures, heap entries and receipts
remain in the frontier. Native terms here are raw syntax. The controls are
execution evidence, not an independent claim of native logical admission.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeedMachineExamples

open PrimeNeedReference PolarizedNeed PolarizedNeedMachine

abbrev Source := Computation Nat Unit Nat 0 0 0
abbrev ExampleMachine := NeedMachine Nat Unit Nat Unit Unit 0

def primitive (_ : Unit) (term : Tm Nat 0) : Produced (Tm Nat 0) Unit Unit := .value term
def machineExtension : NeedExtension Nat Unit Nat Unit Unit 0 := extension primitive

def initial (source : Source) : ExampleMachine where
  world := ⟨0, [], .empty, .empty, 0, 0⟩
  control := .run (.evaluate ⟨0, 0, 0, source, ids, Fin.elim0, Fin.elim0⟩ .done) []

def frontier (fuel : Nat) (source : Source) : List ExampleMachine :=
  PrimeNeedLocalSteps.runFrontier machineExtension fuel [initial source]

inductive AnswerView where
  | native (term : Tm Nat 0)
  | thunk
  | packNative (index : Tm Nat 0) (value : AnswerView)
  | nativeFunction
  | valueFunction
  deriving DecidableEq, Repr

def valueView : RuntimeValue Nat Unit Nat 0 → AnswerView
  | .native term => .native term
  | .thunk _ _ _ _ => .thunk
  | .packNative index value => .packNative index (valueView value)

def answerView : Answer Nat Unit Nat 0 → AnswerView
  | .returned value => valueView value
  | .nativeFunction _ => .nativeFunction
  | .valueFunction _ => .valueFunction

def outcomeView : Outcome Nat Unit Nat Unit Unit 0 → Produced AnswerView Unit (Fault Unit)
  | .value answer => .value (answerView answer)
  | .stableFault fault => .stableFault fault
  | .retryableFault reason => .retryableFault reason

def effects (machine : ExampleMachine) : List Nat :=
  machine.world.receipts.nodes.reverse.filterMap fun node =>
    match node.payload with
    | .effect effect => some effect
    | _ => none

def observations (fuel : Nat) (source : Source) :=
  (frontier fuel source).map fun machine =>
    ((haltedOutcome machine).map outcomeView, effects machine)

def producer {n v k : Nat} : Computation Nat Unit Nat n v k :=
  .emit 7 (.choose (.returnValue (.native (.head 10))) (.returnValue (.native (.head 20))))

/-- An ordinary thunk returned as a value and forced at two source sites. -/
def ordinaryTwice : Source :=
  .bindValue (.returnValue (.thunk producer))
    (.sequenceSigma (.forceThunk (.variable 0)) (.forceThunk (.variable 0)))

/-- The execution of the received thunk, not just its construction, is shared. -/
def sharedExecution : Source :=
  .bindValue (.returnValue (.thunk producer))
    (.letNeed (.forceThunk (.variable 0)) (.sequenceSigma (.forceNeed 0) (.forceNeed 0)))

/-- Sharing a returned thunk does not change ordinary force into Need force. -/
def sharedConstruction : Source :=
  .letNeed (.returnValue (.thunk producer))
    (.bindValue (.forceNeed 0)
      (.sequenceSigma (.forceThunk (.variable 0)) (.forceThunk (.variable 0))))

def unusedThunk : Source := .returnValue (.thunk producer)

/-- A returned higher-order function accepts a thunked function and a thunked
argument. All function bodies are source trees. -/
def returnedHigherOrder : Source :=
  .bindValue (.returnValue (.thunk applyThunked))
    (.valueApply
      (.valueApply (.forceThunk (.variable 0))
        (.thunk (.valueLambda (.forceThunk (.variable 0)))))
      (.thunk producer))

/-- The exported closure captures native 10 and Need producer 30. Later
native 99, Need producer 20 and a new value parameter cannot capture them. -/
def mixedCapture : Source :=
  .bindNative (.returnValue (.native (.head 10)))
    (.letNeed (.returnValue (.native (.head 30)))
      (.bindValue
        (.returnValue (.thunk
          (.sequenceSigma (.forceNeed 0) (.returnValue (.native (.var 1))))))
        (.bindNative (.returnValue (.native (.head 99)))
          (.letNeed (.returnValue (.native (.head 20)))
            (.valueApply (.valueLambda (.forceThunk (.variable 1)))
              (.thunk (.forceNeed 0)))))))

/-- An effect-selected native index travels together with a closure retaining
that index. Unpacking opens native and value binders simultaneously. This raw
observer then forgets the index: no outer dependent result type is claimed. -/
def indexedClosure : Source :=
  .bindValue
    (.bindNative producer
      (.returnValue (.packNative (.var 0)
        (.thunk (.returnValue (.native (.refl (.var 0))))))))
    (.unpackNative (.variable 0) (.forceThunk (.variable 0)))

/-- Retain the selected index with the obtained proof instead of exporting
an unindexed projection of an index-dependent result. -/
def retainedIndexedResult : Source :=
  .bindValue
    (.bindNative producer
      (.returnValue (.packNative (.var 0)
        (.thunk (.returnValue (.native (.refl (.var 0))))))))
    (.unpackNative (.variable 0)
      (.bindNative (.forceThunk (.variable 0))
        (.returnValue (.packNative (.var 1) (.native (.var 0))))))

/-- The Need cell caches a computation function answer; it is applied twice.
Effects before the lambda occur once, effects in its body occur per call. -/
def sharedFunction : Source :=
  .letNeed (.emit 3 (.nativeLambda (.emit 4 (.returnValue (.native (.var 0))))))
    (.sequenceSigma (.nativeApply (.forceNeed 0) (.head 10))
      (.nativeApply (.forceNeed 0) (.head 20)))

def appliedEffectfulFunction : Source :=
  .nativeApply (.emit 3 (.nativeLambda (.emit 4 (.returnValue (.native (.var 0)))))) (.head 10)

def badForce : Source := .forceThunk (.native (.head 10))

def selfApplication {n v k : Nat} : Value Nat Unit Nat n v k :=
  .thunk (.valueLambda (.valueApply (.forceThunk (.variable 0)) (.variable 0)))

def rawLoop : Source := .valueApply (.forceThunk selfApplication) selfApplication

theorem ordinary_forcing_reexecutes :
    observations 96 ordinaryTwice =
      [(some (.value (.native (.pair (.head 10) (.head 10)))), [7, 7]),
       (some (.value (.native (.pair (.head 10) (.head 20)))), [7, 7]),
       (some (.value (.native (.pair (.head 20) (.head 10)))), [7, 7]),
       (some (.value (.native (.pair (.head 20) (.head 20)))), [7, 7])] := by
  rfl

theorem explicit_need_shares_execution :
    observations 96 sharedExecution =
      [(some (.value (.native (.pair (.head 10) (.head 10)))), [7]),
       (some (.value (.native (.pair (.head 20) (.head 20)))), [7])] := by
  rfl

theorem ordinary_force_is_not_shared_force :
    observations 96 ordinaryTwice ≠ observations 96 sharedExecution := by
  rw [ordinary_forcing_reexecutes, explicit_need_shares_execution]
  decide

theorem cached_thunk_still_reexecutes :
    observations 96 sharedConstruction = observations 96 ordinaryTwice := by
  rw [ordinary_forcing_reexecutes]
  rfl

theorem caching_construction_is_not_caching_execution :
    observations 96 sharedConstruction ≠ observations 96 sharedExecution := by
  rw [cached_thunk_still_reexecutes]
  exact ordinary_force_is_not_shared_force

theorem unused_thunk_does_not_execute :
    observations 32 unusedThunk = [(some (.value .thunk), [])] := by
  rfl

theorem source_higher_order_application :
    observations 96 returnedHigherOrder =
      [(some (.value (.native (.head 10))), [7]),
       (some (.value (.native (.head 20))), [7])] := by
  rfl

theorem closure_retains_all_three_scopes :
    observations 96 mixedCapture =
      [(some (.value (.native (.pair (.head 30) (.head 10)))), [])] := by
  rfl

theorem later_binders_do_not_capture :
    observations 96 mixedCapture ≠
      [(some (.value (.native (.pair (.head 20) (.head 99)))), [])] := by
  rw [closure_retains_all_three_scopes]
  decide

theorem selected_index_stays_with_closure :
    observations 96 indexedClosure =
      [(some (.value (.native (.refl (.head 10)))), [7]),
       (some (.value (.native (.refl (.head 20)))), [7])] := by
  rfl

theorem dependent_result_keeps_its_index :
    observations 96 retainedIndexedResult =
      [(some (.value (.packNative (.head 10) (.native (.refl (.head 10))))), [7]),
       (some (.value (.packNative (.head 20) (.native (.refl (.head 20))))), [7])] := by
  rfl

theorem dependent_packet_is_not_unindexed_projection :
    observations 96 retainedIndexedResult ≠ observations 96 indexedClosure := by
  rw [dependent_result_keeps_its_index, selected_index_stays_with_closure]
  decide

theorem computation_function_sharing_preserves_call_effects :
    observations 96 sharedFunction =
      [(some (.value (.native (.pair (.head 10) (.head 20)))), [3, 4, 4])] := by
  rfl

theorem application_retains_function_prefix_effects :
    observations 32 appliedEffectfulFunction = [(some (.value (.native (.head 10))), [3, 4])] := by
  rfl

theorem native_data_is_not_a_thunk :
    observations 32 badForce = [(some (.retryableFault (.domain .expectedThunk)), [])] := by
  rfl

theorem raw_self_application_retains_unfinished_state :
    observations 12 rawLoop = [(none, [])] ∧
      (frontier 12 rawLoop).map isHalted = [false] ∧
      (frontier 12 rawLoop).map (fun machine => machine.work.allocations) = [0] := by
  exact ⟨rfl, rfl, rfl⟩

/-- The embedded native sequencing still allocates and demands a producer.
Its native answer agrees with beta reduction, but allocation is retained. -/
def allocatedReturn : Source :=
  .bindNative (.returnValue (.native (.head 10))) (.returnValue (.native (.var 0)))

def directReturn : Source := .returnValue (.native (.head 10))

theorem sequence_unit_at_native_observation :
    observations 32 allocatedReturn = observations 32 directReturn := by
  rfl

theorem sequence_unit_not_exact_allocation_equality :
    (frontier 32 allocatedReturn).map (fun machine => machine.work.allocations) = [1] ∧
      (frontier 32 directReturn).map (fun machine => machine.work.allocations) = [0] := by
  exact ⟨rfl, rfl⟩

theorem sequence_unit_does_not_preserve_full_frontier :
    frontier 32 allocatedReturn ≠ frontier 32 directReturn := by
  intro equal
  have same := congrArg (List.map (fun machine : ExampleMachine => machine.work.allocations)) equal
  rw [sequence_unit_not_exact_allocation_equality.1,
    sequence_unit_not_exact_allocation_equality.2] at same
  contradiction

#print axioms ordinary_forcing_reexecutes
#print axioms explicit_need_shares_execution
#print axioms ordinary_force_is_not_shared_force
#print axioms cached_thunk_still_reexecutes
#print axioms caching_construction_is_not_caching_execution
#print axioms unused_thunk_does_not_execute
#print axioms source_higher_order_application
#print axioms closure_retains_all_three_scopes
#print axioms later_binders_do_not_capture
#print axioms selected_index_stays_with_closure
#print axioms dependent_result_keeps_its_index
#print axioms dependent_packet_is_not_unindexed_projection
#print axioms computation_function_sharing_preserves_call_effects
#print axioms application_retains_function_prefix_effects
#print axioms native_data_is_not_a_thunk
#print axioms raw_self_application_retains_unfinished_state
#print axioms sequence_unit_at_native_observation
#print axioms sequence_unit_not_exact_allocation_equality
#print axioms sequence_unit_does_not_preserve_full_frontier

end PolarizedNeedMachineExamples
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
