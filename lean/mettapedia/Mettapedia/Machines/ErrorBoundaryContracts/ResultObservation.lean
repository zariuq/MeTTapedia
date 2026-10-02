import Mettapedia.Machines.RunContracts.ScopedOutcome
import Mettapedia.Machines.RunContracts.Completion

/-!
# Explicit result observation at a declared handler boundary

The existing raised/value distinction is preserved in a reversible tagged
representation. A fused producer emits those tags after the existing pure,
branch-local handler stack, without materializing an intermediate unhandled
collection. Its correspondence is with the independently specified observation
judgment, including occurrence multiplicity.

Three policies are deliberately different: observe each independent branch,
stop the protected search at its first raise, and atomically collect a scope.
These finite observation models are not a new specification of PeTTa catch.
Capturing a value or fault does not complete an interrupted enclosing producer.
The same model also does not claim that catching a fault rolls back IO.

No native evaluator, foreign exception adapter, recursive search, or effectful
handler distribution is verified here. In a strict language a surface handler
must receive a suspended computation before its body is evaluated.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ErrorBoundaryContracts.ResultObservation

open RunContracts.ScopedOutcome
open RunContracts.Completion

variable {Value Fault Effect State : Type}

/-- This adapter observes the control constructor, never the payload spelling. -/
def toResult : Outcome Value Fault → Except Fault Value
  | .value value => .ok value
  | .raised fault => .error fault

def fromResult : Except Fault Value → Outcome Value Fault
  | .ok value => .value value
  | .error fault => .raised fault

@[simp] theorem from_to (outcome : Outcome Value Fault) :
    fromResult (toResult outcome) = outcome := by cases outcome <;> rfl

@[simp] theorem to_from (result : Except Fault Value) :
    toResult (fromResult result) = result := by cases result <;> rfl

theorem toResult_injective : Function.Injective (@toResult Value Fault) := by
  intro left right equal
  simpa using congrArg fromResult equal

def branchResults (outcomes : List (Outcome Value Fault)) : List (Except Fault Value) :=
  outcomes.map toResult

theorem branchResults_roundtrip (outcomes : List (Outcome Value Fault)) :
    (branchResults outcomes).map fromResult = outcomes := by
  simp [branchResults, List.map_map, Function.comp_def]

theorem branchResults_length (outcomes : List (Outcome Value Fault)) :
    (branchResults outcomes).length = outcomes.length := by simp [branchResults]

theorem branchResults_append (left right : List (Outcome Value Fault)) :
    branchResults (left ++ right) = branchResults left ++ branchResults right := by
  simp [branchResults]

theorem branchResults_perm {left right : List (Outcome Value Fault)}
    (permuted : left.Perm right) : (branchResults left).Perm (branchResults right) :=
  permuted.map toResult

/-- A producer with an explicit output continuation. This is pure: no law
here licenses evaluating effectful search branches in the reverse order. -/
def collectInto (handlers : List (Handler Value Fault)) :
    Computation Value Fault → List (Except Fault Value) → List (Except Fault Value)
  | .pure value, tail => ((route handlers (.value value)).toList.map toResult) ++ tail
  | .raise fault, tail => ((route handlers (.raised fault)).toList.map toResult) ++ tail
  | .empty, tail => tail
  | .choice left right, tail => collectInto handlers left (collectInto handlers right tail)
  | .handle body handler, tail => collectInto (handler :: handlers) body tail

theorem collectInto_eq (program : Computation Value Fault)
    (handlers : List (Handler Value Fault)) (tail : List (Except Fault Value)) :
    collectInto handlers program tail = branchResults (execute handlers program) ++ tail := by
  induction program generalizing handlers tail with
  | pure value => rfl
  | raise fault => rfl
  | empty => rfl
  | choice left right ihLeft ihRight =>
      simp only [collectInto, ihLeft, ihRight, execute, branchResults_append, List.append_assoc]
  | handle body handler ih => exact ih _ _

/-- The optimization is checked against the relational observation semantics,
not just a second name for the producer implementation. -/
theorem collectInto_observes (program : Computation Value Fault)
    (observations : List (Outcome Value Fault)) (specified : Observes program observations) :
    collectInto [] program [] = branchResults observations := by
  rw [collectInto_eq, (execute_iff program observations).mpr specified, List.append_nil]

theorem collectInto_composes (program : Computation Value Fault)
    (handlers : List (Handler Value Fault)) (left right : List (Except Fault Value)) :
    collectInto handlers program (left ++ right) = collectInto handlers program left ++ right := by
  simp only [collectInto_eq, List.append_assoc]

/-- A selective handler forwards every nonselected raised fault unchanged. -/
def catchOnly (accepts : Fault → Bool) (recover : Fault → Value) : Handler Value Fault :=
  fun fault => some (if accepts fault then .value (recover fault) else .raised fault)

theorem catchOnly_value (accepts : Fault → Bool) (recover : Fault → Value) (value : Value) :
    handleOne (catchOnly accepts recover) (.value value) = some (.value value) := rfl

theorem catchOnly_unselected (accepts : Fault → Bool) (recover : Fault → Value)
    (fault : Fault) (unselected : accepts fault = false) :
    handleOne (catchOnly accepts recover) (.raised fault) = some (.raised fault) := by
  simp [handleOne, catchOnly, unselected]

theorem catchOnly_selected (accepts : Fault → Bool) (recover : Fault → Value)
    (fault : Fault) (selected : accepts fault = true) :
    handleOne (catchOnly accepts recover) (.raised fault) = some (.value (recover fault)) := by
  simp [handleOne, catchOnly, selected]

/-- Strict sequencing invokes the value continuation only after an argument
returns a value. A raised argument bypasses an ordinary function body. -/
def andThen {Next : Type} (argument : Outcome Value Fault)
    (continuation : Value → Outcome Next Fault) : Outcome Next Fault :=
  match argument with
  | .value value => continuation value
  | .raised fault => .raised fault

theorem raised_argument_bypasses_function {Next : Type} (fault : Fault)
    (continuation : Value → Outcome Next Fault) :
    andThen (.raised fault) continuation = .raised fault := rfl

/-- This explicit control observer has access to the tagged outcome; an
ordinary value-only continuation does not. The native handler must therefore
be installed before evaluating a suspended body. -/
def protect (outcome : Outcome Value Fault) : Outcome (Except Fault Value) Fault :=
  .value (toResult outcome)

theorem protect_reflect (outcome : Outcome Value Fault) :
    andThen (protect outcome) fromResult = outcome := by
  cases outcome <;> rfl

/-- Prefix observation at a scope that abandons remaining alternatives on a
raise. It does not claim those abandoned alternatives were executed. -/
def scopeResults : List (Outcome Value Fault) → List (Except Fault Value)
  | [] => []
  | .value value :: rest => .ok value :: scopeResults rest
  | .raised fault :: _ => [.error fault]

/-- Pure fold of the supplied observations. A fault discards the value buffer.
This function alone says nothing about whether the supplied list is complete;
`checkedAtomicCollect` additionally checks the producer stop. -/
def atomicCollect : List (Outcome Value Fault) → Except Fault (List Value)
  | [] => .ok []
  | .value value :: rest => (atomicCollect rest).map (List.cons value)
  | .raised fault :: _ => .error fault

theorem scopeResults_prefix (outcomes : List (Outcome Value Fault)) :
    (scopeResults outcomes).IsPrefix (branchResults outcomes) := by
  induction outcomes with
  | nil => exact ⟨[], rfl⟩
  | cons outcome rest ih =>
      cases outcome with
      | value value =>
          obtain ⟨suffix, same⟩ := ih
          exact ⟨suffix, by simpa [scopeResults, branchResults, toResult] using congrArg (List.cons (.ok value)) same⟩
      | raised fault => exact ⟨branchResults rest, rfl⟩

theorem value_only_policies_agree (values : List Value) :
    scopeResults (values.map (Outcome.value : Value → Outcome Value Fault)) = values.map Except.ok ∧
    atomicCollect (values.map (Outcome.value : Value → Outcome Value Fault)) = .ok values := by
  induction values with
  | nil => exact ⟨rfl, rfl⟩
  | cons value rest ih => simp [scopeResults, atomicCollect, ih.1, ih.2, Except.map]

/-- Reifying already observed faults does not change the producer's completion
tag. A prefix of values is not an exhaustive result merely because it is tagged. -/
theorem capture_preserves_completion (demand : Demand)
    (outcomes : List (Outcome Value Fault)) (stop : ProducerStop State Fault) :
    completeB demand (branchResults outcomes).length stop =
      completeB demand outcomes.length stop := by rw [branchResults_length]

theorem capture_cannot_complete_interruption (demand : Demand)
    (outcomes : List (Outcome Value Fault)) (reason : ResourceInterruption) :
    completeB demand (branchResults outcomes).length
      (ProducerStop.observed (State := State) (Fault := Fault) (.interrupted reason)) = false := by
  cases demand <;> rfl

/-- Admission for an exhaustive atomic observation. `none` means no completed
collection is certified, not an empty answer or a successfully handled error.
The enclosing runner retains the original stop reason for reporting. -/
def checkedAtomicCollect (outcomes : List (Outcome Value Fault))
    (stop : ProducerStop State Fault) : Option (Except Fault (List Value)) :=
  if completeB .exhaustive outcomes.length stop then some (atomicCollect outcomes) else none

theorem checkedAtomicCollect_iff (outcomes : List (Outcome Value Fault))
    (stop : ProducerStop State Fault) (result : Except Fault (List Value)) :
    checkedAtomicCollect outcomes stop = some result ↔
      ObservationComplete .exhaustive outcomes stop ∧ atomicCollect outcomes = result := by
  unfold checkedAtomicCollect
  by_cases complete : completeB .exhaustive outcomes.length stop = true
  · simp [complete, (completeB_iff .exhaustive outcomes stop).mp complete]
  · have incomplete : ¬ ObservationComplete .exhaustive outcomes stop := by
      simpa only [completeB_iff] using complete
    simp [complete, incomplete]

theorem checkedAtomicCollect_interrupted (outcomes : List (Outcome Value Fault))
    (reason : ResourceInterruption) :
    checkedAtomicCollect outcomes
      (ProducerStop.observed (State := State) (Fault := Fault) (.interrupted reason)) = none := rfl

/-- An already executed effect prefix is retained across result reification.
This representation has no implicit transaction or compensating action. -/
structure EffectfulObservation (Effect Value Fault : Type) where
  effects : List Effect
  outcome : Outcome Value Fault
  deriving DecidableEq, Repr

def EffectfulObservation.capture (observation : EffectfulObservation Effect Value Fault) :
    List Effect × Except Fault Value := (observation.effects, toResult observation.outcome)

def EffectfulObservation.restore (observation : List Effect × Except Fault Value) :
    EffectfulObservation Effect Value Fault := ⟨observation.1, fromResult observation.2⟩

theorem effectful_roundtrip (observation : EffectfulObservation Effect Value Fault) :
    EffectfulObservation.restore observation.capture = observation := by
  cases observation
  simp [EffectfulObservation.restore, EffectfulObservation.capture]

namespace Controls

def mixed : List (Outcome Nat String) := [.value 7, .raised "bad", .value 8]

theorem handler_boundary_changes_observation :
    branchResults mixed = [.ok 7, .error "bad", .ok 8] ∧
    scopeResults mixed = [.ok 7, .error "bad"] ∧
    atomicCollect mixed = .error "bad" := by decide

theorem first_fault_changes_under_reordering :
    atomicCollect ([.raised "left", .raised "right"] : List (Outcome Nat String)) ≠
      atomicCollect [.raised "right", .raised "left"] ∧
    (branchResults ([.raised "left", .raised "right"] : List (Outcome Nat String))).Perm
      (branchResults [.raised "right", .raised "left"]) := by
  constructor
  · decide
  · exact List.Perm.swap _ _ []

theorem returned_error_value_is_still_success :
    toResult (.value (Except.error "ordinary data") : Outcome (Except String Nat) String) =
      .ok (.error "ordinary data") := rfl

theorem repeated_occurrences_survive :
    branchResults ([.value 7, .value 7, .raised "bad", .raised "bad"] :
      List (Outcome Nat String)) = [.ok 7, .ok 7, .error "bad", .error "bad"] := rfl

theorem no_answers_is_not_a_fault :
    branchResults ([] : List (Outcome Nat String)) = [] ∧
    branchResults [.raised "bad"] ≠ ([] : List (Except String Nat)) := by decide

theorem selective_handler_does_not_hide_programmer_fault :
    handleOne (catchOnly (fun fault : String => fault == "temporary") (fun _ => 0))
      (.raised "programmer fault") = some (.raised "programmer fault") := by decide

theorem ordinary_eager_wrapper_cannot_catch_argument :
    andThen (.raised "bad" : Outcome Nat String) (fun value => .value (Except.ok value)) =
      (Outcome.raised "bad" : Outcome (Except String Nat) String) ∧
    protect (.raised "bad" : Outcome Nat String) = .value (.error "bad") := by decide

theorem capture_does_not_undo_recorded_effect :
    (EffectfulObservation.capture
      (⟨["sent"], .raised "lost acknowledgement"⟩ : EffectfulObservation String Nat String)).1 =
      ["sent"] := rfl

theorem same_values_do_not_determine_completion (reason : ResourceInterruption) :
    checkedAtomicCollect ([.value 7] : List (Outcome Nat String))
      (ProducerStop.observed (State := Unit) .complete) = some (.ok [7]) ∧
    checkedAtomicCollect ([.value 7] : List (Outcome Nat String))
      (ProducerStop.observed (State := Unit) (.interrupted reason)) = none := by
  constructor <;> rfl

end Controls
end Mettapedia.Machines.ErrorBoundaryContracts.ResultObservation
