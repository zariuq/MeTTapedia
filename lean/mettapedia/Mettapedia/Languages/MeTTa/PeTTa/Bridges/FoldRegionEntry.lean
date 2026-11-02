import Mettapedia.Languages.MeTTa.PeTTa.FoldSourceBoundary
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldSurfaceClassifier

/-!
# Fold specialization after source operand evaluation

Source operands are prepared exactly once by the existing evaluator. The
completed observer may then select an ordered callback worker or an inferred
additive word worker. A failed specialization retains the captured list,
initial accumulator and resulting store for the reference fold continuation.
It never returns to the original pre-operand entrance.

The result retains the full request as data. This is a formal host adapter,
not C dispatch, a physical GC proof or a claim that arbitrary source pages
may be fused. Stronger page/prefix observers take the reference route before
evaluating operands.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldRegionEntry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open SpaceSemantics FoldSourceBoundary
open MeTTaIL.WireKit (number)

structure Driver (program : Program) (caller : Subst) (code : Code) (items : List Atom) (initial : Atom) where
  result : Atom
  returns : ∀ state, FoldSource.Evaluates program (code.callback caller) state items initial result

def compileDriver (budget : Nat) (program : Program) (caller : Subst) :
    (code : Code) → (items : List Atom) → (initial : Atom) → Option (Driver program caller code items initial)
  | .named _ _ head, items, initial => do
      let compiled ← FoldCallbackExtraction.prepare budget program (.named head) items initial
      return ⟨compiled.result, compiled.returns⟩
  | .inline _ _ accumulatorName itemName body, items, initialAtom => do
      let certificate ← AdditiveFoldSource.infer caller accumulatorName itemName body
      match decoded : AdditiveFoldSource.naturals items with
      | none => none
      | some values =>
          match initialDecoded : AdditiveFoldSource.natural initialAtom with
          | none => none
          | some initial =>
              match accepted : AdditiveFoldSource.words certificate.weight values initial with
              | none => none
              | some value =>
                  return ⟨number value, fun state => by
                    rw [AdditiveFoldSource.naturals_exact items values decoded,
                      AdditiveFoldSource.natural_exact initialAtom initial initialDecoded]
                    exact AdditiveFoldSource.words_source_exact certificate program state values initial value accepted⟩

structure Completion (request : Request) where
  after : Effects.State
  value : Atom
  source : Evaluates request.program request.caller request.code request.before after value

inductive Result (request : Request)
  | reference
  | handoff (saved : Handoff)
  | referenceFold (captured : Captured request.program request.caller request.code request.before)
  | completed (answer : Completion request)

def resolve (budget : Nat) (request : Request)
    (captured : Captured request.program request.caller request.code request.before) : Result request :=
  match compileDriver budget request.program request.caller request.code captured.items captured.initial with
  | none => .referenceFold captured
  | some driver => .completed ⟨captured.after, driver.result, captured.finish _ (driver.returns captured.after)⟩

theorem refused_driver_keeps_captured_entrance (budget : Nat) (request : Request)
    (captured : Captured request.program request.caller request.code request.before)
    (refused : compileDriver budget request.program request.caller request.code captured.items captured.initial = none) :
    resolve budget request captured = .referenceFold captured := by simp [resolve, refused]

theorem resolve_ne_reference (budget : Nat) (request : Request)
    (captured : Captured request.program request.caller request.code request.before) :
    resolve budget request captured ≠ .reference := by
  unfold resolve
  split <;> simp

def run (observer : FoldSurfaceClassifier.Observer) (listFuel initialFuel callbackBudget : Nat)
    (request : Request) : Result request :=
  match observer with
  | .callbackPrefixes | .sourcePage => .reference
  | .completed => match FoldSourceBoundary.prepare listFuel initialFuel request.program request.caller
      request.code request.before with
    | .reference => .reference
    | .handoff saved => .handoff saved
    | .ready captured => resolve callbackBudget request captured

structure Envelope where
  saved : Request
  result : Result saved

def retainedRun (observer : FoldSurfaceClassifier.Observer) (listFuel initialFuel callbackBudget : Nat)
    (request : Request) : Envelope :=
  ⟨request, run observer listFuel initialFuel callbackBudget request⟩

theorem exact_pages_decline_before_operands (listFuel initialFuel callbackBudget : Nat) (request : Request) :
    run .sourcePage listFuel initialFuel callbackBudget request = .reference := rfl

theorem prefixes_decline_before_operands (listFuel initialFuel callbackBudget : Nat) (request : Request) :
    run .callbackPrefixes listFuel initialFuel callbackBudget request = .reference := rfl

theorem source_request_retained (observer : FoldSurfaceClassifier.Observer)
    (listFuel initialFuel callbackBudget : Nat) (request : Request) :
    (retainedRun observer listFuel initialFuel callbackBudget request).saved = request := rfl

def observation {request : Request} : Result request → Option (Effects.State × Atom)
  | .completed answer => some (answer.after, answer.value)
  | .reference | .handoff _ | .referenceFold _ => none

theorem completed_source_exact (observer : FoldSurfaceClassifier.Observer)
    (listFuel initialFuel callbackBudget : Nat) (request : Request)
    (after : Effects.State) (value : Atom)
    (completed : observation (run observer listFuel initialFuel callbackBudget request) = some (after, value)) :
    Evaluates request.program request.caller request.code request.before after value := by
  cases result : run observer listFuel initialFuel callbackBudget request with
  | completed answer =>
      have same : answer.after = after ∧ answer.value = value := by simpa [observation, result] using completed
      obtain ⟨rfl, rfl⟩ := same
      exact answer.source
  | reference | handoff | referenceFold => simp [observation, result] at completed

/-- Backward uniqueness is supplied by the independent source sequencing
judgment, not just by the forward certificate attached to a result. -/
theorem completed_no_other_source_result (observer : FoldSurfaceClassifier.Observer)
    (listFuel initialFuel callbackBudget : Nat) (request : Request)
    (after otherAfter : Effects.State) (value otherValue : Atom)
    (completed : observation (run observer listFuel initialFuel callbackBudget request) = some (after, value))
    (other : Evaluates request.program request.caller request.code request.before otherAfter otherValue) :
    otherAfter = after ∧ otherValue = value :=
  evaluates_unique other (completed_source_exact observer listFuel initialFuel callbackBudget request after value completed)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldRegionEntry
