import Mettapedia.Machines.FoldNativeCompletion

/-!
# Private scalar-fold attempts and ordinary fallback

A native attempt changes only its private accumulator. Successful native
steps must refine one pure, single-answer source callback at the captured
world. A later refusal restarts ordinary execution from the original world
and accumulator. Interruption is a separate terminal disposition and never
causes ordinary replay. This extends the existing fold-completion carrier;
it is not a proof of the C recognizer, signed-word implementation or arena.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PrivateScalarFold

variable {Value Item World : Type}

inductive Attempt (Value : Type)
  | value (result : Value)
  | refused
  | interrupted
  deriving DecidableEq

def attempt (nativeStep : Value → Item → Option Value) (cancel : Nat → Bool) :
    Nat → List Item → Value → Attempt Value
  | _, [], accumulator => .value accumulator
  | index, item :: rest, accumulator =>
      if cancel index then .interrupted
      else match nativeStep accumulator item with
        | none => .refused
        | some next => attempt nativeStep cancel (index + 1) rest next

/-- A local refinement includes purity and one successful source answer.
It does not postulate the whole fold's equality. -/
def StepRefines (sourceStep : FoldNativeCompletion.Step Value Item World)
    (nativeStep : Value → Item → Option Value) (world : World) : Prop :=
  ∀ accumulator item next, nativeStep accumulator item = some next →
    sourceStep world accumulator item = (world, .ok next)

theorem accepted_fold_refines (sourceStep : FoldNativeCompletion.Step Value Item World)
    (nativeStep : Value → Item → Option Value) (cancel : Nat → Bool)
    (world : World) (refines : StepRefines sourceStep nativeStep world)
    (index : Nat) (items : List Item) (initial result : Value)
    (accepted : attempt nativeStep cancel index items initial = .value result) :
    FoldNativeCompletion.produce sourceStep items world initial = (world, .ok result) := by
  induction items generalizing index initial with
  | nil => simpa [attempt, FoldNativeCompletion.produce] using accepted
  | cons item rest ih =>
    by_cases interrupted : cancel index = true
    · simp [attempt, interrupted] at accepted
    · cases step : nativeStep initial item with
      | none => simp [attempt, interrupted, step] at accepted
      | some next =>
        have tail := ih (index + 1) next (by simpa [attempt, interrupted, step] using accepted)
        simpa [FoldNativeCompletion.produce, refines initial item next step] using tail

inductive Outcome (Value World : Type)
  | completed (world : World) (reply : Except Value Value)
  | interrupted (world : World)
  deriving DecidableEq

def dispatch (sourceStep : FoldNativeCompletion.Step Value Item World)
    (nativeStep : Value → Item → Option Value) (cancel : Nat → Bool)
    (items : List Item) (world : World) (initial : Value) : Outcome Value World :=
  match attempt nativeStep cancel 0 items initial with
  | .value value => .completed world (.ok value)
  | .refused =>
      let result := FoldNativeCompletion.produce sourceStep items world initial
      .completed result.1 result.2
  | .interrupted => .interrupted world

theorem completed_exact (sourceStep : FoldNativeCompletion.Step Value Item World)
    (nativeStep : Value → Item → Option Value) (cancel : Nat → Bool)
    (items : List Item) (world : World) (initial : Value)
    (refines : StepRefines sourceStep nativeStep world) (after : World) (reply : Except Value Value)
    (completed : dispatch sourceStep nativeStep cancel items world initial = .completed after reply) :
    FoldNativeCompletion.produce sourceStep items world initial = (after, reply) := by
  cases tried : attempt nativeStep cancel 0 items initial with
  | value value =>
    have equal : world = after ∧ Except.ok value = reply := by simpa [dispatch, tried] using completed
    rw [← equal.1, ← equal.2]
    exact accepted_fold_refines sourceStep nativeStep cancel world refines 0 items initial value tried
  | refused =>
    have equal := Outcome.completed.inj (show
      Outcome.completed (FoldNativeCompletion.produce sourceStep items world initial).1
        (FoldNativeCompletion.produce sourceStep items world initial).2 = .completed after reply by
          simpa [dispatch, tried] using completed)
    exact Prod.ext equal.1 equal.2
  | interrupted => simp [dispatch, tried] at completed

theorem refusal_restarts_original (sourceStep : FoldNativeCompletion.Step Value Item World)
    (nativeStep : Value → Item → Option Value) (cancel : Nat → Bool)
    (items : List Item) (world : World) (initial : Value)
    (refused : attempt nativeStep cancel 0 items initial = .refused) :
    dispatch sourceStep nativeStep cancel items world initial =
      .completed (FoldNativeCompletion.produce sourceStep items world initial).1
        (FoldNativeCompletion.produce sourceStep items world initial).2 := by simp [dispatch, refused]

theorem interruption_never_replays (sourceStep : FoldNativeCompletion.Step Value Item World)
    (nativeStep : Value → Item → Option Value) (cancel : Nat → Bool)
    (items : List Item) (world : World) (initial : Value)
    (interrupted : attempt nativeStep cancel 0 items initial = .interrupted) :
    dispatch sourceStep nativeStep cancel items world initial = .interrupted world := by
  simp [dispatch, interrupted]

namespace Controls

def signedSource : FoldNativeCompletion.Step Int Int Unit := fun world accumulator item =>
  (world, .ok (accumulator + item))

/-- An exact-integer model of a checked signed range, not Int64 ABI verification. -/
def checkedSignedAdd (accumulator item : Int) : Option Int :=
  if -(2^63) ≤ accumulator + item ∧ accumulator + item < 2^63 then some (accumulator + item) else none

theorem signed_local_refinement : StepRefines signedSource checkedSignedAdd () := by
  intro accumulator item next accepted
  unfold checkedSignedAdd at accepted
  split at accepted
  · cases accepted; rfl
  · cases accepted

theorem negative_arithmetic_is_preserved :
    dispatch signedSource checkedSignedAdd (fun _ => false) [-5, 2] () 1 = .completed () (.ok (-2)) := by decide

theorem late_overflow_restarts_original :
    attempt checkedSignedAdd (fun _ => false) 0 [5, 2^63 - 1] 0 = .refused ∧
    dispatch signedSource checkedSignedAdd (fun _ => false) [5, 2^63 - 1] () 0 =
      .completed () (.ok (2^63 + 4)) := by decide

def effectfulFallback : FoldNativeCompletion.Step Int Int (List Int) := fun world accumulator item =>
  (world ++ [item], .ok (accumulator + item))

theorem cancellation_is_not_refusal :
    dispatch effectfulFallback checkedSignedAdd (fun index => index == 1) [5, 6] [] 0 = .interrupted [] ∧
    FoldNativeCompletion.produce effectfulFallback [5, 6] [] 0 = ([5, 6], .ok 11) := by decide

theorem purity_is_a_real_obligation : ¬ StepRefines effectfulFallback checkedSignedAdd [] := by
  intro falseRefinement
  have changed := falseRefinement 0 5 5 (by decide)
  cases changed

end Controls
end Mettapedia.Machines.PrivateScalarFold
