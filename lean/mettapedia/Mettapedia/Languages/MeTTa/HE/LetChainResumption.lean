import Mettapedia.Languages.MeTTa.HE.NondeterminismCarrier
import Mettapedia.Languages.MeTTa.HE.ProducerChoicePoint

/-!
# Let/Chain Resumption Refinement

Formalizes the missing middle layer between CeTTa's current eager
`OutcomeSet` collection for `let`/`chain` and a future resumable evaluator.

The key idea is a two-frame machine:
- a **source frame** enumerates source evaluation results
- a **body frame** enumerates the results of the body for one selected source
  result while remembering the suspended source continuation

This is the abstraction needed for heap-allocated resumption frames:
one call to `resume?` delivers exactly one body result, and the returned frame
contains all remaining work.

## Key results

- `run_source_eq_flatMap` — source-frame execution matches eager `flatMap`
- `resume?_decompose` — each resume step peels one result from the same list
- `resume?_none_iff_run_nil` — no resume step iff no residual results remain
- `resume?_toBag_step` — one resume step preserves bag semantics

## Connection to CeTTa

In `/home/zar/claude/c-projects/CeTTa-mork/src/eval.c`, both `let` and `chain`
currently evaluate the source expression eagerly into an `OutcomeSet`, then
iterate those results to evaluate bodies. This file proves that the same
observable behavior can be recovered by a resumable source/body frame split.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- A **source frame** stores the remaining source results whose bodies have not
    yet been entered. -/
structure SourceFrame where
  remaining : ResultList
  deriving Repr

/-- A **body frame** stores the pending body results for the current source
    result together with the suspended source continuation. -/
structure BodyFrame where
  pending : ResultList
  suspended : SourceFrame
  deriving Repr

/-- Resumable let/chain state: either we are choosing the next source result, or
    we are draining the current body's remaining results. -/
inductive LetChainFrame where
  | source (frame : SourceFrame)
  | body (frame : BodyFrame)
  deriving Repr

namespace LetChainFrame

/-- Eagerly run all bodies for a source-result list. This is the direct
    `flatMap` semantics that CeTTa currently materializes via `OutcomeSet`. -/
def runFromSource (body : ResultPair → ResultList) : ResultList → ResultList
  | [] => []
  | r :: rs => body r ++ runFromSource body rs

/-- Total residual results represented by a resumable frame. -/
def run (body : ResultPair → ResultList) : LetChainFrame → ResultList
  | .source sf => runFromSource body sf.remaining
  | .body bf => bf.pending ++ runFromSource body bf.suspended.remaining

/-- Enter the next source result whose body is nonempty, if one exists. The
    first body result is delivered immediately; the remaining body results stay
    suspended in a body frame. -/
def nextFromSource? (body : ResultPair → ResultList) :
    ResultList → Option (ResultPair × LetChainFrame)
  | [] => none
  | r :: rs =>
      match body r with
      | [] => nextFromSource? body rs
      | b :: bs => some (b, .body ⟨bs, ⟨rs⟩⟩)

/-- Resume one step of let/chain-style evaluation, yielding at most one result.
    If the current body still has pending results, keep draining it. Otherwise,
    resume the suspended source frame and enter the next body. -/
def resume? (body : ResultPair → ResultList) :
    LetChainFrame → Option (ResultPair × LetChainFrame)
  | .source sf => nextFromSource? body sf.remaining
  | .body ⟨[], sf⟩ => nextFromSource? body sf.remaining
  | .body ⟨r :: rs, sf⟩ => some (r, .body ⟨rs, sf⟩)

/-- The eager source runner is exactly `flatMap`. -/
theorem runFromSource_eq_flatMap (body : ResultPair → ResultList) :
    ∀ rs : ResultList, runFromSource body rs = rs.flatMap body
  | [] => by simp [runFromSource]
  | r :: rs => by
      simp [runFromSource, runFromSource_eq_flatMap body rs]

/-- Starting from a source frame yields the same results as eager `flatMap`. -/
theorem run_source_eq_flatMap (body : ResultPair → ResultList) (sf : SourceFrame) :
    run body (.source sf) = sf.remaining.flatMap body := by
  simpa [run] using runFromSource_eq_flatMap body sf.remaining

/-- A body frame's residual semantics is its pending body results followed by
    the eager semantics of the suspended source continuation. -/
theorem run_body_eq_append (body : ResultPair → ResultList) (bf : BodyFrame) :
    run body (.body bf) = bf.pending ++ bf.suspended.remaining.flatMap body := by
  simp [run, runFromSource_eq_flatMap]

/-- If `nextFromSource?` yields one result, the eager source semantics splits
    into that head result followed by the residual frame. -/
theorem nextFromSource?_decompose (body : ResultPair → ResultList) :
    ∀ rs r frame,
      nextFromSource? body rs = some (r, frame) →
      runFromSource body rs = r :: run body frame
  | [], _, _, h => by simp [nextFromSource?] at h
  | src :: rest, r, frame, h => by
      cases hbody : body src with
      | nil =>
          simp [nextFromSource?, hbody] at h
          simpa [runFromSource, hbody] using
            nextFromSource?_decompose body rest r frame h
      | cons out outs =>
          simp [nextFromSource?, hbody] at h
          rcases h with ⟨rfl, rfl⟩
          simp [run, runFromSource, hbody]

/-- A source frame is exhausted exactly when `nextFromSource?` cannot produce a
    next result. -/
theorem nextFromSource?_none_iff_runFromSource_nil (body : ResultPair → ResultList) :
    ∀ rs : ResultList, nextFromSource? body rs = none ↔ runFromSource body rs = []
  | [] => by simp [nextFromSource?, runFromSource]
  | src :: rest => by
      cases hbody : body src with
      | nil =>
          simpa [nextFromSource?, runFromSource, hbody] using
            nextFromSource?_none_iff_runFromSource_nil body rest
      | cons out outs =>
          simp [nextFromSource?, runFromSource, hbody]

/-- One resume step peels exactly one result from the frame's residual
    semantics. This is the key refinement theorem for a heap-resumable
    source/body evaluator. -/
theorem resume?_decompose (body : ResultPair → ResultList) :
    ∀ frame r next,
      resume? body frame = some (r, next) →
      run body frame = r :: run body next
  | .source sf, r, next, h => by
      exact nextFromSource?_decompose body sf.remaining r next h
  | .body ⟨[], sf⟩, r, next, h => by
      simpa [resume?, run] using nextFromSource?_decompose body sf.remaining r next h
  | .body ⟨r0 :: rs, sf⟩, r, next, h => by
      cases h
      simp [run]

/-- No resume step is available exactly when the frame's residual semantics is
    empty. -/
theorem resume?_none_iff_run_nil (body : ResultPair → ResultList) :
    ∀ frame : LetChainFrame, resume? body frame = none ↔ run body frame = []
  | .source sf => by
      exact nextFromSource?_none_iff_runFromSource_nil body sf.remaining
  | .body ⟨[], sf⟩ => by
      simpa [resume?, run] using nextFromSource?_none_iff_runFromSource_nil body sf.remaining
  | .body ⟨r :: rs, sf⟩ => by
      simp [resume?, run]

/-- Bag-level corollary of `resume?_decompose`: each yielded result plus the
    residual frame accounts for exactly the same multiset of answers as the
    original frame. -/
theorem resume?_toBag_step (body : ResultPair → ResultList)
    (frame next : LetChainFrame) (r : ResultPair)
    (h : resume? body frame = some (r, next)) :
    ResultList.toBag (run body frame) =
      ({r} : ResultBag) + ResultList.toBag (run body next) := by
  rw [resume?_decompose body frame r next h]
  simp [ResultList.toBag]

end LetChainFrame

/-! ## Structural call selection and completed empty frontiers

`none` records an inapplicable equation. `some []` records an entered equation
whose computation completed without a return. These are different observations:
only a wholly inapplicable call can remain its original syntax. The matcher and
body evaluator supply these observations; this layer does not prove their native
implementation. The reference folds completed equation observations, whereas the
machine inspects one occurrence or publishes one pending return per transition.
-/

namespace StructuralCall

abbrev Attempts := List (Option ResultList)

/-- Direct, source-ordered equation semantics, retaining applicability even
when every entered body is empty. -/
def referenceAttempts : Attempts → Option ResultList
  | [] => none
  | none :: rest => referenceAttempts rest
  | some results :: rest =>
      some (results ++ (referenceAttempts rest).getD [])

def reference (source : ResultPair) (attempts : Attempts) : ResultList :=
  (referenceAttempts attempts).getD [source]

/-- Separate pending returns from candidate selection. Applicability remains
owned after the selected body and its pending returns have been retired. -/
structure Frame where
  source : ResultPair
  remaining : Attempts
  pending : ResultList
  entered : Bool

inductive Transition where
  | inspect (next : Frame)
  | publish (result : ResultPair) (next : Frame)
  | complete

def step (frame : Frame) : Transition :=
  match frame.pending with
  | result :: rest => .publish result { frame with pending := rest }
  | [] =>
      match frame.remaining with
      | none :: rest => .inspect { frame with remaining := rest }
      | some results :: rest => .inspect
          { frame with remaining := rest, pending := results, entered := true }
      | [] => if frame.entered then .complete else
          .publish frame.source { frame with entered := true }

def residual (frame : Frame) : ResultList :=
  frame.pending ++ if frame.entered then
    (referenceAttempts frame.remaining).getD []
  else reference frame.source frame.remaining

/-- Empty entered bodies cannot turn into an unmatched call after completion. -/
theorem entered_empty_has_no_fallback (source : ResultPair) :
    reference source [some []] = [] := by
  simp [reference, referenceAttempts]

theorem unmatched_preserves_source (source : ResultPair) (attempts : Attempts)
    (unmatched : referenceAttempts attempts = none) :
    reference source attempts = [source] := by
  simp [reference, unmatched]

/-- Each transition preserves the entire ordered residual, including duplicate
returns and their bindings. Publication removes exactly one physical occurrence. -/
theorem step_residual (frame : Frame) :
    match step frame with
    | .inspect next => residual frame = residual next
    | .publish result next => residual frame = result :: residual next
    | .complete => residual frame = [] := by
  rcases frame with ⟨source, remaining, pending, entered⟩
  cases pending with
  | cons result rest => simp [step, residual]
  | nil =>
      cases remaining with
      | nil => cases entered <;> simp [step, residual, reference, referenceAttempts]
      | cons attempt rest =>
          cases attempt with
          | none => simp [step, residual, reference, referenceAttempts]
          | some results =>
              cases entered <;> simp [step, residual, reference, referenceAttempts]

/-- An administrative allowance counts inspections and publications. It does
not pretend that inspecting a candidate is an authored body firing. -/
def run : Nat → Frame → ResultList × Option Frame
  | 0, frame => ([], some frame)
  | fuel + 1, frame =>
      match step frame with
      | .complete => ([], none)
      | .inspect next => run fuel next
      | .publish result next =>
          let tail := run fuel next
          (result :: tail.1, tail.2)

def savedResidual : Option Frame → ResultList
  | none => []
  | some frame => residual frame

/-- Stopping at any allowance preserves both the accepted prefix and the exact
undelivered frontier. This is stronger than agreement of answer sets or counts. -/
theorem run_preserves_residual (fuel : Nat) (frame : Frame) :
    (run fuel frame).1 ++ savedResidual (run fuel frame).2 = residual frame := by
  induction fuel generalizing frame with
  | zero => simp [run, savedResidual]
  | succ fuel ih =>
      have preserved := step_residual frame
      cases nextStep : step frame with
      | complete =>
          simp only [nextStep] at preserved
          simpa [run, nextStep, savedResidual] using preserved
      | inspect next =>
          simp only [nextStep] at preserved
          simpa [run, nextStep, preserved] using ih next
      | publish result next =>
          simp only [nextStep] at preserved
          simpa only [run, nextStep, List.cons_append, ih next] using preserved.symm

/-- A quantitative measure includes each remaining body return, each pending
return, candidate inspections, and the one possible unmatched publication. -/
def work (frame : Frame) : Nat :=
  frame.remaining.length +
  ((frame.remaining.filterMap id).map List.length).sum +
  frame.pending.length + (if frame.entered then 0 else 1) + 1

theorem step_work_decreases (frame : Frame) :
    match step frame with
    | .inspect next => work next < work frame
    | .publish _ next => work next < work frame
    | .complete => True := by
  rcases frame with ⟨source, remaining, pending, entered⟩
  cases pending with
  | cons result rest => simp [step, work]
  | nil =>
      cases remaining with
      | nil => cases entered <;> simp [step, work]
      | cons attempt rest =>
          cases attempt with
          | none => simp [step, work]
          | some results => cases entered <;> simp [step, work] <;> omega

/-- The derived bound guarantees completion; allowance exhaustion below the
bound retains a frame instead of becoming a false claim of exhaustion. -/
theorem run_complete_of_work_le (fuel : Nat) (frame : Frame)
    (bound : work frame ≤ fuel) : (run fuel frame).2 = none := by
  induction fuel generalizing frame with
  | zero => have : 0 < work frame := by simp [work]
            omega
  | succ fuel ih =>
      have decreased := step_work_decreases frame
      cases nextStep : step frame with
      | complete => simp [run, nextStep]
      | inspect next =>
          simp only [nextStep] at decreased
          simpa [run, nextStep] using ih next (by omega)
      | publish result next =>
          simp only [nextStep] at decreased
          simpa [run, nextStep] using ih next (by omega)

/-- The independently defined ordered call semantics is recovered within the
inspection/publication bound. Body evaluation work is not counted by this layer. -/
theorem run_initial_eq_reference (source : ResultPair) (attempts : Attempts) :
    let initial : Frame := ⟨source, attempts, [], false⟩
    (run (work initial) initial).1 = reference source attempts := by
  dsimp
  let initial : Frame := ⟨source, attempts, [], false⟩
  have complete := run_complete_of_work_le (work initial) initial (by rfl)
  have preserved := run_preserves_residual (work initial) initial
  simpa [complete, savedResidual, residual, initial] using preserved

example : reference (.symbol "call", Bindings.empty)
    [none, some [(.symbol "a", Bindings.empty), (.symbol "a", Bindings.empty)],
     some [], some [(.symbol "b", Bindings.empty)]] =
    [(.symbol "a", Bindings.empty), (.symbol "a", Bindings.empty),
     (.symbol "b", Bindings.empty)] := by
  simp [reference, referenceAttempts]

end StructuralCall


/-! ## Delimited producer completion

HE's caller consumes the completed producer, after success priority, rather
than consuming each raw firing as it arrives. The machine below stores returns
in reverse order and publishes only at its completion transition. The direct
reference filters the original ordered list; neither is defined by the other.
Body execution and native service costs remain outside this administrative
account.
-/

namespace ProducerCompletion

/-- The expression-completion policy used by HE: retain successful returns if
any exist, and otherwise retain errors. Bindings travel with each occurrence. -/
def reference (returns : ResultList) : ResultList :=
  let successes := returns.filter fun pair => !isErrorAtom pair.1
  if successes.isEmpty then returns.filter fun pair => isErrorAtom pair.1
  else successes

structure Frame where
  savedRev : ResultList
  remaining : ResultList

inductive Step where
  | collect (next : Frame)
  | complete (returns : ResultList)

/-- A collection transition saves a producer return without invoking its
caller. Only exhaustion permits a completion transition. -/
def step (frame : Frame) : Step :=
  match frame.remaining with
  | [] => .complete (reference frame.savedRev.reverse)
  | result :: rest => .collect ⟨result :: frame.savedRev, rest⟩

/-- The independently specified result still owed to the caller. -/
def residual (frame : Frame) : ResultList :=
  reference (frame.savedRev.reverse ++ frame.remaining)

/-- An exhausted budget retains the exact completion frame and publishes no
partial producer. -/
def run : Nat → Frame → Option ResultList × Option Frame
  | 0, frame => (none, some frame)
  | fuel + 1, frame =>
      match step frame with
      | .collect next => run fuel next
      | .complete returns => (some returns, none)

/-- A raw return preserves the complete ordered residual, including bindings,
errors and duplicate occurrences. -/
theorem collect_preserves_residual (frame next : Frame)
    (transition : step frame = .collect next) :
    residual next = residual frame := by
  rcases frame with ⟨saved, remaining⟩
  cases remaining with
  | nil => simp [step] at transition
  | cons result rest =>
      cases transition
      simp [residual, List.reverse_cons, List.append_assoc]

/-- Completion returns the whole residual, rather than a prefix observed
before a later successful alternative suppresses earlier errors. -/
theorem complete_eq_residual (frame : Frame) (returns : ResultList)
    (transition : step frame = .complete returns) :
    returns = residual frame := by
  rcases frame with ⟨saved, remaining⟩
  cases remaining with
  | nil => simpa [step, residual] using transition.symm
  | cons result rest => simp [step] at transition

/-- Every finite execution either publishes exactly its specified completion
or retains a frame with exactly that completion still owed. -/
theorem run_preserves_completion (fuel : Nat) (frame : Frame) :
    match run fuel frame with
    | (some returns, none) => returns = residual frame
    | (none, some next) => residual next = residual frame
    | _ => False := by
  induction fuel generalizing frame with
  | zero => simp [run]
  | succ fuel ih =>
      cases transition : step frame with
      | collect next =>
          have preserved := collect_preserves_residual frame next transition
          simpa only [run, transition, preserved] using ih next
      | complete returns =>
          simpa [run, transition] using complete_eq_residual frame returns transition

/-- Collecting all remaining occurrences takes one transition each, followed
by a single completion transition. -/
def work (frame : Frame) : Nat := frame.remaining.length + 1

theorem run_complete_at_work (frame : Frame) :
    run (work frame) frame = (some (residual frame), none) := by
  rcases frame with ⟨saved, remaining⟩
  induction remaining generalizing saved with
  | nil => simp [work, run, step, residual]
  | cons result rest ih =>
      simpa [work, run, step, residual, List.reverse_cons,
        List.append_assoc] using ih (result :: saved)

/-- A budget below completion cannot publish a raw return prematurely. -/
theorem run_before_completion (fuel : Nat) (frame : Frame)
    (budget : fuel ≤ frame.remaining.length) : (run fuel frame).1 = none := by
  induction fuel generalizing frame with
  | zero => rfl
  | succ fuel ih =>
      rcases frame with ⟨saved, remaining⟩
      cases remaining with
      | nil => simp at budget
      | cons result rest =>
          simp only [List.length_cons] at budget
          simpa [run, step] using ih ⟨result :: saved, rest⟩
            (by change fuel ≤ rest.length; omega)

/-- The native last-alternative path can return directly when its bank is
empty. No earlier occurrence is discarded, and a fault remains a fault. -/
theorem reference_singleton (result : ResultPair) : reference [result] = [result] := by
  cases classification : isErrorAtom result.1 <;> simp [reference, classification]

/-- Completion followed by a consumer is ordered composition. In particular,
completion is performed before an answerless consumer erases the successes. -/
def consume (body : ResultPair → ResultList) (returns : ResultList) : ResultList :=
  (reference returns).flatMap body

private def fault : ResultPair :=
  (.expression [.symbol "Error", .symbol "source", .symbol "fault"], Bindings.empty)
private def success : ResultPair := (.symbol "ok", Bindings.empty)

/-- Positive control: ordered duplicates survive completion, while an earlier
error is suppressed by these successful alternatives. -/
example : reference [fault, success, success] = [success, success] := by
  simp [reference, fault, success, isErrorAtom]

/-- Negative control: streaming a raw producer into its caller gives a
spurious error when the caller returns no answer for each successful value. -/
example : consume (fun pair => if isErrorAtom pair.1 then [pair] else [])
    [fault, success] = [] ∧
    ([fault, success].flatMap fun pair =>
      if isErrorAtom pair.1 then [pair] else []) = [fault] := by
  simp [consume, reference, fault, success, isErrorAtom]

end ProducerCompletion

/-! ## Positive and negative examples -/

private def samplePair (name : String) : ResultPair :=
  (.symbol name, Bindings.empty)

private def sampleBody : ResultPair → ResultList
  | (.symbol "x", _) => [samplePair "x1", samplePair "x2"]
  | (.symbol "y", _) => [samplePair "y1"]
  | _ => []

/-- Positive example: one source result can suspend a body frame with multiple
    remaining body results. -/
example :
    LetChainFrame.resume? sampleBody
      (.source ⟨[samplePair "x", samplePair "y"]⟩) =
      some (samplePair "x1",
        .body ⟨[samplePair "x2"], ⟨[samplePair "y"]⟩⟩) := by
  simp [LetChainFrame.resume?, LetChainFrame.nextFromSource?, sampleBody, samplePair]

/-- Negative example: source results whose bodies are empty contribute no
    resumable work. -/
example :
    LetChainFrame.resume? sampleBody
      (.source ⟨[samplePair "z"]⟩) = none := by
  simp [LetChainFrame.resume?, LetChainFrame.nextFromSource?, sampleBody, samplePair]

end Mettapedia.Languages.MeTTa.HE
