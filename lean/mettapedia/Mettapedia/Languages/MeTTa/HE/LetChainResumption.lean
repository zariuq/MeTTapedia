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
