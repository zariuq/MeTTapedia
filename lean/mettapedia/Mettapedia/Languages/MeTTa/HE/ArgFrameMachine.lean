-- LLM primer: Follows LetChainResumption.lean closely.
-- runFromSource terminates on `remaining.length` (decreases by 1 each step).
-- `unfold runFromSource` is needed in proofs since simp doesn't auto-unfold
-- well-founded recursive functions.

import Mettapedia.Languages.MeTTa.HE.NondeterminismCarrier

/-!
# Argument Evaluation Frame Machine

Frame-based argument evaluator for MeTTa's `InterpretArgs`
(EvalSpec.lean lines 255-294). Eliminates C recursion in
`interpret_function_args` (eval.c:8112).

## Architecture

Two-frame machine following LetChainResumption:
- **ArgSourceFrame**: tracks remaining `(arg, type)` pairs
- **ArgBodyFrame**: drains eval1 results for current arg, source suspended

## C Seam Mapping

| Lean notion | C location |
|-------------|-----------|
| `ArgSourceFrame.remaining` | `orig_args[idx..nargs]` with types |
| `ArgBodyFrame.pending` | results from `arg_os` at eval.c:8492 |
| `resume?` | what C must become: yield one result, save frame |
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## Frame Definitions -/

structure ArgSourceFrame where
  done      : List Atom
  remaining : List (Atom × Atom)
  env       : Bindings
  deriving Repr

structure ArgBodyFrame where
  pending   : ResultList
  suspended : ArgSourceFrame
  deriving Repr

inductive ArgEvalFrame where
  | source (frame : ArgSourceFrame)
  | body (frame : ArgBodyFrame)
  deriving Repr

namespace ArgEvalFrame

/-! ## Eager Semantics -/

/-- Eagerly evaluate all remaining arguments left-to-right, threading bindings.
    Terminates because `remaining` shrinks by one each recursive call. -/
def runFromSource (eval1 : Atom → Atom → Bindings → ResultList) :
    ArgSourceFrame → ResultList
  | ⟨done, [], env⟩ => [(.expression done, env)]
  | ⟨done, (arg, ty) :: rest, env⟩ =>
    (eval1 arg ty env).flatMap fun (argVal, env') =>
      runFromSource eval1 ⟨done ++ [argVal], rest, env'⟩
termination_by sf => sf.remaining.length

/-- Total residual results for a resumable frame. -/
def run (eval1 : Atom → Atom → Bindings → ResultList) : ArgEvalFrame → ResultList
  | .source sf => runFromSource eval1 sf
  | .body bf => bf.pending.flatMap fun (argVal, env') =>
      runFromSource eval1 ⟨bf.suspended.done ++ [argVal],
                            bf.suspended.remaining, env'⟩

/-! ## Resume Protocol -/

/-- Enter the next pending argument. -/
def nextFromSource? (eval1 : Atom → Atom → Bindings → ResultList) :
    ArgSourceFrame → Option (ResultPair × ArgEvalFrame)
  | ⟨_, [], _⟩ => none
  | ⟨done, (arg, ty) :: rest, env⟩ =>
    match eval1 arg ty env with
    | [] => none
    | r :: rs => some (r, .body ⟨rs, ⟨done, rest, env⟩⟩)

/-- Resume one step: yield at most one eval1 result pair. -/
def resume? (eval1 : Atom → Atom → Bindings → ResultList) :
    ArgEvalFrame → Option (ResultPair × ArgEvalFrame)
  | .source sf => nextFromSource? eval1 sf
  | .body ⟨[], sf⟩ => nextFromSource? eval1 sf
  | .body ⟨r :: rs, sf⟩ => some (r, .body ⟨rs, sf⟩)

/-! ## Correctness Theorems -/

theorem runFromSource_nil (eval1 : Atom → Atom → Bindings → ResultList)
    (done : List Atom) (env : Bindings) :
    runFromSource eval1 ⟨done, [], env⟩ = [(.expression done, env)] := by
  unfold runFromSource; rfl

theorem run_source_eq (eval1 : Atom → Atom → Bindings → ResultList)
    (sf : ArgSourceFrame) :
    run eval1 (.source sf) = runFromSource eval1 sf := rfl

theorem run_body_eq (eval1 : Atom → Atom → Bindings → ResultList)
    (bf : ArgBodyFrame) :
    run eval1 (.body bf) = bf.pending.flatMap fun (argVal, env') =>
      runFromSource eval1 ⟨bf.suspended.done ++ [argVal],
                            bf.suspended.remaining, env'⟩ := rfl

/-- Source cons unfolds to flatMap. -/
@[simp]
theorem runFromSource_cons (eval1 : Atom → Atom → Bindings → ResultList)
    (done : List Atom) (arg ty : Atom) (rest : List (Atom × Atom)) (env : Bindings) :
    runFromSource eval1 ⟨done, (arg, ty) :: rest, env⟩ =
      (eval1 arg ty env).flatMap fun (argVal, env') =>
        runFromSource eval1 ⟨done ++ [argVal], rest, env'⟩ := by
  simp [runFromSource]

/-- If `nextFromSource?` yields one result, the source semantics splits. -/
theorem nextFromSource?_decompose (eval1 : Atom → Atom → Bindings → ResultList) :
    ∀ sf r frame,
      nextFromSource? eval1 sf = some (r, frame) →
      runFromSource eval1 sf =
        (runFromSource eval1 ⟨sf.done ++ [r.1], sf.remaining.tail, r.2⟩)
        ++ run eval1 frame
  | ⟨_, [], _⟩, _, _, h => by simp [nextFromSource?] at h
  | ⟨done, (arg, ty) :: rest, env⟩, r, frame, h => by
    simp only [nextFromSource?] at h
    cases heval : eval1 arg ty env with
    | nil => simp [heval] at h
    | cons hd tl =>
      simp [heval] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [runFromSource_cons, heval]
      simp [List.flatMap_cons, run]

/-- Source frame exhaustion. -/
theorem nextFromSource?_none_iff (eval1 : Atom → Atom → Bindings → ResultList) :
    ∀ sf : ArgSourceFrame, nextFromSource? eval1 sf = none ↔
      sf.remaining = [] ∨
      ∃ arg ty rest, sf.remaining = (arg, ty) :: rest ∧ eval1 arg ty sf.env = []
  | ⟨_, [], _⟩ => by simp [nextFromSource?]
  | ⟨done, (arg, ty) :: rest, env⟩ => by
    constructor
    · intro h
      simp only [nextFromSource?] at h
      right; refine ⟨arg, ty, rest, rfl, ?_⟩
      cases heval : eval1 arg ty env with
      | nil => rfl
      | cons hd tl => simp [heval] at h
    · intro h
      rcases h with heq | ⟨a, t, r, heq, hemp⟩
      · simp at heq
      · simp only [List.cons.injEq, Prod.mk.injEq] at heq
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
        simp [nextFromSource?, hemp]

/-- Resume on body frame with pending results: peels one result. -/
theorem resume?_body_cons (eval1 : Atom → Atom → Bindings → ResultList)
    (r0 : ResultPair) (rs : ResultList) (sf : ArgSourceFrame) :
    resume? eval1 (.body ⟨r0 :: rs, sf⟩) = some (r0, .body ⟨rs, sf⟩) := rfl

/-- Body run decomposition: cons splits into first + rest. -/
theorem run_body_cons (eval1 : Atom → Atom → Bindings → ResultList)
    (r0 : ResultPair) (rs : ResultList) (sf : ArgSourceFrame) :
    run eval1 (.body ⟨r0 :: rs, sf⟩) =
      runFromSource eval1 ⟨sf.done ++ [r0.1], sf.remaining, r0.2⟩
      ++ run eval1 (.body ⟨rs, sf⟩) := by
  simp [run, List.flatMap_cons]

/-- Bag-level preservation per body resume step. -/
theorem resume?_body_toBag_step (eval1 : Atom → Atom → Bindings → ResultList)
    (r0 : ResultPair) (rs : ResultList) (sf : ArgSourceFrame) :
    ResultList.toBag (run eval1 (.body ⟨r0 :: rs, sf⟩)) =
      ResultList.toBag (runFromSource eval1 ⟨sf.done ++ [r0.1], sf.remaining, r0.2⟩)
      + ResultList.toBag (run eval1 (.body ⟨rs, sf⟩)) := by
  rw [run_body_cons]
  simp [ResultList.toBag]

/-- Resume on empty body delegates to source. -/
theorem resume?_body_nil (eval1 : Atom → Atom → Bindings → ResultList)
    (sf : ArgSourceFrame) :
    resume? eval1 (.body ⟨[], sf⟩) = nextFromSource? eval1 sf := rfl

/-! ## Examples -/

private def sampleEval : Atom → Atom → Bindings → ResultList
  | .symbol "x", _, b => [(.symbol "x_val", b)]
  | .symbol "y", _, b => [(.symbol "y_val1", b), (.symbol "y_val2", b)]
  | _, _, _ => []

example : nextFromSource? sampleEval
    ⟨[], [(.symbol "x", .symbol "T")], Bindings.empty⟩ =
    some ((.symbol "x_val", Bindings.empty),
          .body ⟨[], ⟨[], [], Bindings.empty⟩⟩) := by
  simp [nextFromSource?, sampleEval]

example : nextFromSource? sampleEval
    ⟨[], [(.symbol "y", .symbol "T")], Bindings.empty⟩ =
    some ((.symbol "y_val1", Bindings.empty),
          .body ⟨[(.symbol "y_val2", Bindings.empty)],
                 ⟨[], [], Bindings.empty⟩⟩) := by
  simp [nextFromSource?, sampleEval]

example : nextFromSource? sampleEval
    ⟨[], [(.symbol "z", .symbol "T")], Bindings.empty⟩ = none := by
  simp [nextFromSource?, sampleEval]

example : resume? sampleEval
    (.body ⟨[(.symbol "y_val2", Bindings.empty)],
            ⟨[], [], Bindings.empty⟩⟩) =
    some ((.symbol "y_val2", Bindings.empty),
          .body ⟨[], ⟨[], [], Bindings.empty⟩⟩) := rfl

end ArgEvalFrame

end Mettapedia.Languages.MeTTa.HE
