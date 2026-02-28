import Mettapedia.Languages.ProcessCalculi.MORK.Space

/-!
# MORK: Three-Phase Execution Protocol

MORK's execution uses priority-scheduled exec rules with a three-phase protocol:

```
Phase 1 — UNFOLD  (priorities  0..31):  Spawn N sub-queries + wait token
Phase 2 — BASE    (priorities 32..63):  Resolve leaf queries directly
Phase 3 — FOLD    (priorities 64..95):  Wait + all N sub-results → assembled result
```

This file formalises the phase structure and the three canonical step types.
The bridge to MQ-calculus COMM is in `MORKCommBridge.lean`.

## Spec warning

MORK is an evolving system. This formalization captures the current (2026-02)
three-phase protocol as described in `mork_backend.rs`. Future versions may:
- Change priority bands or introduce more phases
- Change how sub-query IDs are constructed (`sub-0-$qid` vs `(sub $k $qid)`)
- Extend the fold protocol to support streaming/incremental results

**Canary theorems** at the bottom of this file will FAIL TO COMPILE if the
stated invariants are violated by a future change to this file.  Update the
spec here AND in `MORKCommBridge.lean` whenever MORK evolves.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.OSLF.MeTTaCore (Atom)

/-! ## Phase type -/

/-- The three phases of MORK execution. -/
inductive Phase where
  | unfold : Phase   -- Phase 1: spawn sub-queries
  | base   : Phase   -- Phase 2: resolve leaf cases
  | fold   : Phase   -- Phase 3: assemble sub-results
  deriving Repr, DecidableEq

/-- Priority band for each phase (inclusive on both ends). -/
def phaseRange : Phase → ℕ × ℕ
  | .unfold => (0,  31)
  | .base   => (32, 63)
  | .fold   => (64, 95)

/-- A priority falls within its phase's range. -/
def inPhase (n : ℕ) (ph : Phase) : Prop :=
  (phaseRange ph).1 ≤ n ∧ n ≤ (phaseRange ph).2

/-! ## Step types -/

/-- An UNFOLD step: query `qid` is expanded into N sub-queries and a wait token.
    Phase 1 rule fires when `(metta-query qid lhs)` is in the space.
    It removes the original query and adds N sub-queries plus a wait atom. -/
structure UnfoldStep where
  /-- The original query ID atom (e.g., `(metta-query q0 expr)`) -/
  qid      : Atom
  /-- Sub-query IDs spawned (e.g., `(sub-0 q0)`, `(sub-1 q0)`, …) -/
  subQids  : List Atom
  /-- Wait token synchronizing fold; contains context for assembling -/
  waitAtom : Atom
  /-- Priority of the unfold exec rule -/
  priority : ℕ
  /-- Priority is in the unfold phase band -/
  inUnfold : inPhase priority .unfold
  deriving Repr

/-- A BASE step: query `qid` resolves directly (leaf case).
    Phase 2 rule fires when `(metta-query qid lhs)` is in the space and lhs
    matches a base case equation.  Produces `(metta-result qid rhs)`. -/
structure BaseStep where
  /-- The query ID atom -/
  qid    : Atom
  /-- The direct result atom -/
  result : Atom
  /-- Priority of the base exec rule -/
  priority : ℕ
  /-- Priority is in the base phase band -/
  inBase : inPhase priority .base
  deriving Repr

/-- A FOLD step: the wait token plus ALL sub-results are consumed and
    assembled into the final result.
    Phase 3 rule fires when:
    - `waitAtom` is in the space
    - All `subResults` (one per sub-query) are in the space
    Produces `(metta-result qid assembled)` and removes the wait + sub-results. -/
structure FoldStep where
  /-- The original query ID -/
  qid        : Atom
  /-- Wait token (consumed) -/
  waitAtom   : Atom
  /-- Sub-results consumed (ordered: sub-0 result first) -/
  subResults : List Atom
  /-- The assembled final result -/
  assembled  : Atom
  /-- Priority of the fold exec rule -/
  priority   : ℕ
  /-- Priority is in the fold phase band -/
  inFold     : inPhase priority .fold
  deriving Repr

/-! ## Phase ordering lemmas -/

/-- Phase ranges are mutually disjoint. -/
theorem phase_ranges_disjoint (p q : Phase) (h : p ≠ q)
    (n : ℕ) (hp : inPhase n p) (hq : inPhase n q) : False := by
  cases p <;> cases q <;> simp_all [inPhase, phaseRange] <;> omega

/-- Unfold priorities are strictly less than base priorities. -/
theorem unfold_lt_base (nu nb : ℕ) (hu : inPhase nu .unfold) (hb : inPhase nb .base) :
    nu < nb := by
  simp [inPhase, phaseRange] at *; omega

/-- Base priorities are strictly less than fold priorities. -/
theorem base_lt_fold (nb nf : ℕ) (hb : inPhase nb .base) (hf : inPhase nf .fold) :
    nb < nf := by
  simp [inPhase, phaseRange] at *; omega

/-- Unfold priorities are strictly less than fold priorities. -/
theorem unfold_lt_fold (nu nf : ℕ) (hu : inPhase nu .unfold) (hf : inPhase nf .fold) :
    nu < nf := by
  simp [inPhase, phaseRange] at *; omega

/-- Phase priority ordering is transitive: unfold < base < fold. -/
theorem phase_priority_monotone :
    ∀ nu nb nf : ℕ,
    inPhase nu .unfold → inPhase nb .base → inPhase nf .fold →
    nu < nb ∧ nb < nf := by
  intro nu nb nf hu hb hf
  exact ⟨unfold_lt_base nu nb hu hb, base_lt_fold nb nf hb hf⟩

/-! ## Step invariants -/

/-- An unfold step must spawn at least one sub-query. -/
def UnfoldStep.isNontrivial (step : UnfoldStep) : Prop :=
  step.subQids.length ≥ 1

/-- A fold step's sub-results list matches the unfold step's sub-queries. -/
def FoldStep.isCompatibleWith (fold : FoldStep) (unfold : UnfoldStep) : Prop :=
  fold.qid = unfold.qid ∧
  fold.subResults.length = unfold.subQids.length

/-- For a binary (N=2) fold step, the sub-results list has exactly 2 entries. -/
def FoldStep.isBinary (fold : FoldStep) : Prop :=
  fold.subResults.length = 2

/-- The "zero" sub-result in a binary fold (first sub-result, index 0). -/
def FoldStep.subResult0 (fold : FoldStep) (h : fold.isBinary) : Atom :=
  fold.subResults[0]'(by simp [FoldStep.isBinary] at h; omega)

/-- The "one" sub-result in a binary fold (second sub-result, index 1). -/
def FoldStep.subResult1 (fold : FoldStep) (h : fold.isBinary) : Atom :=
  fold.subResults[1]'(by simp [FoldStep.isBinary] at h; omega)

/-! ## Space transitions -/

/-- Apply an unfold step to a space: remove original query, add sub-queries + wait. -/
def applyUnfold (s : Space) (step : UnfoldStep) : Space :=
  let s1 := s.erase step.qid
  let s2 := step.subQids.foldl (· ∪ {·}) s1
  s2 ∪ {step.waitAtom}

/-- Apply a base step to a space: remove query, add result. -/
def applyBase (s : Space) (step : BaseStep) : Space :=
  (s.erase step.qid) ∪ {step.result}

/-- Apply a fold step to a space: remove wait + sub-results, add assembled result. -/
def applyFold (s : Space) (step : FoldStep) : Space :=
  let s1 := s.erase step.waitAtom
  let s2 := step.subResults.foldl (· \ {·}) s1
  s2 ∪ {step.assembled}

/-! ## Canary theorems
    These must pass at compile time. If MORK's phase protocol changes, update here. -/

section CanaryPhases

-- Phase ranges are what the spec says
example : phaseRange .unfold = (0, 31)  := rfl
example : phaseRange .base   = (32, 63) := rfl
example : phaseRange .fold   = (64, 95) := rfl

-- Phase ranges are disjoint (proved above)
#check @phase_ranges_disjoint

-- Priority ordering is proven
#check @phase_priority_monotone

-- inPhase is decidable (for concrete priorities)
example : inPhase 10 .unfold := by simp [inPhase, phaseRange]
example : inPhase 50 .base   := by simp [inPhase, phaseRange]
example : inPhase 80 .fold   := by simp [inPhase, phaseRange]
example : ¬ inPhase 50 .unfold := by simp [inPhase, phaseRange]
example : ¬ inPhase 80 .base   := by simp [inPhase, phaseRange]

-- FoldStep.isBinary and sub-result accessors typecheck
#check @FoldStep.subResult0
#check @FoldStep.subResult1

end CanaryPhases

end Mettapedia.Languages.ProcessCalculi.MORK
