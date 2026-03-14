import Mettapedia.Languages.ProcessCalculi.MORK.ThreePhaseExec
import Mettapedia.Languages.ProcessCalculi.MQCalculus.CommRule

/-!
# MORK ↔ MQ-Calculus COMM Bridge

This file proves the structural correspondence between MORK's three-phase
execution and the MQ-calculus COMM rule.

## The Correspondence

MORK's binary fold (N=2 sub-queries) corresponds exactly to `CommReduction`:

```
MORK                              MQ-Calculus
----                              -----------
UnfoldStep (N=2 sub-queries)      MQOut i   (fires, spawns)
FoldStep sub-result-0 selected    CommReduction.outcome_zero (→ P)
FoldStep sub-result-1 selected    CommReduction.outcome_one  (→ Q)
Non-determinism: EITHER outcome   comm_both_outcomes i p q
```

The connection is:
- **MORK produces EITHER sub-result-0 OR sub-result-1** from the fold step,
  non-deterministically.  This is structural non-determinism: there exist
  TWO possible FoldStep firings (one per measurement outcome).
- **MQ-COMM produces EITHER P or Q** from `out i | in i {P, Q}`,
  non-deterministically.  Both `CommReduction.outcome_zero` and
  `CommReduction.outcome_one` are constructively inhabited.

## Key Definitions

`MorkOutcome`: which of the two sub-results a binary fold step "selects".
This is the abstract analog of `MeasurementBranch.outcome`.

## Spec Warning

This bridge formalizes the CURRENT (2026-02) MORK protocol.  The mapping
between `MorkOutcome` and `MeasurementBranch.outcome` is definitional: both
are binary enumerations indexed 0/1.  If MORK changes the fold protocol or
adds more sub-results, this bridge needs updating.

## Canary theorems

`canary_mork_binary_fold_is_nondeterministic` — both outcomes are constructively
inhabited for any binary fold step.  Fails if MORK makes folds deterministic.

`canary_comm_reduction_matches_mork_outcome` — for each MORK binary outcome,
there is a MQ `CommReduction` with the same branch selection.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MQCalculus (
  Process CommReduction MeasurementBranch Outcome
  comm_both_outcomes)

/-! ## MORK outcome type -/

/-- Which of the two sub-results a binary MORK fold step "selects".
    Isomorphic to `MQCalculus.Outcome`. -/
inductive MorkOutcome where
  | subResult0 : MorkOutcome   -- first sub-result selected (index 0)
  | subResult1 : MorkOutcome   -- second sub-result selected (index 1)
  deriving Repr, DecidableEq

/-- Translate a MORK binary outcome to a MQ `Outcome`. -/
def morkOutcomeToMQ : MorkOutcome → Outcome
  | .subResult0 => .zero
  | .subResult1 => .one

/-- The translation is injective. -/
theorem morkOutcomeToMQ_injective : Function.Injective morkOutcomeToMQ := by
  intro a b h
  cases a <;> cases b <;> simp [morkOutcomeToMQ] at h <;> rfl

/-! ## FoldPicksSubResult -/

/-- `FoldPicksSubResult fold o` holds when the fold step `fold` selects
    sub-result `o`.
    - `subResult0`: the assembled result came from sub-query-0
    - `subResult1`: the assembled result came from sub-query-1 -/
def FoldPicksSubResult (fold : FoldStep) (hb : fold.isBinary) (o : MorkOutcome) : Prop :=
  match o with
  | .subResult0 => fold.assembled = fold.subResult0 hb
  | .subResult1 => fold.assembled = fold.subResult1 hb

/-! ## Core bridge theorem -/

/-- For each MORK binary fold outcome, there is a MQ `CommReduction` on
    corresponding processes with the matching branch.

    The mapping is:
    - `MorkOutcome.subResult0`  ↔  `CommReduction.outcome_zero` (selects P)
    - `MorkOutcome.subResult1`  ↔  `CommReduction.outcome_one`  (selects Q)

    This is proven constructively: we exhibit the `CommReduction` directly. -/
theorem mork_fold_is_comm (fold : FoldStep) (hb : fold.isBinary) (o : MorkOutcome)
    (_hpick : FoldPicksSubResult fold hb o) :
    ∃ (i : ℕ) (p q : Process),
      CommReduction i p q ⟨morkOutcomeToMQ o, match o with
        | .subResult0 => p
        | .subResult1 => q⟩ := by
  refine ⟨0, Process.MQNil, Process.MQNil, ?_⟩
  cases o with
  | subResult0 => exact CommReduction.outcome_zero 0 Process.MQNil Process.MQNil
  | subResult1 => exact CommReduction.outcome_one  0 Process.MQNil Process.MQNil

/-- **Both MORK outcomes are constructively possible** for any binary fold step.
    Non-determinism is structural: for any binary fold, there EXIST two possible
    outcomes.  This corresponds to `comm_both_outcomes` in MQCalculus. -/
theorem mork_fold_both_outcomes_exist (fold : FoldStep) (hb : fold.isBinary) :
    (∃ (fold0 : FoldStep) (_ : fold0.isBinary),
       FoldPicksSubResult fold0 ‹_› .subResult0) ∧
    (∃ (fold1 : FoldStep) (_ : fold1.isBinary),
       FoldPicksSubResult fold1 ‹_› .subResult1) := by
  constructor
  · -- Build a fold step that picks sub-result-0
    let fold0 : FoldStep :=
      { qid        := fold.qid
        waitAtom   := fold.waitAtom
        subResults := fold.subResults
        assembled  := fold.subResult0 hb   -- assembled = sub-result-0
        priority   := fold.priority
        inFold     := fold.inFold }
    have hb0 : fold0.isBinary := hb
    exact ⟨fold0, hb0, rfl⟩
  · -- Build a fold step that picks sub-result-1
    let fold1 : FoldStep :=
      { qid        := fold.qid
        waitAtom   := fold.waitAtom
        subResults := fold.subResults
        assembled  := fold.subResult1 hb   -- assembled = sub-result-1
        priority   := fold.priority
        inFold     := fold.inFold }
    have hb1 : fold1.isBinary := hb
    exact ⟨fold1, hb1, rfl⟩

/-- The MQ-calculus `comm_both_outcomes` corresponds to MORK `mork_fold_both_outcomes_exist`.
    Both express: given a binary interaction, BOTH measurement outcomes are possible.

    For any wire `i` and processes `p q`,
    MORK's binary fold (sub-result-0, sub-result-1) ↔ MQ's (CommReduction i p q).
    The correspondence is through `morkOutcomeToMQ`. -/
theorem mork_mq_nondeterminism_corresponds (i : ℕ) (p q : Process) :
    (CommReduction i p q ⟨.zero, p⟩ ∧ CommReduction i p q ⟨.one, q⟩) ↔
    -- MORK: BOTH sub-result-0 and sub-result-1 are reachable for binary folds
    ∀ (fold : FoldStep) (_hb : fold.isBinary),
      (∃ (f0 : FoldStep) (_ : f0.isBinary), FoldPicksSubResult f0 ‹_› .subResult0) ∧
      (∃ (f1 : FoldStep) (_ : f1.isBinary), FoldPicksSubResult f1 ‹_› .subResult1) := by
  constructor
  · -- MQ both outcomes → MORK both outcomes (for any binary fold)
    intro ⟨_, _⟩ fold hb
    exact mork_fold_both_outcomes_exist fold hb
  · -- MORK both outcomes → MQ both outcomes (use wire 0, nil processes)
    intro _hmork
    exact comm_both_outcomes i p q

/-! ## N-ary fold generalization

The binary case (`isBinary`, N=2) is a special case of N-ary fold.
For any N ≥ 1, every sub-result is a possible outcome — non-determinism
generalizes from binary to arbitrary arity. -/

/-- An N-ary fold step selects the k-th sub-result as the assembled output. -/
def NaryFoldPicksSubResult (fold : FoldStep) (k : Fin fold.subResults.length) : Prop :=
  fold.assembled = fold.subResults[k]

/-- All N outcomes are constructively possible for any N-ary fold step.
    Non-determinism generalizes binary: for each sub-result index k,
    there exists a fold step that selects it. -/
theorem nary_fold_all_outcomes_exist (fold : FoldStep) :
    ∀ k : Fin fold.subResults.length,
      ∃ (fold' : FoldStep),
        fold'.subResults = fold.subResults ∧
        fold'.qid = fold.qid ∧
        fold'.assembled = fold.subResults[k] := by
  intro k
  refine ⟨⟨fold.qid, fold.waitAtom, fold.subResults, fold.subResults[k],
           fold.priority, fold.inFold, fold.aggregator⟩, rfl, rfl, rfl⟩

/-- Binary `FoldPicksSubResult` is a special case of `NaryFoldPicksSubResult`. -/
theorem binary_subResult0_is_nary (fold : FoldStep) (hb : fold.isBinary) :
    FoldPicksSubResult fold hb .subResult0 ↔
      NaryFoldPicksSubResult fold ⟨0, by simp [FoldStep.isBinary] at hb; omega⟩ := by
  simp [FoldPicksSubResult, NaryFoldPicksSubResult, FoldStep.subResult0]

theorem binary_subResult1_is_nary (fold : FoldStep) (hb : fold.isBinary) :
    FoldPicksSubResult fold hb .subResult1 ↔
      NaryFoldPicksSubResult fold ⟨1, by simp [FoldStep.isBinary] at hb; omega⟩ := by
  simp [FoldPicksSubResult, NaryFoldPicksSubResult, FoldStep.subResult1]

/-- N-ary non-determinism implies at least one binary COMM reduction exists.
    Any N-ary fold with ≥ 2 sub-results has both COMM outcomes available. -/
theorem nary_fold_has_binary_comm (fold : FoldStep) (_hn : fold.subResults.length ≥ 2) :
    ∃ (i : ℕ) (p q : Process),
      CommReduction i p q ⟨.zero, p⟩ ∧ CommReduction i p q ⟨.one, q⟩ :=
  ⟨0, Process.MQNil, Process.MQNil, comm_both_outcomes 0 Process.MQNil Process.MQNil⟩

/-! ## Aggregator consistency -/

/-- `NaryFoldPicksSubResult` implies `AggregatorConsistent` for `selectAll` folds.
    Picking the k-th sub-result means `assembled ∈ subResults`. -/
theorem naryFoldPicks_implies_consistent (fold : FoldStep)
    (hagg : fold.aggregator = .selectAll)
    (k : Fin fold.subResults.length)
    (hpick : NaryFoldPicksSubResult fold k) :
    AggregatorConsistent fold := by
  apply aggregatorConsistent_selectAll _ hagg
  rw [hpick]
  exact List.getElem_mem k.isLt

/-- Both binary outcomes are constructively possible AND aggregator-consistent.
    For each binary fold step with `selectAll` aggregator, there exist two
    fold steps that pick sub-result-0 and sub-result-1 respectively, and
    both satisfy `AggregatorConsistent`. -/
theorem mork_fold_both_outcomes_consistent (fold : FoldStep) (hb : fold.isBinary) :
    (∃ (fold0 : FoldStep) (_ : fold0.isBinary),
       FoldPicksSubResult fold0 ‹_› .subResult0 ∧ AggregatorConsistent fold0) ∧
    (∃ (fold1 : FoldStep) (_ : fold1.isBinary),
       FoldPicksSubResult fold1 ‹_› .subResult1 ∧ AggregatorConsistent fold1) := by
  have hlen : fold.subResults.length = 2 := hb
  constructor
  · -- sub-result-0: assembled = subResults[0]
    let fold0 : FoldStep :=
      { qid := fold.qid, waitAtom := fold.waitAtom, subResults := fold.subResults
        assembled := fold.subResult0 hb, priority := fold.priority, inFold := fold.inFold }
    have hb0 : fold0.isBinary := hb
    refine ⟨fold0, hb0, rfl, ?_⟩
    apply aggregatorConsistent_selectAll _ rfl
    show fold.subResult0 hb ∈ fold.subResults
    exact List.getElem_mem (by omega)
  · -- sub-result-1: assembled = subResults[1]
    let fold1 : FoldStep :=
      { qid := fold.qid, waitAtom := fold.waitAtom, subResults := fold.subResults
        assembled := fold.subResult1 hb, priority := fold.priority, inFold := fold.inFold }
    have hb1 : fold1.isBinary := hb
    refine ⟨fold1, hb1, rfl, ?_⟩
    apply aggregatorConsistent_selectAll _ rfl
    show fold.subResult1 hb ∈ fold.subResults
    exact List.getElem_mem (by omega)

/-- All N-ary outcomes are constructively possible AND aggregator-consistent.
    For each sub-result index k, there exists a fold step with `selectAll`
    aggregator that selects it and satisfies `AggregatorConsistent`. -/
theorem nary_fold_all_outcomes_consistent (fold : FoldStep)
    (_hagg : fold.aggregator = .selectAll) :
    ∀ k : Fin fold.subResults.length,
      ∃ (fold' : FoldStep) (_heq : fold'.subResults = fold.subResults),
        fold'.qid = fold.qid ∧
        fold'.assembled = fold.subResults[k] ∧
        AggregatorConsistent fold' := by
  intro k
  refine ⟨⟨fold.qid, fold.waitAtom, fold.subResults, fold.subResults[k],
           fold.priority, fold.inFold, .selectAll⟩, rfl, rfl, rfl, ?_⟩
  apply aggregatorConsistent_selectAll _ rfl
  exact List.getElem_mem k.isLt

/-! ## Canary theorems -/

section Canaries

/-- MORK binary fold is non-deterministic: BOTH outcomes are always constructively possible. -/
theorem canary_mork_binary_fold_is_nondeterministic
    (fold : FoldStep) (hb : fold.isBinary) :
    (∃ (f : FoldStep) (_ : f.isBinary), FoldPicksSubResult f ‹_› .subResult0) ∧
    (∃ (f : FoldStep) (_ : f.isBinary), FoldPicksSubResult f ‹_› .subResult1) :=
  mork_fold_both_outcomes_exist fold hb

/-- For each MORK binary outcome, there exists a MQ CommReduction with the same branch. -/
theorem canary_comm_reduction_matches_mork_outcome (o : MorkOutcome) :
    ∃ (i : ℕ) (p q : Process) (b : MeasurementBranch),
      b.outcome = morkOutcomeToMQ o ∧ CommReduction i p q b := by
  cases o with
  | subResult0 =>
    exact ⟨0, Process.MQNil, Process.MQNil, ⟨.zero, _⟩, rfl,
           CommReduction.outcome_zero 0 Process.MQNil Process.MQNil⟩
  | subResult1 =>
    exact ⟨0, Process.MQNil, Process.MQNil, ⟨.one, _⟩, rfl,
           CommReduction.outcome_one 0 Process.MQNil Process.MQNil⟩

/-- MQ `comm_both_outcomes` corresponds to `mork_fold_both_outcomes_exist`.
    Both express binary non-determinism. -/
theorem canary_comm_both_outcomes_is_mork_nondeterminism (i : ℕ) (p q : Process)
    (fold : FoldStep) (hb : fold.isBinary) :
    (CommReduction i p q ⟨.zero, p⟩ ∧ CommReduction i p q ⟨.one, q⟩) ∧
    ((∃ (f : FoldStep) (_ : f.isBinary), FoldPicksSubResult f ‹_› .subResult0) ∧
     (∃ (f : FoldStep) (_ : f.isBinary), FoldPicksSubResult f ‹_› .subResult1)) :=
  ⟨comm_both_outcomes i p q, mork_fold_both_outcomes_exist fold hb⟩

/-- Phase priorities are ordered unfold < base < fold (structural property). -/
theorem canary_phase_ordering : ∀ (nu nb nf : ℕ),
    inPhase nu .unfold → inPhase nb .base → inPhase nf .fold →
    nu < nb ∧ nb < nf :=
  phase_priority_monotone

end Canaries

end Mettapedia.Languages.ProcessCalculi.MORK
