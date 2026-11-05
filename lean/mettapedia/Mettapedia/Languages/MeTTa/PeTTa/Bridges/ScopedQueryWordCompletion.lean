import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryWordRefinement

/-!
# Reserve-aware completion of the existing scoped query traversal

A leaf completes when its word and the already collected packets fit the
available reserve. Its conservation equation supplies the next sibling's
reserve. Capture partitions words using actual selected controls, so the
induction constructs completion without assuming a future successful run.
The measures are abstract source resources, not a native memory cost bound.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryWordCompletion

open EagerDFS.Destination
open NamedGuardedCandidateBatch (State)
open NestedQuerySource (Leg)
open ScopedNestedQueryExecution

variable {Context Letter : Type}

def Completes (words : Control → List Letter → Prop) (invariant : State Context → Prop)
    (available collected : State Context → Nat) (worker : Worker Context) : Prop :=
  ∀ caller before context origins pending word,
    words caller word → invariant before → word.length + collected before ≤ available before →
    ∃ after, (worker caller before context origins pending).stop = .complete after ∧ invariant after ∧
      available after + word.length + collected before = available before + collected after

theorem visit_completes (words : Control → List Letter → Prop) (invariant : State Context → Prop)
    (available collected : State Context → Nat) (worker : Worker Context)
    (completes : Completes words invariant available collected worker)
    (older : List Goal) (context : Context) (origins : List Nat)
    (selected : List (Nat × Control)) (assigned : List (List Letter))
    (callers : List.Forall₂ (fun entry word => words {entry.2 with goals := older} word) selected assigned)
    (state : State Context) (pending : List (CollectionWork Context))
    (valid : invariant state) (reserve : assigned.flatten.length + collected state ≤ available state) :
    ∃ after, (visit worker older context origins selected state pending).stop = .complete after ∧ invariant after ∧
      available after + assigned.flatten.length + collected state = available state + collected after := by
  induction callers generalizing state with
  | nil => exact ⟨state, rfl, valid, by simp⟩
  | @cons entry word selected assigned head _tail ih =>
      have totalReserve : word.length + assigned.flatten.length + collected state ≤ available state := by
        simpa only [List.flatten_cons, List.length_append] using reserve
      have firstReserve : word.length + collected state ≤ available state := by omega
      obtain ⟨middle, firstDone, middleValid, firstLedger⟩ := completes
        {entry.2 with goals := older} state context (origins ++ [entry.1])
        (ScopedQuerySource.work context origins selected ++ pending) word head valid firstReserve
      have laterReserve : assigned.flatten.length + collected middle ≤ available middle := by omega
      obtain ⟨after, laterDone, afterValid, laterLedger⟩ := ih middle middleValid laterReserve
      refine ⟨after, ?_, afterValid, ?_⟩
      · simpa only [visit, firstDone] using laterDone
      · simp only [List.flatten_cons, List.length_append]
        omega

/-- Uniform completion follows from actual capture existence, exact word
decomposition and a leaf reserve contract. Every sibling receives the state
and reserve reached by its predecessor; no frozen-state execution is used. -/
theorem run_completes (program : SpaceSemantics.Program) (leaf : Leaf program Context)
    (words : List Leg → Control → List Letter → Prop) (invariant : State Context → Prop)
    (available collected : State Context → Nat)
    (atLeaf : Completes (words []) invariant available collected leaf.execute)
    (captureExists : ∀ leg rest caller state context origins pending word,
      words (leg :: rest) caller word → invariant state →
      ∃ selected, (ScopedMatchEntry.execute program leg.1 leg.2 (source rest leaf.source) leaf.destination
        caller state context origins pending).result = .captured selected)
    (atCapture : ∀ leg rest caller state context origins pending word
      (selected : ScopedMatchEntry.Selection (source rest leaf.source) leaf.destination caller.goals),
      words (leg :: rest) caller word → invariant state →
      (ScopedMatchEntry.execute program leg.1 leg.2 (source rest leaf.source) leaf.destination caller state context origins pending).result =
        .captured selected →
      ∃ assigned, List.Forall₂ (fun entry part => words rest {entry.2 with goals := caller.goals} part) selected.choices assigned ∧
        assigned.flatten = word)
    (legs : List Leg) : Completes (words legs) invariant available collected (run program leaf legs) := by
  induction legs with
  | nil => exact atLeaf
  | cons leg rest ih =>
      intro caller state context origins pending word described valid reserve
      obtain ⟨selected, captured⟩ := captureExists leg rest caller state context origins pending word described valid
      obtain ⟨assigned, callers, same⟩ := atCapture leg rest caller state context origins pending word
        selected described valid captured
      have assignedReserve : assigned.flatten.length + collected state ≤ available state := by
        simpa only [same] using reserve
      obtain ⟨after, completed, afterValid, ledger⟩ := visit_completes (words rest) invariant available collected
        (run program leaf rest) ih caller.goals context origins selected.choices assigned callers state pending valid assignedReserve
      exact ⟨after, by simpa only [run, captured] using completed, afterValid, by simpa only [same] using ledger⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryWordCompletion

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryWordCompletion.visit_completes
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryWordCompletion.run_completes
