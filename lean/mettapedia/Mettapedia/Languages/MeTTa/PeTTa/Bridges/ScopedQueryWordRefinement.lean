import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedNestedQueryExecution

/-!
# Ordered word refinement of the existing scoped traversal

Each captured child is assigned a specification word. Their concatenation is
the parent's word; the actual traversal supplies every reached intermediate
state. Reference and suspension remain source outcomes, not empty words or
successful execution. This is an induction law for `run` and `visit`, not a
second evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryWordRefinement

open EagerDFS.Destination
open NamedGuardedCandidateBatch (State)
open NestedQuerySource (Leg)
open ScopedNestedQueryExecution

variable {Context Letter : Type}

def Refines (words : Control → List Letter → Prop) (invariant : State Context → Prop)
    (relation : List Letter → State Context → State Context → Prop) (worker : Worker Context) : Prop :=
  ∀ caller state context origins pending after word,
    words caller word → invariant state →
    (worker caller state context origins pending).stop = .complete after →
    invariant after ∧ relation word state after

theorem visit_refines (words : Control → List Letter → Prop) (invariant : State Context → Prop)
    (relation : List Letter → State Context → State Context → Prop)
    (nil : ∀ state, invariant state → relation [] state state)
    (append : ∀ first later before middle after,
      relation first before middle → relation later middle after → relation (first ++ later) before after)
    (worker : Worker Context) (refines : Refines words invariant relation worker)
    (older : List Goal) (context : Context) (origins : List Nat)
    (selected : List (Nat × Control)) (assigned : List (List Letter))
    (callers : List.Forall₂ (fun entry word => words {entry.2 with goals := older} word) selected assigned)
    (state : State Context) (pending : List (CollectionWork Context)) (after : State Context)
    (valid : invariant state)
    (completed : (visit worker older context origins selected state pending).stop = .complete after) :
    invariant after ∧ relation assigned.flatten state after := by
  induction callers generalizing state after with
  | nil =>
    have same : state = after := Stop.complete.inj completed
    subst after
    exact ⟨valid, nil state valid⟩
  | @cons entry word selected assigned head _tail ih =>
    let first := worker {entry.2 with goals := older} state context (origins ++ [entry.1])
      (ScopedQuerySource.work context origins selected ++ pending)
    cases stopped : first.stop with
    | reference saved =>
      dsimp only [first] at stopped
      simp only [visit, stopped] at completed
      cases completed
    | suspended request saved =>
      dsimp only [first] at stopped
      simp only [visit, stopped] at completed
      cases completed
    | complete middle =>
      have firstResult := refines {entry.2 with goals := older} state context (origins ++ [entry.1])
        (ScopedQuerySource.work context origins selected ++ pending) middle word head valid stopped
      dsimp only [first] at stopped
      simp only [visit, stopped] at completed
      have later := ih middle after firstResult.1 completed
      exact ⟨later.1, append word assigned.flatten state middle after firstResult.2 later.2⟩

/-- Capture decomposes the specification word using the actual selected
controls. The leaf and append laws then refine a whole completed source
traversal, with the invariant threaded through every sibling boundary. -/
theorem run_refines (program : SpaceSemantics.Program) (leaf : Leaf program Context)
    (words : List Leg → Control → List Letter → Prop) (invariant : State Context → Prop)
    (relation : List Letter → State Context → State Context → Prop)
    (nil : ∀ state, invariant state → relation [] state state)
    (append : ∀ first later before middle after,
      relation first before middle → relation later middle after → relation (first ++ later) before after)
    (atLeaf : Refines (words []) invariant relation leaf.execute)
    (atCapture : ∀ leg rest caller state context origins pending word
      (selected : ScopedMatchEntry.Selection (source rest leaf.source) leaf.destination caller.goals),
      words (leg :: rest) caller word → invariant state →
      (ScopedMatchEntry.execute program leg.1 leg.2 (source rest leaf.source) leaf.destination caller state context origins pending).result =
        .captured selected →
      ∃ assigned, List.Forall₂ (fun entry part => words rest {entry.2 with goals := caller.goals} part) selected.choices assigned ∧
        assigned.flatten = word)
    (legs : List Leg) : Refines (words legs) invariant relation (run program leaf legs) := by
  induction legs with
  | nil => exact atLeaf
  | cons leg rest ih =>
    intro caller state context origins pending after word described valid completed
    unfold run at completed
    dsimp only at completed
    split at completed
    · cases completed
    next selected captured =>
      obtain ⟨assigned, callers, same⟩ := atCapture leg rest caller state context origins pending word selected described valid captured
      have result := visit_refines (words rest) invariant relation nil append (run program leaf rest) ih
        caller.goals context origins selected.choices assigned callers state pending after valid completed
      rw [same] at result
      exact result

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryWordRefinement
