import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedNestedQueryExecution

/-!
# Uniform admission through the actual nested source traversal

No-reference admission permits explicit suspension. Completed children carry
the live invariant to the next sibling; nothing assumes a future successful
run. Actual query entry must construct a capture, and every captured child
must retain the source-frame conditions needed by its suffix.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryAdmission

open EagerDFS.Destination
open NamedGuardedCandidateBatch (State)
open NestedQuerySource (Leg)
open ScopedNestedQueryExecution

variable {Context : Type}

def NoReference (execution : Execution Context) : Prop :=
  ∀ saved, execution.stop ≠ .reference saved

def AdmittedOn (goodCaller : Control → Prop) (invariant : State Context → Prop) (worker : Worker Context) : Prop :=
  ∀ caller state context origins pending, goodCaller caller → invariant state →
    NoReference (worker caller state context origins pending)

theorem visit_admitted (goodCaller : Control → Prop) (invariant : State Context → Prop)
    (worker : Worker Context) (preserves : PreservesOn goodCaller invariant worker)
    (admitted : AdmittedOn goodCaller invariant worker)
    (older : List Goal) (context : Context) (origins : List Nat) (selected : List (Nat × Control))
    (state : State Context) (pending : List (CollectionWork Context))
    (callers : ∀ entry ∈ selected, goodCaller {entry.2 with goals := older}) (valid : invariant state) :
    NoReference (visit worker older context origins selected state pending) := by
  induction selected generalizing state with
  | nil => simp [NoReference, visit]
  | cons entry rest ih =>
    let first := worker {entry.2 with goals := older} state context (origins ++ [entry.1])
      (ScopedQuerySource.work context origins rest ++ pending)
    cases stopped : first.stop with
    | reference saved =>
      exact False.elim (admitted {entry.2 with goals := older} state context (origins ++ [entry.1])
        (ScopedQuerySource.work context origins rest ++ pending) (callers entry List.mem_cons_self) valid saved stopped)
    | suspended request saved =>
      dsimp only [first] at stopped
      simp only [NoReference, visit, stopped]
      intro rejected impossible
      cases impossible
    | complete middle =>
      have nextValid := preserves {entry.2 with goals := older} state context (origins ++ [entry.1])
        (ScopedQuerySource.work context origins rest ++ pending) middle (callers entry List.mem_cons_self) valid stopped
      have later := ih middle (fun choice member => callers choice (List.mem_cons_of_mem _ member)) nextValid
      dsimp only [first] at stopped
      simpa only [NoReference, visit, stopped] using later

theorem run_admitted (program : SpaceSemantics.Program) (leaf : Leaf program Context)
    (goodCaller : List Leg → Control → Prop) (invariant : State Context → Prop)
    (leafPreserves : PreservesOn (goodCaller []) invariant leaf.execute)
    (leafAdmitted : AdmittedOn (goodCaller []) invariant leaf.execute)
    (capturePreserves : ∀ leg rest caller state context origins pending
      (selected : ScopedMatchEntry.Selection (source rest leaf.source) leaf.destination caller.goals),
      goodCaller (leg :: rest) caller → invariant state →
      (ScopedMatchEntry.execute program leg.1 leg.2 (source rest leaf.source) leaf.destination caller state context origins pending).result =
        .captured selected →
      ∀ entry ∈ selected.choices, goodCaller rest {entry.2 with goals := caller.goals})
    (captureExists : ∀ leg rest caller state context origins pending,
      goodCaller (leg :: rest) caller → invariant state →
      ∃ selected, (ScopedMatchEntry.execute program leg.1 leg.2 (source rest leaf.source) leaf.destination
        caller state context origins pending).result = .captured selected)
    (legs : List Leg) : AdmittedOn (goodCaller legs) invariant (run program leaf legs) := by
  induction legs with
  | nil => exact leafAdmitted
  | cons leg rest ih =>
    intro caller state context origins pending framed valid
    obtain ⟨selected, captured⟩ := captureExists leg rest caller state context origins pending framed valid
    have preserved := run_preserves_family program leaf goodCaller invariant leafPreserves capturePreserves rest
    have later := visit_admitted (goodCaller rest) invariant (run program leaf rest) preserved ih
      caller.goals context origins selected.choices state pending
      (capturePreserves leg rest caller state context origins pending selected framed valid captured) valid
    simpa only [NoReference, run, captured] using later

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryAdmission
