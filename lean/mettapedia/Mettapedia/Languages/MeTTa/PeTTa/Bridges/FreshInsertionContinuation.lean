import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshInsertionSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.EffectfulQuerySource

/-!
# Fresh insertion followed by an authored continuation

The continuation runs only after a genuinely new row is inserted. Its answer
stream, not the insertion flag, is returned. In particular an empty result
does not certify that the store stayed unchanged or that a closure is complete.
The completed `Returns` judgment permits state changes but no external I/O;
callbacks with printed or input traces need the corresponding trace judgment.
The worker is a private state computation; failure supplies no rollback law
for an implementation which already published its insertion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshInsertionContinuation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval SpaceSemantics NamedSpaces EffectfulQuerySource

def guardedSource (condition insertion : Atom) (temporary : String) (continuation : Atom) : Atom :=
  .expression [.symbol "if", condition,
    .expression [.symbol "let", .var temporary, insertion, continuation],
    .expression [.symbol "empty"]]

def source (spaceName rowName temporary : String) (continuation : Atom) : Atom :=
  guardedSource (GuardedInsertionSource.absent spaceName rowName)
    (.expression [.symbol "add-atom", .var spaceName, .var rowName]) temporary continuation

def run (target : Handle) (row : Atom) (temporary : String) (body : Body)
    (bindings : Subst) (before : Effects.State) : Option (Effects.State × List Atom) := do
  let inserted ← FreshInsertionSource.update before target row
  if inserted.2 then body ((temporary, Effects.boolean true) :: bindings) inserted.1
  else some (inserted.1, [])

theorem returns_using (program : Program) (condition insertion : Atom) (temporary : String) (continuation : Atom)
    (target : Handle) (row : Atom) (body : Body) (bindings : Subst)
    (before after : Effects.State) (answers : List Atom)
    (testLaw : ∀ rows, before.read target = some rows →
      PureReturns program bindings before condition before (Effects.boolean (decide (row ∉ rows))))
    (insertLaw : ∀ middle, Effects.insert before target row = some middle →
      PureReturns program bindings before insertion middle (Effects.boolean true))
    (fresh : Subst.lookup bindings temporary = none)
    (law : ∀ current next values,
      body ((temporary, Effects.boolean true) :: bindings) current = some (next, values) →
      Returns program ((temporary, Effects.boolean true) :: bindings) current continuation next values)
    (completed : run target row temporary body bindings before = some (after, answers)) :
    Returns program bindings before (guardedSource condition insertion temporary continuation) after answers := by
  obtain ⟨inserted, update, later⟩ := Option.bind_eq_some_iff.mp completed
  rcases inserted with ⟨middle, changed⟩
  obtain ⟨rows, snapshot, _, flag⟩ := FreshInsertionSource.update_reads_back update
  have test := testLaw rows snapshot
  cases changed with
  | false =>
      have same := FreshInsertionSource.zero_progress_preserves_state update
      subst middle
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj later)
      have present : row ∈ rows := by
        by_contra missing
        simp [missing] at flag
      apply if_answers program bindings before before before _ (Effects.boolean false) _ _ []
        (by simpa [present] using test)
      simpa [Effects.boolean] using empty_returns program bindings before
  | true =>
      have missing : row ∉ rows := by
        intro present
        simp [present] at flag
      have written : Effects.insert before target row = some middle := by
        have plain := FreshInsertionSource.unchanged_update update
        simpa [GuardedInsertionSource.update, snapshot, missing] using plain
      have insertedSource := insertLaw middle written
      have tail := law middle after answers later
      have letSource := let_answers program bindings ((temporary, Effects.boolean true) :: bindings)
        before middle after (.var temporary) _ continuation (Effects.boolean true) answers insertedSource
        (by simp [matchBinding, matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, fresh]) tail
      apply if_answers program bindings before before after _ (Effects.boolean true) _ _ answers
        (by simpa [missing] using test)
      simpa [Effects.boolean] using letSource

theorem returns (program : Program) (spaceName rowName temporary : String) (continuation : Atom)
    (target : Handle) (row : Atom) (body : Body) (bindings : Subst)
    (before after : Effects.State) (answers : List Atom)
    (location : Subst.lookup bindings spaceName = some (Effects.handleValue target))
    (bound : Subst.lookup bindings rowName = some row)
    (fresh : Subst.lookup bindings temporary = none)
    (law : ∀ current next values,
      body ((temporary, Effects.boolean true) :: bindings) current = some (next, values) →
      Returns program ((temporary, Effects.boolean true) :: bindings) current continuation next values)
    (completed : run target row temporary body bindings before = some (after, answers)) :
    Returns program bindings before (source spaceName rowName temporary continuation) after answers :=
  returns_using program _ _ temporary continuation target row body bindings before after answers
    (fun rows snapshot => GuardedInsertionSource.absent_returns program bindings before spaceName rowName target row rows
      location bound snapshot)
    (fun middle written => GuardedInsertionSource.insert_returns program bindings before middle spaceName rowName
      target row location bound written) fresh law completed

theorem held_row_skips_body (target : Handle) (row : Atom) (temporary : String) (body : Body)
    (bindings : Subst) (state : Effects.State) (rows : List Atom)
    (snapshot : state.read target = some rows) (present : row ∈ rows) :
    run target row temporary body bindings state = some (state, []) := by
  simp [run, FreshInsertionSource.update, snapshot, present]

theorem missing_read_is_not_an_empty_result (target : Handle) (row : Atom) (temporary : String) (body : Body)
    (bindings : Subst) (state : Effects.State) (missing : state.read target = none) :
    run target row temporary body bindings state = none := by
  simp [run, FreshInsertionSource.update, missing]

/-- Every successful fresh branch enters its continuation with the row already
visible. This retains the recursive cycle-breaking point. -/
theorem body_entry_has_row (target : Handle) (row : Atom) (before middle : Effects.State)
    (updated : FreshInsertionSource.update before target row = some (middle, true)) :
    ∃ rows, middle.read target = some rows ∧ row ∈ rows := by
  obtain ⟨old, _, reading, flag⟩ := FreshInsertionSource.update_reads_back updated
  have missing : row ∉ old := by
    intro present
    simp [present] at flag
  refine ⟨old ++ [row], by simpa [missing] using reading, ?_⟩
  simp

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshInsertionContinuation
