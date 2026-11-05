import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedQuerySource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedQueryAdmission

/-!
# Source-level insertion-on-absence with an explicit success observation

The existing PeTTa evaluator has ordered bag spaces. An absence guard over a
complete captured read can implement insertion without duplicate rows while
still answering true on both the fresh and already-present branches. These
are sequential source laws; an interleaving write between the test and insert
requires a separate atomicity or stability contract.

This is not a redefinition of the source's bag insertion primitive and does
not claim that the CeTTa extended set-space constructor is already modeled.
The theorem uses the existing evaluator's matcher; runtime conformance for
open stored facts is not inferred from it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedInsertionSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Eval SpaceSemantics NamedSpaces
open FlatQueryRelationCompilation

def query (spaceName rowName : String) : Atom :=
  .expression [.symbol "match", .var spaceName, .var rowName, Effects.boolean true]

def absent (spaceName rowName : String) : Atom :=
  .expression [.symbol "==", .expression [.symbol "collapse", query spaceName rowName], .expression []]

def source (spaceName rowName : String) : Atom :=
  .expression [.symbol "if", absent spaceName rowName,
    .expression [.symbol "add-atom", .var spaceName, .var rowName], Effects.boolean true]

def update (state : Effects.State) (handle : Handle) (row : Atom) : Option Effects.State := do
  let rows ← state.read handle
  if row ∈ rows then some state else Effects.insert state handle row

theorem match_bound_row (bindings : Subst) (name : String) (row candidate : Atom)
    (bound : Subst.lookup bindings name = some row) :
    matchValue bindings (.var name) candidate = if candidate = row then some bindings else none := by
  simp only [matchValue, matchAtom, bound]
  simp only [beq_iff_eq]

theorem scan_empty_iff (bindings : Subst) (name : String) (row : Atom)
    (bound : Subst.lookup bindings name = some row) (rows : List Atom) (start : Nat) :
    sourceScan bindings (.var name) start rows = [] ↔ row ∉ rows := by
  induction rows generalizing start with
  | nil => simp [sourceScan]
  | cons candidate rows ih =>
      by_cases same : candidate = row
      · subst candidate
        simp [sourceScan, match_bound_row bindings name row row bound]
      · simp [sourceScan, match_bound_row bindings name row candidate bound, same, Ne.symm same, ih]

theorem query_returns (program : Program) (bindings : Subst) (state : Effects.State)
    (spaceName rowName : String) (handle : Handle) (rows : List Atom)
    (location : Subst.lookup bindings spaceName = some (Effects.handleValue handle))
    (snapshot : state.read handle = some rows) :
    Returns program bindings state (query spaceName rowName) state
      ((sourceScan bindings (.var rowName) 0 rows).map fun _ => Effects.boolean true) := by
  have space : PureReturns program bindings state (.var spaceName) state (Effects.handleValue handle) := by
    simpa only [applySubst, location, Option.getD_some] using variable_returns program bindings state spaceName
  have result := CapturedQuerySource.match_returns program state bindings (.var spaceName)
    (Effects.handleValue handle) rows space (by simp [snapshot]) (.var rowName) (Effects.boolean true)
    (fun _ => [Effects.boolean true]) (fun _ _ after _ => grounded_returns program after state (.bool true))
  simpa only [query, ← List.map_eq_flatMap] using result

theorem absent_returns (program : Program) (bindings : Subst) (state : Effects.State)
    (spaceName rowName : String) (handle : Handle) (row : Atom) (rows : List Atom)
    (location : Subst.lookup bindings spaceName = some (Effects.handleValue handle))
    (bound : Subst.lookup bindings rowName = some row) (snapshot : state.read handle = some rows) :
    PureReturns program bindings state (absent spaceName rowName) state (Effects.boolean (decide (row ∉ rows))) := by
  have collected := collapse_returns program bindings state state _ _
    (query_returns program bindings state spaceName rowName handle rows location snapshot)
  have emptyReturns : PureReturns program bindings state (.expression []) state (.expression []) :=
    .step (step_transition rfl) (.step (step_transition rfl) (.refl _))
  have equal :
      ((Atom.expression ((sourceScan bindings (.var rowName) 0 rows).map fun _ => Effects.boolean true)) ==
        Atom.expression []) = decide (row ∉ rows) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, Atom.expression.injEq, List.map_eq_nil_iff, decide_eq_true_eq]
    exact scan_empty_iff bindings rowName row bound rows 0
  exact native_binary_call_returns program bindings state state state state "=="
    _ _ _ _ _ (by decide) (by decide)
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument])
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument]) collected emptyReturns
    (by simp only [StdLib.structural_equality, equal]) (by decide)

theorem insert_returns (program : Program) (bindings : Subst) (before after : Effects.State)
    (spaceName rowName : String) (handle : Handle) (row : Atom)
    (location : Subst.lookup bindings spaceName = some (Effects.handleValue handle))
    (bound : Subst.lookup bindings rowName = some row) (inserted : Effects.insert before handle row = some after) :
    PureReturns program bindings before (.expression [.symbol "add-atom", .var spaceName, .var rowName])
      after (Effects.boolean true) := by
  apply native_variable_call_returns program bindings before after "add-atom" [spaceName, rowName] _
    (by decide) (by decide) _ (by decide)
  simp only [List.map_cons, List.map_nil, applySubst, location, bound, Option.getD_some]
  change (match Effects.readHandle (Effects.handleValue handle) >>= fun chosen => Effects.insert before chosen row with
    | some result => Except.ok (result, [Effects.boolean true])
    | none => Except.error Effects.Fault.invalidSpace) = _
  rw [Effects.readHandle_handleValue]
  change (match Effects.insert before handle row with
    | some result => Except.ok (result, [Effects.boolean true])
    | none => Except.error Effects.Fault.invalidSpace) = _
  rw [inserted]

theorem source_returns (program : Program) (bindings : Subst) (before after : Effects.State)
    (spaceName rowName : String) (handle : Handle) (row : Atom) (rows : List Atom)
    (location : Subst.lookup bindings spaceName = some (Effects.handleValue handle))
    (bound : Subst.lookup bindings rowName = some row) (snapshot : before.read handle = some rows)
    (updated : update before handle row = some after) :
    PureReturns program bindings before (source spaceName rowName) after (Effects.boolean true) := by
  have tested := absent_returns program bindings before spaceName rowName handle row rows location bound snapshot
  by_cases present : row ∈ rows
  · have same : before = after := by simpa [update, snapshot, present] using updated
    subst after
    have branch := grounded_returns program bindings before (.bool true)
    simpa [source, present] using if_returns program bindings before before before
      (absent spaceName rowName) (Effects.boolean false) (.expression [.symbol "add-atom", .var spaceName, .var rowName])
      (Effects.boolean true) (Effects.boolean true) (by simpa [present] using tested) (by simpa [Effects.boolean] using branch)
  · have inserted : Effects.insert before handle row = some after := by simpa [update, snapshot, present] using updated
    have branch := insert_returns program bindings before after spaceName rowName handle row location bound inserted
    simpa [source, present] using if_returns program bindings before before after
      (absent spaceName rowName) (Effects.boolean true) (.expression [.symbol "add-atom", .var spaceName, .var rowName])
      (Effects.boolean true) (Effects.boolean true) (by simpa [present] using tested) (by simpa using branch)

theorem update_reads_back {before after : Effects.State} {handle : Handle} {row : Atom}
    (updated : update before handle row = some after) :
    ∃ rows, before.read handle = some rows ∧
      after.read handle = some (if row ∈ rows then rows else rows ++ [row]) := by
  unfold update at updated
  cases snapshot : before.read handle with
  | none => simp [snapshot] at updated
  | some rows =>
      simp only [snapshot] at updated
      refine ⟨rows, rfl, ?_⟩
      by_cases present : row ∈ rows
      · have same : before = after := by simpa [present] using updated
        subst after
        simpa [present] using snapshot
      · have inserted : Effects.insert before handle row = some after := by simpa [present] using updated
        obtain ⟨old, oldRead, afterRead⟩ := Effects.insert_reads_back inserted
        have same : old = rows := Option.some.inj (oldRead.symm.trans snapshot)
        simpa only [same, if_neg present] using afterRead

theorem update_exists {before : Effects.State} {handle : Handle} {rows : List Atom}
    (snapshot : before.read handle = some rows) (row : Atom) : ∃ after, update before handle row = some after := by
  by_cases present : row ∈ rows
  · exact ⟨before, by simp [update, snapshot, present]⟩
  · obtain ⟨after, inserted⟩ := Effects.insert_exists_of_read_some snapshot row
    exact ⟨after, by simp [update, snapshot, present, inserted]⟩

theorem update_cases {before after : Effects.State} {handle : Handle} {row : Atom}
    (updated : update before handle row = some after) :
    before = after ∨ Effects.insert before handle row = some after := by
  unfold update at updated
  cases snapshot : before.read handle with
  | none => simp [snapshot] at updated
  | some rows =>
      simp only [snapshot] at updated
      change (if row ∈ rows then some before else Effects.insert before handle row) = some after at updated
      split at updated
      · exact Or.inl (Option.some.inj updated)
      · exact Or.inr updated

theorem update_read_other {before after : Effects.State} {handle other : Handle} {row : Atom}
    (updated : update before handle row = some after) (different : other ≠ handle) :
    after.read other = before.read other := by
  rcases update_cases updated with same | inserted
  · rw [same]
  · exact Effects.insert_read_other inserted different

theorem update_preserves_cells {before after : Effects.State} {handle : Handle} {row : Atom}
    (updated : update before handle row = some after) : after.cells = before.cells := by
  rcases update_cases updated with same | inserted
  · rw [same]
  · exact Effects.insert_preserves_cells inserted

theorem missing_space_is_not_presence (before : Effects.State) (handle : Handle) (row : Atom)
    (missing : before.read handle = none) : update before handle row = none := by simp [update, missing]

theorem update_nodup {before after : Effects.State} {handle : Handle} {row : Atom} {rows : List Atom}
    (snapshot : before.read handle = some rows) (distinct : rows.Nodup) (updated : update before handle row = some after) :
    ∃ result, after.read handle = some result ∧ result.Nodup ∧ result.toFinset = insert row rows.toFinset := by
  obtain ⟨old, oldRead, afterRead⟩ := update_reads_back updated
  have same : old = rows := Option.some.inj (oldRead.symm.trans snapshot)
  subst old
  refine ⟨_, afterRead, ?_, ?_⟩
  · split
    · exact distinct
    · simp_all [List.nodup_append]
      intro atom member same
      subst atom
      contradiction
  · split <;> simp_all

theorem source_meaning (program : Program) (bindings : Subst) (before after : Effects.State)
    (spaceName rowName : String) (handle : Handle) (row : Atom)
    (location : Subst.lookup bindings spaceName = some (Effects.handleValue handle))
    (bound : Subst.lookup bindings rowName = some row) (updated : update before handle row = some after) :
    PureCallPortfolio.sourceMeaning program bindings (source spaceName rowName) before =
      {⟨after, [Effects.boolean true], [], []⟩} := by
  obtain ⟨rows, snapshot, _⟩ := update_reads_back updated
  have returned := source_returns program bindings before after spaceName rowName handle row rows location bound snapshot updated
  ext observed
  change DeclarativeSpec.Runs program {state := before, control := .evaluate bindings (source spaceName rowName)}
    (.complete observed.state observed.answers observed.input observed.output) ↔ _
  rw [pure_returns_derivation_iff program bindings before after (source spaceName rowName) (Effects.boolean true) returned]
  cases observed
  simp [PureCallPortfolio.Completed.mk.injEq]

open Mettapedia.GSLT.Dynamics ObservationQualified in
def region (program : Program) (bindings : Subst) (spaceName rowName : String) (handle : Handle) (row : Atom)
    (location : Subst.lookup bindings spaceName = some (Effects.handleValue handle))
    (bound : Subst.lookup bindings rowName = some row) :
    CertifiedRegion (PureCallPortfolio.boundary program bindings (source spaceName rowName)) Nat where
  regime := 0
  Artifact := PureCallPortfolio.Completed
  attempt before := if ClosedQueryAdmission.targetReady before handle [row] then
    match update before handle row with
    | none => .declined before
    | some after => .committed ⟨after, [Effects.boolean true], [], []⟩
    else .declined before
  decode observed := {observed}
  restores before restored declined := by
    dsimp only at declined
    split at declined
    · cases updated : update before handle row with
      | none => exact (PartialRegionPlan.Attempt.declined.inj (by simpa only [updated] using declined)).symm
      | some after => simp only [updated] at declined; cases declined
    · exact (PartialRegionPlan.Attempt.declined.inj declined).symm
  exact before observed accepted := by
    split at accepted
    · cases updated : update before handle row with
      | none => simp only [updated] at accepted; cases accepted
      | some after =>
          have same : (PureCallPortfolio.Completed.mk after [Effects.boolean true] [] []) = observed := by
            simpa only [updated, PartialRegionPlan.Attempt.committed.injEq] using accepted
          subst observed
          exact (source_meaning program bindings before after spaceName rowName handle row location bound updated).symm
    · cases accepted

theorem missing_handle_declines_without_changing_state (program : Program) (bindings : Subst)
    (spaceName rowName : String) (handle : Handle) (row : Atom)
    (location : Subst.lookup bindings spaceName = some (Effects.handleValue handle))
    (bound : Subst.lookup bindings rowName = some row) (before : Effects.State) (missing : before.read handle = none) :
    (region program bindings spaceName rowName handle row location bound).attempt before = .declined before := by
  simp only [region, ClosedQueryAdmission.missing_nonempty_target_refuses before handle row [] missing,
    Bool.false_eq_true, ↓reduceIte]

/-- The data-only adapter excludes open rows and declaration/equation writes.
Those writes have additional program-revision obligations not discharged here. -/
def dataRow : Atom → Bool
  | row@(.expression (.symbol head :: _)) =>
      head != "=" && head != ":" && Mettapedia.Languages.ProcessCalculi.MORK.isGroundAtom row
  | _ => false

open Mettapedia.GSLT.Dynamics ObservationQualified in
def classify (observation : PureCallExtraction.Observation) (program : Program) (bindings : Subst)
    (spaceName rowName : String) (handle : Handle) (row : Atom)
    (location : Subst.lookup bindings spaceName = some (Effects.handleValue handle))
    (bound : Subst.lookup bindings rowName = some row) :
    Option (CertifiedRegion (PureCallPortfolio.boundary program bindings (source spaceName rowName)) Nat) :=
  match observation with
  | .exactPage => none
  | .completedResult => if dataRow row then some (region program bindings spaceName rowName handle row location bound) else none

theorem exact_page_refuses (program : Program) (bindings : Subst) (spaceName rowName : String)
    (handle : Handle) (row : Atom) (location : Subst.lookup bindings spaceName = some (Effects.handleValue handle))
    (bound : Subst.lookup bindings rowName = some row) :
    classify .exactPage program bindings spaceName rowName handle row location bound = none := rfl

theorem unsupported_row_refuses (program : Program) (bindings : Subst) (spaceName rowName : String)
    (handle : Handle) (row : Atom) (location : Subst.lookup bindings spaceName = some (Effects.handleValue handle))
    (bound : Subst.lookup bindings rowName = some row) (unsupported : dataRow row = false) :
    classify .completedResult program bindings spaceName rowName handle row location bound = none := by
  simp [classify, unsupported]

namespace Controls

def row : Atom := .expression [.symbol "fact", .grounded (.int 7)]
def emptyState : Effects.State := Store.new [] []
def heldState : Effects.State := Store.new [row] []
def duplicatedState : Effects.State := Store.new [row, row] []
def caller : Subst := [("space", .symbol "&self"), ("row", row)]
def program : Program := {equations := [], declarations := []}
def twice : Atom := .expression [.symbol "superpose", .expression [source "space" "row", source "space" "row"]]

theorem present_insertion_still_returns_success :
    PureReturns {equations := [], declarations := []} [("space", .symbol "&self"), ("row", row)]
      heldState (source "space" "row") heldState (Effects.boolean true) := by
  exact source_returns _ _ _ _ "space" "row" .self row [row] rfl rfl rfl rfl

theorem fresh_insertion_adds_one_row : update emptyState .self row = some heldState := rfl

theorem fresh_source_returns_success :
    PureReturns program caller emptyState (source "space" "row") heldState (Effects.boolean true) :=
  source_returns _ _ _ _ "space" "row" .self row [] rfl rfl rfl fresh_insertion_adds_one_row

theorem two_successes_need_not_mean_two_stored_rows :
    Returns program caller emptyState twice heldState [Effects.boolean true, Effects.boolean true] ∧
      heldState.core.length = 1 := by
  refine ⟨?_, rfl⟩
  refine .step (step_transition rfl) ?_
  apply sequence_cons_answers program emptyState heldState heldState
    (.evaluate caller (source "space" "row")) [.evaluate caller (source "space" "row")] []
    [Effects.boolean true] [Effects.boolean true, Effects.boolean true] fresh_source_returns_success
  apply sequence_cons_answers program heldState heldState heldState
    (.evaluate caller (source "space" "row")) [] [Effects.boolean true]
    [Effects.boolean true] [Effects.boolean true, Effects.boolean true] present_insertion_still_returns_success
  exact .step (step_transition rfl) (.refl _)

theorem actual_collection_counts_two_successes :
    PureReturns program caller emptyState
      (.expression [.symbol "size-atom", .expression [.symbol "collapse", twice]])
      heldState (.grounded (.int 2)) := by
  have collected := collapse_returns program caller emptyState heldState twice _
    two_successes_need_not_mean_two_stored_rows.1
  exact native_unary_call_returns program caller emptyState heldState heldState "size-atom"
    _ _ _ (by decide) (by decide) (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument])
    collected rfl (by decide)

theorem stale_absence_does_not_license_a_second_blind_append :
    Effects.insert emptyState .self row = some heldState ∧
    Effects.insert heldState .self row = some duplicatedState ∧
    duplicatedState.core.length = 2 ∧ ¬duplicatedState.core.Nodup := by
  exact ⟨rfl, rfl, rfl, by decide +kernel⟩

theorem baseline_constructor_has_no_set_kind_clause :
    StdLib.apply emptyState "new-space" [.symbol "set"] = .error (.invalidArguments "new-space") := rfl

theorem data_admission_keeps_revision_and_scope_boundaries :
    dataRow row = true ∧
    dataRow (.expression [.symbol "fact", .var "x"]) = false ∧
    dataRow (.expression [.symbol "=", .expression [.symbol "f"], .grounded (.int 7)]) = false ∧
    dataRow (.expression [.symbol ":", .symbol "f", .symbol "Atom"]) = false := by decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedInsertionSource
