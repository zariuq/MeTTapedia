import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLPreimageSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.EffectfulTraversal
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PreparedEffectfulQuery

/-!
# Captured CTL predecessor execution with source effects

The satisfaction choices are captured once. The reverse-edge table remains
unchanged while the satisfaction table grows. Flattening the prepared loops
preserves their order and every insertion occurrence. The actual source
derivation includes both matches, raw insertion, collapse and the returned
producer count.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLPreimageExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Eval SpaceSemantics NamedSpaces EffectfulQuerySource CTLPreimageSource

def prepared (satHead reverseHead : String) (names : Names) (table : Handle)
    (caller : Subst) (satRows graphRows : List Atom) (before : Effects.State) : Option (Effects.State × List Atom) :=
  traverse (fun bindings state =>
    traverse (QueryBagMaterialization.emit table (template satHead names))
      (choices bindings (reversePattern reverseHead names) graphRows) (state, []))
    (choices caller (satPattern satHead names) satRows) (before, [])

theorem prepared_flatten (satHead reverseHead : String) (names : Names) (table : Handle)
    (caller : Subst) (satRows graphRows : List Atom) (before : Effects.State) :
    prepared satHead reverseHead names table caller satRows graphRows before =
      traverse (QueryBagMaterialization.emit table (template satHead names))
        (candidates satHead reverseHead names caller satRows graphRows) (before, []) :=
  traverse_nested _ _ _ _ _

private theorem handle_returns (program : Program) (caller : Subst) (state : Effects.State) (handle : Handle) :
    PureReturns program caller state (.expression [.symbol "quote", Effects.handleValue handle]) state (Effects.handleValue handle) := by
  have returned := quote_returns program caller state (Effects.handleValue handle)
  have fixed : applySubst caller (Effects.handleValue handle) = Effects.handleValue handle := by cases handle <;> rfl
  simpa only [fixed] using returned

theorem prepared_source (program : Program) (satHead reverseHead : String) (names : Names) (table graph : Handle)
    (apart : graph ≠ table) (caller : Subst) (before after : Effects.State) (satRows graphRows answers : List Atom)
    (location : Subst.lookup caller names.space = some (Effects.handleValue table))
    (satRead : before.read table = some satRows) (graphRead : before.read graph = some graphRows)
    (completed : prepared satHead reverseHead names table caller satRows graphRows before = some (after, answers)) :
    PureReturns program caller before (source satHead reverseHead names table graph) after (.grounded (.int answers.length)) ∧
      after.read graph = some graphRows := by
  let leaf := QueryBagMaterialization.emit table (template satHead names)
  let leafSource := QueryBagMaterialization.insertion names.space (template satHead names)
  let innerSource := NestedQuerySource.source [(graph, reversePattern reverseHead names)] leafSource
  let invariant := fun state : Effects.State => state.read graph = some graphRows
  have outer := PreparedEffectfulQuery.match_returns_invariant program caller before after
    (.expression [.symbol "quote", Effects.handleValue table]) (satPattern satHead names) innerSource
    table (choices caller (satPattern satHead names) satRows)
    (fun bindings state => traverse leaf (choices bindings (reversePattern reverseHead names) graphRows) (state, []))
    answers invariant (handle_returns program caller before table) (by simp [QueryReadStability.view, satRead])
    (by
      intro bindings member current next values valid computed
      change current.read graph = some graphRows at valid
      have boundLocation := choices_extend caller (satPattern satHead names) satRows bindings member names.space _ location
      apply PreparedEffectfulQuery.match_returns_invariant program bindings current next
        (.expression [.symbol "quote", Effects.handleValue graph]) (reversePattern reverseHead names) leafSource graph
        (choices bindings (reversePattern reverseHead names) graphRows) leaf values invariant
        (handle_returns program bindings current graph) (by simp [QueryReadStability.view, valid]) _ valid computed
      intro bound boundMember entered exited results kept executed
      have liveLocation := choices_extend bindings (reversePattern reverseHead names) graphRows bound boundMember names.space _ boundLocation
      refine ⟨QueryBagMaterialization.emit_returns program names.space table (template satHead names) bound entered exited results liveLocation executed, ?_⟩
      obtain ⟨finish, inserted, same⟩ := Option.map_eq_some_iff.mp executed
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      exact (Effects.insert_read_other inserted apart).trans kept)
    graphRead completed
  have collected := collapse_returns program caller before after _ _ outer.1
  refine ⟨?_, outer.2⟩
  exact native_unary_call_returns program caller before after after "size-atom" _ _ _
    (by decide) (by decide) (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument]) collected rfl (by decide)

theorem prepared_receipt (satHead reverseHead : String) (names : Names) (table : Handle)
    (caller : Subst) (before after : Effects.State) (satRows graphRows answers : List Atom)
    (satRead : before.read table = some satRows)
    (completed : prepared satHead reverseHead names table caller satRows graphRows before = some (after, answers)) :
    after.read table = some (satRows ++
      (candidates satHead reverseHead names caller satRows graphRows).map (fun bindings => applySubst bindings (template satHead names))) ∧
      answers = List.replicate (candidates satHead reverseHead names caller satRows graphRows).length (Effects.boolean true) ∧
      (∀ other, other ≠ table → after.read other = before.read other) ∧ after.cells = before.cells := by
  rw [prepared_flatten] at completed
  simpa only [List.nil_append] using QueryBagMaterialization.traverse_receipt table (template satHead names)
    _ before after satRows [] answers satRead completed

theorem prepared_exists (satHead reverseHead : String) (names : Names) (table : Handle)
    (caller : Subst) (before : Effects.State) (satRows graphRows : List Atom)
    (satRead : before.read table = some satRows) :
    ∃ after answers, prepared satHead reverseHead names table caller satRows graphRows before = some (after, answers) := by
  obtain ⟨after, installed⟩ := QueryBagMaterialization.installRows_exists table
    ((candidates satHead reverseHead names caller satRows graphRows).map (fun bindings => applySubst bindings (template satHead names)))
    before satRows satRead
  refine ⟨after, List.replicate (candidates satHead reverseHead names caller satRows graphRows).length (Effects.boolean true), ?_⟩
  rw [prepared_flatten, QueryBagMaterialization.traverse_install_exact, installed]
  rfl

def execute (satHead reverseHead : String) (names : Names) (table graph : Handle)
    (caller : Subst) (before : Effects.State) : Option (Effects.State × List Atom) := do
  if Subst.lookup caller names.space = some (Effects.handleValue table) ∧ graph ≠ table then do
    let satRows ← before.read table
    let graphRows ← before.read graph
    if (Subst.lookup caller names.output).any Mettapedia.Languages.ProcessCalculi.MORK.isGroundAtom &&
        ClosedQueryAdmission.capturesReady caller (satPattern satHead names) &&
        ClosedQueryAdmission.capturesReady caller (reversePattern reverseHead names) &&
        ClosedQueryAdmission.rowsReady (satPattern satHead names) satRows &&
        ClosedQueryAdmission.rowsReady (reversePattern reverseHead names) graphRows then
      prepared satHead reverseHead names table caller satRows graphRows before
    else none
  else none

theorem execute_source (program : Program) (satHead reverseHead : String) (names : Names) (table graph : Handle)
    (caller : Subst) (before after : Effects.State) (answers : List Atom)
    (completed : execute satHead reverseHead names table graph caller before = some (after, answers)) :
    PureReturns program caller before (source satHead reverseHead names table graph) after (.grounded (.int answers.length)) := by
  unfold execute at completed
  split at completed
  next valid =>
    obtain ⟨satRows, satRead, rest⟩ := Option.bind_eq_some_iff.mp completed
    obtain ⟨graphRows, graphRead, rest⟩ := Option.bind_eq_some_iff.mp rest
    split at rest
    · exact (prepared_source program satHead reverseHead names table graph valid.2 caller before after satRows graphRows answers
        valid.1 satRead graphRead rest).1
    · cases rest
  next => cases completed

theorem execute_meaning (program : Program) (satHead reverseHead : String) (names : Names) (table graph : Handle)
    (caller : Subst) (before after : Effects.State) (answers : List Atom)
    (completed : execute satHead reverseHead names table graph caller before = some (after, answers)) :
    PureCallPortfolio.sourceMeaning program caller (source satHead reverseHead names table graph) before =
      {PureCallPortfolio.complete after (.grounded (.int answers.length))} := by
  have returned := execute_source program satHead reverseHead names table graph caller before after answers completed
  ext observed
  change DeclarativeSpec.Runs program {state := before, control := .evaluate caller (source satHead reverseHead names table graph)}
    (.complete observed.state observed.answers observed.input observed.output) ↔ _
  rw [pure_returns_derivation_iff program caller before after _ _ returned]
  cases observed
  simp [PureCallPortfolio.complete, PureCallPortfolio.Completed.mk.injEq]

open Mettapedia.GSLT.Dynamics ObservationQualified in
def region {Regime : Type} (regime : Regime) (program : Program) (satHead reverseHead : String) (names : Names)
    (table graph : Handle) (caller : Subst) :
    CertifiedRegion (PureCallPortfolio.boundary program caller (source satHead reverseHead names table graph)) Regime where
  regime := regime
  Artifact := PureCallPortfolio.Completed
  attempt before := match execute satHead reverseHead names table graph caller before with
    | none => .declined before
    | some receipt => .committed (PureCallPortfolio.complete receipt.1 (.grounded (.int receipt.2.length)))
  decode observed := {observed}
  restores before restored refused := by
    dsimp only at refused
    split at refused
    · exact (PartialRegionPlan.Attempt.declined.inj refused).symm
    · cases refused
  exact before observed committed := by
    split at committed
    · cases committed
    next receipt completed =>
      cases PartialRegionPlan.Attempt.committed.inj committed
      exact (execute_meaning program satHead reverseHead names table graph caller before receipt.1 receipt.2 completed).symm

theorem typed_source (program : Program) (satHead reverseHead : String) (names : Names) (table graph : Handle)
    (apart : graph ≠ table) (satOrdinary : satHead ≠ "cons") (reverseOrdinary : reverseHead ≠ "cons")
    (inputLabel outputLabel : String) (satRows : List (String × Nat)) (edges : List (Nat × Nat))
    (caller : Subst) (before : Effects.State)
    (location : Subst.lookup caller names.space = some (Effects.handleValue table))
    (inputRead : Subst.lookup caller names.input = some (.symbol inputLabel))
    (outputRead : Subst.lookup caller names.output = some (.symbol outputLabel))
    (nextFresh : Subst.lookup caller names.next = none) (priorFresh : Subst.lookup caller names.prior = none)
    (satRead : before.read table = some (satRows.map (fun entry => satisfaction satHead entry.1 entry.2)))
    (graphRead : before.read graph = some (edges.map (reverseEdge reverseHead))) :
    ∃ after,
      PureReturns program caller before (source satHead reverseHead names table graph) after
        (.grounded (.int (produced edges (operand inputLabel satRows)).length)) ∧
      after.read table = some (satRows.map (fun entry => satisfaction satHead entry.1 entry.2) ++
        (produced edges (operand inputLabel satRows)).map (satisfaction satHead outputLabel)) ∧
      (∀ other, other ≠ table → after.read other = before.read other) ∧ after.cells = before.cells := by
  obtain ⟨after, answers, completed⟩ := prepared_exists satHead reverseHead names table caller before _ _ satRead
  obtain ⟨returned, _⟩ := prepared_source program satHead reverseHead names table graph apart caller before after _ _ answers
    location satRead graphRead completed
  obtain ⟨afterRead, answersShape, others, cells⟩ := prepared_receipt satHead reverseHead names table caller before after _ _ answers satRead completed
  have rendered := rendered_candidates satHead reverseHead names caller satOrdinary reverseOrdinary inputLabel outputLabel satRows edges
    inputRead outputRead nextFresh priorFresh
  have count := congrArg List.length rendered
  simp only [List.length_map] at count
  rw [rendered] at afterRead
  refine ⟨after, ?_, afterRead, others, cells⟩
  simpa only [answersShape, List.length_replicate, count] using returned

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLPreimageExecution
