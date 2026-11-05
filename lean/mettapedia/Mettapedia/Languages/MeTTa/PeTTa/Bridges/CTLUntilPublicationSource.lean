import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedInsertionSequence
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedInsertionPairSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilMixedCapture

/-!
# Actual EU writes and decoded source-store publication

Available source handles construct the two primitive receipts. The authored
insertion body executes them in order and retains its caller. Observation of
any handle records zero, one or both appended rows, so aliased and separate
targets share one law. No atomic transaction or native allocation guarantee
is inferred from the logical store model.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilPublicationSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor placed)
open FlatQueryRowCodec (Codec)
open CTLUntilMixedStore (Row render decodeRows)
open CTLUntilSourceRows (number)

variable {Label : Type}

def additions (label : Label) (round node : Nat)
    (satisfactionHandle frontierHandle observed : NamedSpaces.Handle) : List (Row Label) :=
  (if observed = satisfactionHandle then [.satisfaction label node] else []) ++
    (if observed = frontierHandle then [.frontier label (round + 1) node] else [])

theorem additions_admitted (label : Label) (round node : Nat)
    (satisfactionHandle frontierHandle observed : NamedSpaces.Handle) :
    ∀ row ∈ additions label round node satisfactionHandle frontierHandle observed, row.admitted := by
  unfold additions
  split_ifs <;> simp [Row.admitted]

theorem satisfaction_literal (codec : Codec Label) (label : Label) (node : Nat) :
    SpaceSemantics.Literal (render codec (.satisfaction label node)) := by
  apply SpaceSemantics.Literal.constructor "sat" _ (by decide)
  intro atom member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact codec.literal label
  · exact .grounded _

theorem frontier_literal (codec : Codec Label) (label : Label) (round node : Nat) :
    SpaceSemantics.Literal (render codec (.frontier label round node)) := by
  apply SpaceSemantics.Literal.constructor "fr" _ (by decide)
  intro atom member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact codec.literal label
  · exact .grounded _
  · exact .grounded _

theorem satisfaction_ordinary (codec : Codec Label) (label : Label) (node : Nat) :
    ScopedQuerySource.mutationPayload false (render codec (.satisfaction label node)) = true := by
  have ground := ClosedQueryAdmission.literal_ground (satisfaction_literal codec label node)
  change (Mettapedia.Languages.ProcessCalculi.MORK.isGroundAtom (render codec (.satisfaction label node)) && true) = true
  simpa only [Bool.and_true] using ground

theorem frontier_ordinary (codec : Codec Label) (label : Label) (round node : Nat) :
    ScopedQuerySource.mutationPayload false (render codec (.frontier label round node)) = true := by
  have ground := ClosedQueryAdmission.literal_ground (frontier_literal codec label round node)
  change (Mettapedia.Languages.ProcessCalculi.MORK.isGroundAtom (render codec (.frontier label round node)) && true) = true
  simpa only [Bool.and_true] using ground

/-- The actual primitive receipts induce exactly the typed append used by
the view-stability lemmas. Every admitted observation can be decoded again. -/
theorem raw_after_writes (codec : Codec Label) (label : Label) (round node : Nat)
    (before middle after : Effects.State) (satisfactionHandle frontierHandle observed : NamedSpaces.Handle)
    (first : Effects.insert before satisfactionHandle (render codec (.satisfaction label node)) = some middle)
    (second : Effects.insert middle frontierHandle (render codec (.frontier label (round + 1) node)) = some after) :
    after.read observed = (before.read observed).map
      (fun atoms => atoms ++ (additions label round node satisfactionHandle frontierHandle observed).map (render codec)) := by
  rw [ScopedInsertionSequence.pair_store_receipt before middle after _ _ _ _ first second observed]
  unfold additions
  split_ifs <;> simp [List.append_assoc]

theorem decoded_after_writes (codec : Codec Label) (label : Label) (round node : Nat)
    (before middle after : Effects.State) (satisfactionHandle frontierHandle observed : NamedSpaces.Handle)
    (atoms : List Atom) (rows : List (Row Label))
    (first : Effects.insert before satisfactionHandle (render codec (.satisfaction label node)) = some middle)
    (second : Effects.insert middle frontierHandle (render codec (.frontier label (round + 1) node)) = some after)
    (snapshot : before.read observed = some atoms) (decoded : decodeRows codec atoms = some rows) :
    after.read observed = some ((rows ++ additions label round node satisfactionHandle frontierHandle observed).map (render codec)) ∧
      decodeRows codec ((rows ++ additions label round node satisfactionHandle frontierHandle observed).map (render codec)) =
        some (rows ++ additions label round node satisfactionHandle frontierHandle observed) := by
  obtain ⟨actual, admitted⟩ := CTLUntilMixedStore.decode_rows_sound codec atoms rows decoded
  constructor
  · rw [raw_after_writes codec label round node before middle after satisfactionHandle frontierHandle observed first second, snapshot]
    simp [actual, List.map_append]
  · apply CTLUntilMixedStore.decode_rows_complete
    intro row member
    rcases List.mem_append.mp member with old | added
    · exact admitted row old
    · exact additions_admitted label round node satisfactionHandle frontierHandle observed row added

/-- The canonical source body constructs and executes the two writes from
available handles. Its conclusion supplies the state transition rather than
requiring a caller-provided successful insertion result. -/
theorem body_prefix {Context : Type} (codec : Codec Label) (label : Label) (round node : Nat)
    (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (caller : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (result temporary : String) (satisfactionHandle frontierHandle : NamedSpaces.Handle)
    (firstCode secondCode : Atom) (principal : Environment) (satisfactionRows frontierRows : List Atom)
    (resolved : resolve caller.bindings = some principal)
    (freshTemporary : FreshFor temporary caller.bindings) (freshResult : FreshFor result caller.bindings)
    (distinct : temporary ≠ result)
    (firstRead : read principal firstCode = render codec (.satisfaction label node))
    (secondRead : read principal secondCode = render codec (.frontier label (round + 1) node))
    (satisfactionSnapshot : world.state.read satisfactionHandle = some satisfactionRows)
    (frontierSnapshot : world.state.read frontierHandle = some frontierRows) :
    ∃ middle after,
      Effects.insert world.state satisfactionHandle (render codec (.satisfaction label node)) = some middle ∧
      Effects.insert middle frontierHandle (render codec (.frontier label (round + 1) node)) = some after ∧
      (ScopedQuerySource.machine .relational program).run 13
        (placed allocator world scope parents
          (ScopedInsertionSequence.entry caller result temporary satisfactionHandle frontierHandle firstCode secondCode)
          context origins pending) =
        ([], .exhausted (placed allocator {world with state := after} scope parents
          (ScopedInsertionSequence.returned caller result temporary satisfactionHandle frontierHandle firstCode secondCode)
          context (origins ++ [0, 0]) pending)) ∧
      (∀ observed atoms rows, world.state.read observed = some atoms → decodeRows codec atoms = some rows →
        after.read observed = some ((rows ++ additions label round node satisfactionHandle frontierHandle observed).map (render codec))) ∧
      after.cells = world.state.cells := by
  obtain ⟨middle, after, first, second⟩ := ScopedInsertionSequence.pair_exists world.state satisfactionHandle frontierHandle
    (render codec (.satisfaction label node)) (render codec (.frontier label (round + 1) node))
    satisfactionRows frontierRows satisfactionSnapshot frontierSnapshot
  refine ⟨middle, after, first, second, ?_, ?_, ?_⟩
  · exact ScopedInsertionSequence.source_prefix program allocator world scope parents caller context origins pending result temporary
      satisfactionHandle frontierHandle firstCode secondCode _ _ principal middle after resolved freshTemporary freshResult distinct
      firstRead secondRead (LiteralQuerySource.read_literal _ (satisfaction_literal codec label node))
      (LiteralQuerySource.read_literal _ (frontier_literal codec label (round + 1) node))
      (satisfaction_ordinary codec label node) (frontier_ordinary codec label (round + 1) node) first second
  · intro observed atoms rows snapshot decoded
    exact (decoded_after_writes codec label round node world.state middle after satisfactionHandle frontierHandle observed
      atoms rows first second snapshot decoded).1
  · exact (Effects.insert_preserves_cells second).trans (Effects.insert_preserves_cells first)

theorem additions_in_publication (codec : Codec Label) (label : Label) (round node : Nat)
    (satisfactionHandle frontierHandle observed : NamedSpaces.Handle) (atom : Atom)
    (member : atom ∈ (additions label round node satisfactionHandle frontierHandle observed).map (render codec)) :
    atom ∈ (CTLUntilMixedCapture.publication label round node).map (render codec) := by
  unfold additions at member
  split_ifs at member <;> simp_all [CTLUntilMixedCapture.publication]

/-- Exact source-write receipts preserve any capture view whose pattern
cannot match the published pair. Missing reads and capture refusal are kept
as such. Live query admission remains a separate obligation. -/
theorem capture_view_after_writes (codec : Codec Label) (label : Label) (round node : Nat)
    (before middle after : Effects.State) (satisfactionHandle frontierHandle observed : NamedSpaces.Handle)
    (caller : Control) (pattern body destination : Atom) (older : List Goal) (offset : Nat)
    (first : Effects.insert before satisfactionHandle (render codec (.satisfaction label node)) = some middle)
    (second : Effects.insert middle frontierHandle (render codec (.frontier label (round + 1) node)) = some after)
    (unmatched : ∀ atom ∈ (CTLUntilMixedCapture.publication label round node).map (render codec),
      SpaceSemantics.matchValue [] pattern atom = none) :
    (after.read observed).bind (ScopedQuerySource.capture caller pattern body destination older offset) =
      (before.read observed).bind (ScopedQuerySource.capture caller pattern body destination older offset) := by
  rw [raw_after_writes codec label round node before middle after satisfactionHandle frontierHandle observed first second]
  cases snapshot : before.read observed with
  | none => rfl
  | some atoms =>
      simp only [Option.map_some, Option.bind_some]
      apply ScopedQueryScanStability.capture_append_unmatched
      intro atom member
      exact unmatched atom (additions_in_publication codec label round node satisfactionHandle frontierHandle observed atom member)

variable [DecidableEq Label]

theorem satisfaction_view_member (label : Label) (node : Nat) (rows : List (Row Label)) :
    node ∈ CTLUntilMixedStore.satisfactionView label rows ↔ Row.satisfaction label node ∈ rows := by
  simp only [CTLUntilMixedStore.satisfactionView, List.mem_filterMap]
  constructor
  · rintro ⟨row, member, selected⟩
    cases row with
    | satisfaction other value =>
        change (if other = label then some value else none) = some node at selected
        split at selected
        next same =>
          cases Option.some.inj selected
          subst other
          exact member
        next => cases selected
    | frontier | edge | other => cases selected
  · intro member
    exact ⟨.satisfaction label node, member, by simp⟩

/-- The guard's actual Atom membership is exactly the typed known-state
membership, including in stores containing unrelated open declarations. -/
theorem satisfaction_membership (codec : Codec Label) (label : Label) (node : Nat)
    (atoms : List Atom) (rows : List (Row Label)) (decoded : decodeRows codec atoms = some rows) :
    render codec (.satisfaction label node) ∈ atoms ↔ node ∈ CTLUntilMixedStore.satisfactionView label rows := by
  obtain ⟨actual, admitted⟩ := CTLUntilMixedStore.decode_rows_sound codec atoms rows decoded
  rw [← actual, satisfaction_view_member]
  constructor
  · rintro member
    obtain ⟨row, present, equal⟩ := List.mem_map.mp member
    have same := congrArg (CTLUntilMixedStore.decode codec) equal
    rw [CTLUntilMixedStore.decode_render codec row (admitted row present),
      CTLUntilMixedStore.decode_render codec (.satisfaction label node) trivial] at same
    exact (Option.some.inj same) ▸ present
  · intro member
    exact List.mem_map.mpr ⟨_, member, rfl⟩

theorem satisfaction_view_append (label : Label) (round node : Nat)
    (satisfactionHandle frontierHandle observed : NamedSpaces.Handle) (rows : List (Row Label)) :
    CTLUntilMixedStore.satisfactionView label
      (rows ++ additions label round node satisfactionHandle frontierHandle observed) =
      CTLUntilMixedStore.satisfactionView label rows ++
        if observed = satisfactionHandle then [node] else [] := by
  unfold CTLUntilMixedStore.satisfactionView additions
  split_ifs <;> simp

/-- Freshness is measured against known-state support, not the number of
stored occurrences. Existing duplicate rows are retained. -/
theorem fresh_known_cardinality (label : Label) (round node : Nat)
    (satisfactionHandle frontierHandle : NamedSpaces.Handle) (rows : List (Row Label))
    (fresh : node ∉ CTLUntilMixedStore.satisfactionView label rows) :
    (CTLUntilMixedStore.satisfactionView label
      (rows ++ additions label round node satisfactionHandle frontierHandle satisfactionHandle)).toFinset.card =
      (CTLUntilMixedStore.satisfactionView label rows).toFinset.card + 1 := by
  rw [satisfaction_view_append]
  simp [List.toFinset_append, fresh, Finset.card_insert_of_notMem]

theorem next_frontier_view_append (label : Label) (round node : Nat)
    (satisfactionHandle frontierHandle observed : NamedSpaces.Handle) (rows : List (Row Label)) :
    (rows ++ additions label round node satisfactionHandle frontierHandle observed).filterMap
      (CTLUntilMixedStore.frontSelect label (round + 1)) =
      rows.filterMap (CTLUntilMixedStore.frontSelect label (round + 1)) ++
        if observed = frontierHandle then [node] else [] := by
  unfold additions
  split_ifs <;> simp [CTLUntilMixedStore.frontSelect, List.filterMap_append, List.filterMap_cons]

theorem current_frontier_view_append (label : Label) (round node : Nat)
    (satisfactionHandle frontierHandle observed : NamedSpaces.Handle) (rows : List (Row Label)) :
    (rows ++ additions label round node satisfactionHandle frontierHandle observed).filterMap
      (CTLUntilMixedStore.frontSelect label round) =
      rows.filterMap (CTLUntilMixedStore.frontSelect label round) := by
  unfold additions
  split_ifs <;> simp [CTLUntilMixedStore.frontSelect, List.filterMap_append, List.filterMap_cons]

theorem operand_view_append (label holds : Label) (apart : label ≠ holds) (round node : Nat)
    (satisfactionHandle frontierHandle observed : NamedSpaces.Handle) (rows : List (Row Label)) :
    CTLUntilMixedStore.satisfactionView holds
      (rows ++ additions label round node satisfactionHandle frontierHandle observed) =
      CTLUntilMixedStore.satisfactionView holds rows := by
  unfold CTLUntilMixedStore.satisfactionView additions
  split_ifs <;> simp [apart]

def request (codec : Codec Label) (handle : NamedSpaces.Handle) (label : Label) (node : Nat) : LiteralQuerySource.Request :=
  ⟨handle, render codec (.satisfaction label node), satisfaction_literal codec label node,
    .symbol "t", .symbol "t", by simp [LiteralQuerySource.ordinaryQuery, render]⟩

/-- For the inlined guard spelling, typed absence and available handles
construct actual guarded execution and the resulting source-store update.
Named-call entry remains a separate composition boundary. -/
theorem fresh_candidate_prefix {Context : Type} (codec : Codec Label) (label : Label) (round node : Nat)
    (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (caller : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (result temporary : String) (satisfactionHandle frontierHandle : NamedSpaces.Handle)
    (firstCode secondCode : Atom) (principal : Environment) (atoms frontierAtoms : List Atom) (rows : List (Row Label))
    (resolved : resolve caller.bindings = some principal)
    (freshTemporary : FreshFor temporary caller.bindings) (freshResult : FreshFor result caller.bindings)
    (distinct : temporary ≠ result)
    (firstRead : read principal firstCode = render codec (.satisfaction label node))
    (secondRead : read principal secondCode = render codec (.frontier label (round + 1) node))
    (satisfactionSnapshot : world.state.read satisfactionHandle = some atoms)
    (frontierSnapshot : world.state.read frontierHandle = some frontierAtoms)
    (decoded : decodeRows codec atoms = some rows)
    (absent : node ∉ CTLUntilMixedStore.satisfactionView label rows) :
    ∃ middle after,
      Effects.insert world.state satisfactionHandle (render codec (.satisfaction label node)) = some middle ∧
      Effects.insert middle frontierHandle (render codec (.frontier label (round + 1) node)) = some after ∧
      (ScopedQuerySource.machine .relational program).run 32
        (placed allocator world scope parents
          (GuardedInsertionPairSource.entry caller result (request codec satisfactionHandle label node)
            frontierHandle temporary firstCode secondCode) context origins pending) =
        ([], .exhausted (placed allocator {world with state := after} scope parents
          (GuardedInsertionPairSource.afterInsert caller result (request codec satisfactionHandle label node)
            frontierHandle temporary firstCode secondCode) context (origins ++ [0, 0, 0, 0]) pending)) ∧
      after.read satisfactionHandle =
        some ((rows ++ additions label round node satisfactionHandle frontierHandle satisfactionHandle).map (render codec)) := by
  obtain ⟨actual, admitted⟩ := CTLUntilMixedStore.decode_rows_sound codec atoms rows decoded
  obtain ⟨middle, after, first, second⟩ := ScopedInsertionSequence.pair_exists world.state satisfactionHandle frontierHandle
    (render codec (.satisfaction label node)) (render codec (.frontier label (round + 1) node))
    atoms frontierAtoms satisfactionSnapshot frontierSnapshot
  have missing := mt (satisfaction_membership codec label node atoms rows decoded).mp absent
  have ready : ClosedQueryAdmission.rowsReady (render codec (.satisfaction label node)) atoms = true := by
    rw [← actual]
    exact CTLUntilMixedStore.rows_ready codec "sat" _ (by simp) rows admitted
  refine ⟨middle, after, first, second, ?_, ?_⟩
  · exact GuardedInsertionPairSource.fresh_prefix program allocator world scope parents caller context origins pending
      result temporary (request codec satisfactionHandle label node) frontierHandle firstCode secondCode
      (render codec (.frontier label (round + 1) node)) principal middle after resolved firstRead secondRead
      (LiteralQuerySource.read_literal _ (frontier_literal codec label (round + 1) node))
      freshTemporary freshResult distinct atoms satisfactionSnapshot ready missing
      (satisfaction_ordinary codec label node) (frontier_ordinary codec label (round + 1) node) first second
  · exact (decoded_after_writes codec label round node world.state middle after satisfactionHandle frontierHandle satisfactionHandle
      atoms rows first second satisfactionSnapshot decoded).1

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilPublicationSource
