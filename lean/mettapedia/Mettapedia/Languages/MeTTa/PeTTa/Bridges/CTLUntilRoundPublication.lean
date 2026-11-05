import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundViews

/-!
# Fresh publication trace of actual completed EU rounds

The live membership test determines an ordered list of newly published nodes.
Known rows and pre-existing next-round rows are retained as prefixes. The
new list is duplicate-free, disjoint from initially known nodes, and has one
entry per produced collector packet. It is not yet identified with the
mathematical candidate planner's fresh list.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundPublication

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open NamedGuardedCandidateBatch (State)
open FlatQueryRowCodec (Codec)
open CTLUntilMixedStore (Row render decodeRows)
open CTLUntilScopedRound

variable {Context Label : Type} [DecidableEq Label]

def observe {Value : Type} (codec : Codec Label) (view : List (Row Label) → Value)
    (handle : NamedSpaces.Handle) (state : Effects.State) : Option Value :=
  ((state.read handle).bind (decodeRows codec)).map view

omit [DecidableEq Label] in
theorem observe_decoded {Value : Type} (codec : Codec Label) (view : List (Row Label) → Value)
    (handle : NamedSpaces.Handle) (state : Effects.State) (atoms : List Atom) (rows : List (Row Label))
    (snapshot : state.read handle = some atoms) (decoded : decodeRows codec atoms = some rows) :
    observe codec view handle state = some (view rows) := by
  simp only [observe, snapshot, Option.bind_some, decoded, Option.map_some]

def known (codec : Codec Label) (label : Label) (query : Query) (state : Effects.State) : Option (List Nat) :=
  observe codec (CTLUntilMixedStore.satisfactionView label) query.satisfactionHandle state

def frontier (codec : Codec Label) (label : Label) (round : Nat) (query : Query) (state : Effects.State) : Option (List Nat) :=
  observe codec (List.filterMap (CTLUntilMixedStore.frontSelect label (round + 1))) query.nextFrontierHandle state

theorem leaf_views (codec : Codec Label) (label : Label) (round node : Nat) (query : Query)
    (before after : State Context)
    (receipt : CTLUntilLeafPublication.Refinement codec label round node query.template before after)
    (valid : Decoded codec query.handles before) :
    ∃ oldKnown oldFrontier,
      known codec label query before.world.state = some oldKnown ∧
      frontier codec label round query before.world.state = some oldFrontier ∧
      known codec label query after.world.state = some (oldKnown ++ if receipt.fresh then [node] else []) ∧
      frontier codec label round query after.world.state = some (oldFrontier ++ if receipt.fresh then [node] else []) ∧
      (receipt.fresh = true → node ∉ oldKnown) := by
  obtain ⟨knownAtoms, knownRows, knownRead, knownDecode⟩ := valid query.satisfactionHandle (by simp [Query.handles])
  obtain ⟨frontAtoms, frontRows, frontRead, frontDecode⟩ := valid query.nextFrontierHandle (by simp [Query.handles])
  have knownAfter := receipt.decoded_after query.satisfactionHandle knownAtoms knownRows knownRead knownDecode
  have frontAfter := receipt.decoded_after query.nextFrontierHandle frontAtoms frontRows frontRead frontDecode
  have guardSame : receipt.guardRows = knownAtoms := Option.some.inj (receipt.snapshot.symm.trans knownRead)
  refine ⟨CTLUntilMixedStore.satisfactionView label knownRows,
    frontRows.filterMap (CTLUntilMixedStore.frontSelect label (round + 1)),
    observe_decoded codec _ _ _ _ _ knownRead knownDecode,
    observe_decoded codec _ _ _ _ _ frontRead frontDecode, ?_, ?_, ?_⟩
  · change observe codec _ _ _ = _
    rw [observe_decoded codec _ _ _ _ _ knownAfter.1 knownAfter.2]
    cases receipt.fresh with
    | false => simp
    | true => simp only [↓reduceIte]
              rw [CTLUntilPublicationSource.satisfaction_view_append]
              simp [Query.template]
  · change observe codec _ _ _ = _
    rw [observe_decoded codec _ _ _ _ _ frontAfter.1 frontAfter.2]
    cases receipt.fresh with
    | false => simp
    | true => simp only [↓reduceIte]
              rw [CTLUntilPublicationSource.next_frontier_view_append]
              simp [Query.template]
  · intro fresh present
    have raw := (CTLUntilPublicationSource.satisfaction_membership codec label node knownAtoms knownRows knownDecode).mpr present
    have decision := receipt.decision
    rw [guardSame] at decision
    simp [raw, fresh] at decision

def Published (codec : Codec Label) (label : Label) (round : Nat) (query : Query)
    (initialKnown initialFrontier : List Nat) (initialCount : Nat) (state : State Context) : Prop :=
  ∃ added : List Nat, added.Nodup ∧ (∀ node ∈ added, node ∉ initialKnown) ∧
    known codec label query state.world.state = some (initialKnown ++ added) ∧
    frontier codec label round query state.world.state = some (initialFrontier ++ added) ∧
    state.scope.collected.length = initialCount + added.length

/-- Exact branch decision for the live guard, not only the implication that
a successful insertion was fresh. -/
theorem leaf_decision (codec : Codec Label) (label : Label) (round node : Nat) (query : Query)
    (before after : State Context)
    (receipt : CTLUntilLeafPublication.Refinement codec label round node query.template before after)
    (valid : Decoded codec query.handles before) (oldKnown : List Nat)
    (observed : known codec label query before.world.state = some oldKnown) :
    receipt.fresh = !decide (node ∈ oldKnown) := by
  obtain ⟨atoms, rows, snapshot, decoded⟩ := valid query.satisfactionHandle (by simp [Query.handles])
  have view := observe_decoded codec (CTLUntilMixedStore.satisfactionView label) query.satisfactionHandle
    before.world.state atoms rows snapshot decoded
  have same := Option.some.inj (observed.symm.trans view)
  subst oldKnown
  have guardSame : receipt.guardRows = atoms := Option.some.inj (receipt.snapshot.symm.trans snapshot)
  have decision := receipt.decision
  rw [guardSame] at decision
  simpa only [CTLUntilPublicationSource.satisfaction_membership codec label node atoms rows decoded] using decision

theorem leaf_published (codec : Codec Label) (label operand : Label) (round : Nat) (query : Query)
    (initialKnown initialFrontier : List Nat) (initialCount : Nat) (program : SpaceSemantics.Program) :
    ScopedNestedQueryExecution.PreservesOn (Frame codec label operand round query [])
      (fun state : State Context => Decoded codec query.handles state ∧
        Published codec label round query initialKnown initialFrontier initialCount state)
      (GuardedNestedQuerySource.leaf program query.template Context).execute := by
  intro caller before context origins pending after frame admitted completed
  have decoded := leaf_preserves codec label operand round query program query.handles
    caller before context origins pending after frame admitted.1 completed
  cases frame with
  | publish _ resolved fixed node bound =>
    obtain ⟨principal, resolved⟩ := resolved
    have readings := fixed principal (resolve_sound resolved)
    have payload := CTLUntilCandidateAdmission.payload_readings codec label round node query.names principal
      readings.1 readings.2.2.2 (bound principal (resolve_sound resolved))
    obtain ⟨receipt⟩ := CTLUntilLeafPublication.completed_refinement codec label round node program query.template
      caller before after context origins pending principal resolved payload.1 payload.2 completed
    obtain ⟨oldKnown, oldFrontier, oldKnownRead, oldFrontierRead, newKnownRead, newFrontierRead, absent⟩ :=
      leaf_views codec label round node query before after receipt admitted.1
    obtain ⟨added, nodup, disjoint, knownRead, frontierRead, count⟩ := admitted.2
    have knownSame := Option.some.inj (oldKnownRead.symm.trans knownRead)
    have frontierSame := Option.some.inj (oldFrontierRead.symm.trans frontierRead)
    subst oldKnown
    subst oldFrontier
    refine ⟨decoded, ?_⟩
    cases fresh : receipt.fresh with
    | false =>
      refine ⟨added, nodup, disjoint, ?_, ?_, ?_⟩
      · simpa [fresh] using newKnownRead
      · simpa [fresh] using newFrontierRead
      · have unchanged := receipt.count
        simp only [fresh, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at unchanged
        exact unchanged.trans count
    | true =>
      have notKnown := absent fresh
      have parts : node ∉ initialKnown ∧ node ∉ added := by simpa using notKnown
      refine ⟨added ++ [node], ?_, ?_, ?_, ?_, ?_⟩
      · exact List.nodup_append.mpr ⟨nodup, by simp, by
          intro old member new memberNew equal
          have same : new = node := by simpa using memberNew
          exact parts.2 ((equal.trans same) ▸ member)⟩
      · intro value member
        rcases List.mem_append.mp member with old | latest
        · exact disjoint value old
        · cases List.mem_singleton.mp latest
          exact parts.1
      · simpa [fresh, List.append_assoc] using newKnownRead
      · simpa [fresh, List.append_assoc] using newFrontierRead
      · have increase := receipt.count
        simp only [fresh, ↓reduceIte] at increase
        simp only [List.length_append, List.length_singleton]
        omega

/-- The actual completed round publishes a duplicate-free ordered extension
to both outputs, retains their old occurrence lists, and produces exactly
one packet per new node. Final decoding is obtained from the same run. -/
theorem completed_publication (codec : Codec Label) (label operand : Label) (round : Nat) (query : Query)
    (apart : query.names.prior ≠ query.names.next) (program : SpaceSemantics.Program)
    (caller : Control) (before after : State Context) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) (resolved : Resolved caller)
    (fixed : Fixed codec label operand round query caller)
    (nextFresh : ClosedOnceQueryFrame.FreshFor query.names.next caller.bindings)
    (priorFresh : ClosedOnceQueryFrame.FreshFor query.names.prior caller.bindings)
    (valid : Decoded codec query.handles before) (initialKnown initialFrontier : List Nat)
    (knownRead : known codec label query before.world.state = some initialKnown)
    (frontierRead : frontier codec label round query before.world.state = some initialFrontier)
    (completed : (ScopedNestedQueryExecution.run program (GuardedNestedQuerySource.leaf program query.template Context)
      query.legs caller before context origins pending).stop = .complete after) :
    Decoded codec query.handles after ∧
      Published codec label round query initialKnown initialFrontier before.scope.collected.length after := by
  let invariant : State Context → Prop := fun state => Decoded codec query.handles state ∧
    Published codec label round query initialKnown initialFrontier before.scope.collected.length state
  apply ScopedNestedQueryExecution.run_preserves_family program
    (GuardedNestedQuerySource.leaf program query.template Context) (Frame codec label operand round query) invariant
    (leaf_published codec label operand round query initialKnown initialFrontier before.scope.collected.length program)
    (fun leg rest currentCaller current currentContext currentOrigins currentPending selected frame admitted captured =>
      capture_frame codec label operand round query apart program leg rest currentCaller current currentContext
        currentOrigins currentPending selected frame admitted.1 captured) query.legs
    caller before context origins pending after (Frame.frontier caller resolved fixed nextFresh priorFresh) _ completed
  exact ⟨valid, [], by simp, by simp, by simpa using knownRead, by simpa using frontierRead, by simp⟩

/-- Only the fixed output label is counted. Old duplicate occurrences remain
in the list, while each fresh publication increases its support by one. -/
theorem Published.fixed_label_count {codec : Codec Label} {label : Label} {round : Nat} {query : Query}
    {initialKnown initialFrontier : List Nat} {initialCount : Nat} {state : State Context}
    (published : Published codec label round query initialKnown initialFrontier initialCount state)
    (finalKnown : List Nat) (observed : known codec label query state.world.state = some finalKnown) :
    finalKnown.toFinset.card + initialCount = initialKnown.toFinset.card + state.scope.collected.length := by
  obtain ⟨added, nodup, separate, knownRead, _frontierRead, count⟩ := published
  have same := Option.some.inj (observed.symm.trans knownRead)
  subst finalKnown
  have disjoint : Disjoint initialKnown.toFinset added.toFinset := by
    apply Finset.disjoint_left.mpr
    intro node initial new
    exact separate node (List.mem_toFinset.mp new) (List.mem_toFinset.mp initial)
  rw [List.toFinset_append, Finset.card_union_of_disjoint disjoint, List.toFinset_card_of_nodup nodup, count]
  omega

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundPublication
