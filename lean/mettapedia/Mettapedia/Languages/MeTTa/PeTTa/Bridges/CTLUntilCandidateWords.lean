import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundViews

/-!
# Ordered candidate words carried by live EU query frames

Each capture partitions the initial candidate word into the words of its
actual selected children. Stability transports the current capture view at
the same prepared caller; it never replaces execution by a frozen-world run.
Physical occurrence coordinates and repeated candidates remain in order.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCandidateWords

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open NamedGuardedCandidateBatch (State)
open FlatQueryRowCodec (Codec)
open CTLUntilMixedStore (Row render decodeRows graphView satisfactionView frontSelect edgeSelect satSelect)
open CTLUntilSourceRows (number located)
open CTLUntilScopedRound
open CTLUntilRoundViews (CaptureView Stable)
open ClosedOnceQueryFrame (FreshFor)
open NestedQuerySource (Leg)

open Mettapedia.Machines

variable {Context Label : Type} [DecidableEq Label]

inductive WordFrame (codec : Codec Label) (label operand : Label) (round : Nat) (query : Query)
    (fronts graph facts : List (Row Label)) : List Leg → Control → List Nat → Prop
  | frontier (caller : Control) (resolved : Resolved caller) (fixed : Fixed codec label operand round query caller)
      (nextFresh : FreshFor query.names.next caller.bindings) (priorFresh : FreshFor query.names.prior caller.bindings) :
      WordFrame codec label operand round query fronts graph facts query.legs caller
        (CTLUntilCandidateBag.candidates (graphView graph) (satisfactionView operand facts) (fronts.filterMap (frontSelect label round)))
  | edge (caller : Control) (resolved : Resolved caller) (fixed : Fixed codec label operand round query caller)
      (next : Nat) (bound : Bound caller query.names.next next) (priorFresh : FreshFor query.names.prior caller.bindings) :
      WordFrame codec label operand round query fronts graph facts [query.edge, query.satisfaction] caller
        (CTLUntilCandidateBag.candidates (graphView graph) (satisfactionView operand facts) [next])
  | satisfaction (caller : Control) (resolved : Resolved caller) (fixed : Fixed codec label operand round query caller)
      (prior : Nat) (bound : Bound caller query.names.prior prior) :
      WordFrame codec label operand round query fronts graph facts [query.satisfaction] caller
        ((satisfactionView operand facts).filter (fun node => node == prior))
  | leaf (caller : Control) (resolved : Resolved caller) (fixed : Fixed codec label operand round query caller)
      (prior : Nat) (bound : Bound caller query.names.prior prior) :
      WordFrame codec label operand round query fronts graph facts [] caller [prior]

theorem WordFrame.frame {codec : Codec Label} {label operand : Label} {round : Nat} {query : Query}
    {fronts graph facts : List (Row Label)} {legs : List Leg} {caller : Control} {word : List Nat}
    (framed : WordFrame codec label operand round query fronts graph facts legs caller word) :
    Frame codec label operand round query legs caller := by
  cases framed with
  | frontier _ resolved fixed nextFresh priorFresh => exact .frontier _ resolved fixed nextFresh priorFresh
  | edge _ resolved fixed next bound priorFresh => exact .edge _ resolved fixed next bound priorFresh
  | satisfaction _ resolved fixed prior bound => exact .satisfaction _ resolved fixed prior bound
  | leaf _ resolved fixed prior bound => exact .publish _ resolved fixed prior bound

omit [DecidableEq Label] in
private theorem frame_resolved {codec : Codec Label} {label operand : Label} {round : Nat} {query : Query}
    {legs : List Leg} {caller : Control} (framed : Frame codec label operand round query legs caller) : Resolved caller := by
  cases framed <;> assumption

omit [DecidableEq Label] in
private theorem frame_fixed {codec : Codec Label} {label operand : Label} {round : Nat} {query : Query}
    {legs : List Leg} {caller : Control} (framed : Frame codec label operand round query legs caller) :
    Fixed codec label operand round query caller := by
  cases framed <;> assumption

omit [DecidableEq Label] in
private theorem frame_prior_fresh {codec : Codec Label} {label operand : Label} {round : Nat} {query : Query}
    {legs : List Leg} {caller : Control} (framed : Frame codec label operand round query legs caller)
    (two : legs.length = 2) : FreshFor query.names.prior caller.bindings := by
  cases framed with
  | frontier => simp [Query.legs] at two
  | edge _ _ _ _ _ fresh => exact fresh
  | satisfaction => simp at two
  | publish => simp at two

private theorem edge_word {codec : Codec Label} {label operand : Label} {round : Nat} {query : Query}
    (fronts graph facts : List (Row Label)) {caller : Control} (next : Nat)
    (framed : Frame codec label operand round query [query.edge, query.satisfaction] caller)
    (bound : Bound caller query.names.next next) :
    WordFrame codec label operand round query fronts graph facts [query.edge, query.satisfaction] caller
      (CTLUntilCandidateBag.candidates (graphView graph) (satisfactionView operand facts) [next]) :=
  .edge _ (frame_resolved framed) (frame_fixed framed) next bound (frame_prior_fresh framed rfl)

private theorem satisfaction_word {codec : Codec Label} {label operand : Label} {round : Nat} {query : Query}
    (fronts graph facts : List (Row Label)) {caller : Control} (prior : Nat)
    (framed : Frame codec label operand round query [query.satisfaction] caller)
    (bound : Bound caller query.names.prior prior) :
    WordFrame codec label operand round query fronts graph facts [query.satisfaction] caller
      ((satisfactionView operand facts).filter (fun node => node == prior)) :=
  .satisfaction _ (frame_resolved framed) (frame_fixed framed) prior bound

private theorem leaf_word {codec : Codec Label} {label operand : Label} {round : Nat} {query : Query}
    (fronts graph facts : List (Row Label)) {caller : Control} (prior : Nat)
    (framed : Frame codec label operand round query [] caller) (bound : Bound caller query.names.prior prior) :
    WordFrame codec label operand round query fronts graph facts [] caller [prior] :=
  .leaf _ (frame_resolved framed) (frame_fixed framed) prior bound

/-- Recover the actual matcher call from a successful entry receipt. -/
private theorem captured_view (program : SpaceSemantics.Program) (handle : NamedSpaces.Handle)
    (pattern body destination : Atom) (caller : Control) (state : State Context) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (selected : ScopedMatchEntry.Selection body destination caller.goals)
    (captured : (ScopedMatchEntry.execute program handle pattern body destination caller state context origins pending).result =
      .captured selected) :
    ∃ environment,
      resolve (ScopedMatchPreparation.ready caller destination handle pattern body).bindings = some environment ∧
      CaptureView state.world.state handle (ScopedMatchPreparation.ready caller destination handle pattern body)
        (read environment pattern) body destination caller.goals 0 = some selected.choices := by
  unfold ScopedMatchEntry.execute at captured
  split at captured
  · cases captured
  next principal resolved =>
    dsimp only at captured
    split at captured
    next failed =>
      obtain ⟨environment, success⟩ := resolve_complete
        (ScopedMatchPreparation.ready_consistent caller destination handle pattern body ⟨principal, resolve_sound resolved⟩)
      rw [failed] at success
      cases success
    next environment prepared =>
      split at captured
      · cases captured
      next atoms snapshot =>
        split at captured
        next complete =>
          split at captured
          next unfused =>
            split at captured
            · cases captured
            next choices actual =>
              have same := congrArg ScopedMatchEntry.Selection.choices (ScopedMatchEntry.Result.captured.inj captured)
              exact ⟨environment, prepared, by simpa only [CaptureView, snapshot, Option.bind_some, actual] using congrArg some same⟩
          next => cases captured
        next => cases captured

/-- Every live capture partitions the fixed initial candidate word. The
three initial reads are typed data evidence, not an expected execution. -/
theorem capture_words (codec : Codec Label) (label operand : Label) (round : Nat) (query : Query)
    (fronts graph facts : List (Row Label)) (apart : query.names.prior ≠ query.names.next)
    (program : SpaceSemantics.Program) (initial : Effects.State)
    (frontAtoms graphAtoms factAtoms : List Atom)
    (frontRead : initial.read query.frontierHandle = some frontAtoms) (frontDecode : decodeRows codec frontAtoms = some fronts)
    (graphRead : initial.read query.edgeHandle = some graphAtoms) (graphDecode : decodeRows codec graphAtoms = some graph)
    (factRead : initial.read query.operandHandle = some factAtoms) (factDecode : decodeRows codec factAtoms = some facts)
    (leg : Leg) (rest : List Leg) (caller : Control) (state : State Context)
    (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (word : List Nat)
    (selected : ScopedMatchEntry.Selection (ScopedNestedQueryExecution.source rest query.template.source)
      (.var query.names.result) caller.goals)
    (framed : WordFrame codec label operand round query fronts graph facts (leg :: rest) caller word)
    (valid : Decoded codec query.handles state)
    (stable : Stable codec label operand round query initial state.world.state)
    (captured : (ScopedMatchEntry.execute program leg.1 leg.2
      (ScopedNestedQueryExecution.source rest query.template.source) (.var query.names.result)
      caller state context origins pending).result = .captured selected) :
    ∃ words : List (List Nat),
      List.Forall₂ (fun entry part => WordFrame codec label operand round query fronts graph facts rest
        {entry.2 with goals := caller.goals} part) selected.choices words ∧ words.flatten = word := by
  have children := capture_frame codec label operand round query apart program leg rest caller state context origins pending
    selected framed.frame valid captured
  obtain ⟨environment, prepared, actual⟩ := captured_view program leg.1 leg.2
    (ScopedNestedQueryExecution.source rest query.template.source) (.var query.names.result)
    caller state context origins pending selected captured
  cases framed with
  | frontier _ resolved fixed nextFresh priorFresh =>
      let body := ScopedNestedQueryExecution.source [query.edge, query.satisfaction] query.template.source
      let ready := ScopedMatchPreparation.ready caller (.var query.names.result) query.frontierHandle query.frontier.2 body
      have readings := fixed environment (ScopedMatchPreparation.ready_inherited caller (.var query.names.result)
        query.frontierHandle query.frontier.2 body environment (resolve_sound prepared))
      have retained := CTLUntilScopedCapture.pattern_name_retained caller (.var query.names.result)
        query.frontierHandle query.frontier.2 body query.names.next (by
          rw [Query.frontier, CTLUntilScopedCapture.frontierCode, CapturedPatternSupport.mem_expression_names]
          exact ⟨.var query.names.next, by simp, by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩)
      have fresh := ScopedMatchPreparation.retained_fresh caller (.var query.names.result)
        query.frontierHandle query.frontier.2 body query.names.next nextFresh retained
      have unbound := ClosedOnceQueryFrame.fresh_read ready.bindings query.names.next environment fresh prepared
      have reading := CTLUntilScopedCapture.frontier_pattern_read codec label round query.names.formula
        query.currentRound query.names.next environment readings.1 readings.2.2.1 unbound
      change CaptureView state.world.state query.frontierHandle ready
        (read environment query.frontier.2) body (.var query.names.result) caller.goals 0 = some selected.choices at actual
      change read environment query.frontier.2 = _ at reading
      rw [reading, stable.frontier] at actual
      obtain ⟨rendered, admitted⟩ := CTLUntilMixedStore.decode_rows_sound codec frontAtoms fronts frontDecode
      have initialCapture := CTLUntilMixedCapture.single_capture codec (frontSelect label round) _ query.names.next
        (CTLUntilMixedStore.frontier_match codec label round query.names.next) ready environment query.names.next
        body (.var query.names.result) caller.goals 0 fronts admitted prepared unbound
      simp only [CaptureView, frontRead, Option.bind_some, ← rendered, initialCapture] at actual
      have choices := (Option.some.inj actual).symm
      refine ⟨(located (frontSelect label round) 0 fronts).map (fun entry =>
        CTLUntilCandidateBag.candidates (graphView graph) (satisfactionView operand facts) [entry.2]), ?_, ?_⟩
      · rw [choices, List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
        intro entry member
        have child := children _ (by rw [choices]; exact List.mem_map.mpr ⟨entry, member, rfl⟩)
        apply edge_word fronts graph facts entry.2 child
        obtain ⟨principal, childResolved⟩ := frame_resolved child
        exact bound_of_reading _ query.names.next entry.2 principal childResolved
          (CTLUntilScopedFrame.number_capture_read caller (.var query.names.result) query.frontierHandle
            query.frontier.2 body query.names.next entry.2 principal childResolved)
      · change (located (frontSelect label round) 0 fronts).flatMap _ = _
        rw [CTLUntilSourceRows.located_flatMap (frontSelect label round) 0 fronts
          (fun next => CTLUntilCandidateBag.candidates (graphView graph) (satisfactionView operand facts) [next])]
        simp only [CTLUntilCandidateBag.candidates, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  | edge _ resolved fixed next bound priorFresh =>
      let body := ScopedNestedQueryExecution.source [query.satisfaction] query.template.source
      let ready := ScopedMatchPreparation.ready caller (.var query.names.result) query.edgeHandle query.edge.2 body
      have inherited := ScopedMatchPreparation.ready_inherited caller (.var query.names.result)
        query.edgeHandle query.edge.2 body environment (resolve_sound prepared)
      have retained := CTLUntilScopedCapture.pattern_name_retained caller (.var query.names.result)
        query.edgeHandle query.edge.2 body query.names.prior (by
          rw [Query.edge, CTLUntilSourceRows.reversePattern, CapturedPatternSupport.mem_expression_names]
          exact ⟨.var query.names.prior, by simp, by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩)
      have fresh := ScopedMatchPreparation.retained_fresh caller (.var query.names.result)
        query.edgeHandle query.edge.2 body query.names.prior priorFresh retained
      have unbound := ClosedOnceQueryFrame.fresh_read ready.bindings query.names.prior environment fresh prepared
      have reading := CTLUntilScopedCapture.edge_pattern_read query.names.next query.names.prior next environment
        (bound environment inherited) unbound
      change CaptureView state.world.state query.edgeHandle ready
        (read environment query.edge.2) body (.var query.names.result) caller.goals 0 = some selected.choices at actual
      change read environment query.edge.2 = _ at reading
      rw [reading, stable.edge] at actual
      obtain ⟨rendered, admitted⟩ := CTLUntilMixedStore.decode_rows_sound codec graphAtoms graph graphDecode
      have initialCapture := CTLUntilMixedCapture.single_capture codec (edgeSelect next) _ query.names.prior
        (CTLUntilMixedCapture.prepared_edge_match codec next query.names.prior) ready environment query.names.prior
        body (.var query.names.result) caller.goals 0 graph admitted prepared unbound
      simp only [CaptureView, graphRead, Option.bind_some, ← rendered, initialCapture] at actual
      have choices := (Option.some.inj actual).symm
      refine ⟨(located (edgeSelect next) 0 graph).map (fun entry =>
        (satisfactionView operand facts).filter (fun node => node == entry.2)), ?_, ?_⟩
      · rw [choices, List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
        intro entry member
        have child := children _ (by rw [choices]; exact List.mem_map.mpr ⟨entry, member, rfl⟩)
        apply satisfaction_word fronts graph facts entry.2 child
        obtain ⟨principal, childResolved⟩ := frame_resolved child
        exact bound_of_reading _ query.names.prior entry.2 principal childResolved
          (CTLUntilScopedFrame.number_capture_read caller (.var query.names.result) query.edgeHandle
            query.edge.2 body query.names.prior entry.2 principal childResolved)
      · change (located (edgeSelect next) 0 graph).flatMap _ = _
        rw [CTLUntilSourceRows.located_flatMap (edgeSelect next) 0 graph
          (fun prior => (satisfactionView operand facts).filter (fun node => node == prior)),
          CTLUntilMixedStore.edge_view, CTLUntilSourceRows.edge_values]
        simp [CTLUntilCandidateBag.candidates]
  | satisfaction _ resolved fixed prior bound =>
      let body := query.template.source
      let ready := ScopedMatchPreparation.ready caller (.var query.names.result) query.operandHandle query.satisfaction.2 body
      have inherited := ScopedMatchPreparation.ready_inherited caller (.var query.names.result)
        query.operandHandle query.satisfaction.2 body environment (resolve_sound prepared)
      have reading := CTLUntilScopedCapture.satisfaction_pattern_read codec operand prior query.operand query.names.prior
        environment (fixed environment inherited).2.1 (bound environment inherited)
      change CaptureView state.world.state query.operandHandle ready
        (read environment query.satisfaction.2) body (.var query.names.result) caller.goals 0 = some selected.choices at actual
      change read environment query.satisfaction.2 = _ at reading
      rw [reading, stable.operand] at actual
      obtain ⟨rendered, admitted⟩ := CTLUntilMixedStore.decode_rows_sound codec factAtoms facts factDecode
      have initialCapture := CTLUntilMixedCapture.satisfaction_capture codec operand prior ready body
        (.var query.names.result) caller.goals 0 facts admitted ⟨environment, resolve_sound prepared⟩
      simp only [CaptureView, factRead, Option.bind_some, ← rendered, initialCapture] at actual
      have choices := (Option.some.inj actual).symm
      refine ⟨(located (satSelect operand prior) 0 facts).map (fun _ => [prior]), ?_, ?_⟩
      · rw [choices, List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
        intro entry member
        have child := children _ (by rw [choices]; exact List.mem_map.mpr ⟨entry, member, rfl⟩)
        apply leaf_word fronts graph facts prior child
        exact bound.inherited (CTLUntilScopedFrame.capture_inherited caller (.var query.names.result)
          query.operandHandle query.satisfaction.2 body [])
      · change (located (satSelect operand prior) 0 facts).flatMap (fun _ => [prior]) = _
        rw [← List.map_eq_flatMap]
        simpa only using (CTLUntilSourceRows.located_map (satSelect operand prior) 0 facts (fun _ => prior)).trans
          (CTLUntilMixedStore.satisfaction_values operand prior facts)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCandidateWords

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCandidateWords.WordFrame.frame
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCandidateWords.capture_words
