import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCandidateWords
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilWordUpdate

/-!
# Actual live EU rounds refine ordered fresh candidate execution

Capture-word decomposition and the single-leaf live membership law are
composed through the existing scoped traversal. Every sibling receives the
actual intermediate state. Completed refinement preserves the ordered fresh
list, not just its support or cardinality. Uniform resource-sufficient
completion and source round recursion are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundRefinement

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open NamedGuardedCandidateBatch (State)
open FlatQueryRowCodec (Codec)
open CTLUntilMixedStore (Row decodeRows graphView satisfactionView frontSelect)
open CTLUntilScopedRound
open CTLUntilRoundViews (Stable)
open CTLUntilCandidateWords (WordFrame)
open CTLUntilWordUpdate (Update)

variable {Context Label : Type} [DecidableEq Label]

theorem refines (codec : Codec Label) (label operand : Label) (distinct : label ≠ operand)
    (round : Nat) (query : Query) (apart : query.names.prior ≠ query.names.next)
    (fronts graph facts : List (Row Label)) (program : SpaceSemantics.Program) (initial : Effects.State)
    (frontAtoms graphAtoms factAtoms : List Atom)
    (frontRead : initial.read query.frontierHandle = some frontAtoms) (frontDecode : decodeRows codec frontAtoms = some fronts)
    (graphRead : initial.read query.edgeHandle = some graphAtoms) (graphDecode : decodeRows codec graphAtoms = some graph)
    (factRead : initial.read query.operandHandle = some factAtoms) (factDecode : decodeRows codec factAtoms = some facts)
    (legs : List NestedQuerySource.Leg) :
    ScopedQueryWordRefinement.Refines (WordFrame codec label operand round query fronts graph facts legs)
      (fun state : State Context => Decoded codec query.handles state ∧
        Stable codec label operand round query initial state.world.state)
      (Update codec label round query)
      (ScopedNestedQueryExecution.run program (GuardedNestedQuerySource.leaf program query.template Context) legs) := by
  apply ScopedQueryWordRefinement.run_refines program
    (GuardedNestedQuerySource.leaf program query.template Context)
    (WordFrame codec label operand round query fronts graph facts)
    (fun state : State Context => Decoded codec query.handles state ∧
      Stable codec label operand round query initial state.world.state)
    (Update codec label round query)
  · intro state valid
    exact Update.nil codec label round query state valid.1
  · intro first later before middle after early late
    exact early.append late
  · intro caller before context origins pending after word described valid completed
    have frame := described.frame
    have decoded := leaf_preserves codec label operand round query program query.handles
      caller before context origins pending after frame valid.1 completed
    have stable := CTLUntilRoundViews.leaf_stable codec label operand distinct round query program
      caller before after context origins pending frame completed
    cases described with
    | leaf _ resolved fixed node bound =>
      exact ⟨⟨decoded, valid.2.trans stable⟩,
        CTLUntilWordUpdate.leaf_update codec label operand round node query program caller before after
          context origins pending resolved fixed bound valid.1 completed⟩
  · intro leg rest caller state context origins pending word selected described valid captured
    exact CTLUntilCandidateWords.capture_words codec label operand round query fronts graph facts apart program initial
      frontAtoms graphAtoms factAtoms frontRead frontDecode graphRead graphDecode factRead factDecode
      leg rest caller state context origins pending word selected described valid.1 valid.2 captured

/-- The candidate word is computed from the initial decoded graph views.
The source itself continues to use live worlds and actual prepared callers. -/
theorem completed_word (codec : Codec Label) (label operand : Label) (distinct : label ≠ operand)
    (round : Nat) (query : Query) (apart : query.names.prior ≠ query.names.next)
    (fronts graph facts : List (Row Label)) (program : SpaceSemantics.Program)
    (caller : Control) (before after : State Context) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) (resolved : Resolved caller)
    (fixed : Fixed codec label operand round query caller)
    (nextFresh : ClosedOnceQueryFrame.FreshFor query.names.next caller.bindings)
    (priorFresh : ClosedOnceQueryFrame.FreshFor query.names.prior caller.bindings)
    (valid : Decoded codec query.handles before) (frontAtoms graphAtoms factAtoms : List Atom)
    (frontRead : before.world.state.read query.frontierHandle = some frontAtoms) (frontDecode : decodeRows codec frontAtoms = some fronts)
    (graphRead : before.world.state.read query.edgeHandle = some graphAtoms) (graphDecode : decodeRows codec graphAtoms = some graph)
    (factRead : before.world.state.read query.operandHandle = some factAtoms) (factDecode : decodeRows codec factAtoms = some facts)
    (completed : (ScopedNestedQueryExecution.run program (GuardedNestedQuerySource.leaf program query.template Context)
      query.legs caller before context origins pending).stop = .complete after) :
    (Decoded codec query.handles after ∧ Stable codec label operand round query before.world.state after.world.state) ∧
      Update codec label round query
        (Mettapedia.Machines.CTLUntilCandidateBag.candidates (graphView graph) (satisfactionView operand facts)
          (fronts.filterMap (frontSelect label round))) before after := by
  exact refines codec label operand distinct round query apart fronts graph facts program before.world.state
    frontAtoms graphAtoms factAtoms frontRead frontDecode graphRead graphDecode factRead factDecode query.legs
    caller before context origins pending after _
    (WordFrame.frontier caller resolved fixed nextFresh priorFresh)
    ⟨valid, Stable.refl codec label operand round query before.world.state⟩ completed

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundRefinement
