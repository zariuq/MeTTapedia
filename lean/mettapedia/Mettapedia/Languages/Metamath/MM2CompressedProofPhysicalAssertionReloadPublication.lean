import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionPendingOrigin
import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgePredecessorOrigin
import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalDecoratedAssertionLaunch
import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionReloadBinding

/-!
# Source-exact reload publication for compressed assertions

The physical assertion launcher may enumerate more than one compatible match
in an extended source workspace.  Every such match nevertheless replays the
unique source-derived pending row.  Consequently every instantiated reload
sink carries the exact proof owner fixed by the source boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionReloadPublication

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgePredecessorOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionPredecessorOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionSourceBoundary
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionPendingOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionSourceLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalDecoratedAssertionLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionReloadBinding
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoff
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK

/-- A pending-factor origin in the physical read space remains an origin in
the original workspace.  This is the representation boundary paired with
`decoratedAssertionMorkMatcher_pending_replay_origin`; keeping the two generic
steps separate avoids re-elaborating the complete authored matcher. -/
theorem pendingReplayOrigin_from_physicalRead
    (space : List Atom)
    (directivePresent : decoratedDirectAssertionDirective.atom ∈ space)
    {substitution : Subst}
    (origin : ∃ carrier ∈
      (morkInsertSupport
        (morkEraseSupport space decoratedDirectAssertionDirective.atom)
        decoratedDirectAssertionDirective.atom),
      applySubst substitution directAssertionPendingTemplate = carrier) :
    ∃ carrier ∈ space,
      applySubst substitution directAssertionPendingTemplate = carrier := by
  obtain ⟨carrier, carrierMember, replay⟩ := origin
  have carrierInSpace : carrier ∈ space := by
    rcases mem_morkInsertSupport_cases carrierMember with live | equal
    · exact (List.mem_filter.mp live).1
    · exact equal.symm ▸ directivePresent
  exact ⟨carrier, carrierInSpace, replay⟩

/-- Every row retained by the physical assertion matcher replays the pending
factor from a concrete row in the original workspace. -/
theorem physicalMatcherRow_pending_replay_origin
    (space : List Atom)
    (directivePresent : decoratedDirectAssertionDirective.atom ∈ space)
    {substitution : Subst}
    (rowMember : substitution ∈ physicalDecoratedAssertionMatcherRows space) :
    ∃ carrier ∈ space,
      applySubst substitution directAssertionPendingTemplate = carrier := by
  unfold physicalDecoratedAssertionMatcherRows at rowMember
  rw [List.mem_map] at rowMember
  obtain ⟨⟨matchedSubstitution, witnesses⟩, filtered, equal⟩ := rowMember
  have readOrigin := decoratedAssertionMorkMatcher_pending_replay_origin
    (morkInsertSupport
      (morkEraseSupport space decoratedDirectAssertionDirective.atom)
      decoratedDirectAssertionDirective.atom)
    (List.mem_filter.mp filtered).1
  have sourceOrigin := pendingReplayOrigin_from_physicalRead space
    directivePresent readOrigin
  exact equal ▸ sourceOrigin

/-- A predecessor-origin invariant turns physical matcher provenance into the
exact pending row for one assertion context. -/
theorem physicalMatcherRow_pending_exact
    (context : DirectAssertionContext) (space : List Atom)
    (directivePresent : decoratedDirectAssertionDirective.atom ∈ space)
    (predecessorOrigin :
      AtomsWithin (AssertionPredecessorRowOrigin context) space)
    {substitution : Subst}
    (rowMember : substitution ∈ physicalDecoratedAssertionMatcherRows space) :
    applySubst substitution directAssertionPendingTemplate =
      context.pendingRow := by
  obtain ⟨carrier, carrierMember, replay⟩ :=
    physicalMatcherRow_pending_replay_origin space directivePresent rowMember
  have carrierHead : compressedDynamicRowHead? carrier =
      some "mm-compressed-step-pending" := by
    rw [← replay, directAssertionPendingTemplate,
      applySubst_expression_symbol]
    rfl
  exact replay.trans ((predecessorOrigin carrier carrierMember).1 carrierHead)

/-- Every reload instantiated from a physical matcher row is the reload row
fixed by the source predecessor invariant. -/
theorem physicalMatcherRow_reload_exact
    (context : DirectAssertionContext) (space : List Atom)
    (directivePresent : decoratedDirectAssertionDirective.atom ∈ space)
    (predecessorOrigin :
      AtomsWithin (AssertionPredecessorRowOrigin context) space)
    {substitution : Subst} {reload : Atom}
    (rowMember : substitution ∈ physicalDecoratedAssertionMatcherRows space)
    (instantiates : instantiateRuleTemplateAtom?
      decoratedDirectAssertionDirective.rule.input substitution
        directAssertionReloadTemplate = some reload) :
    reload = context.reloadRow := by
  exact reload_exact_of_pending_replay context substitution reload
    (physicalMatcherRow_pending_exact context space directivePresent
      predecessorOrigin rowMember)
    instantiates

/-- On the complete source-derived assertion workspace, the physical matcher
can publish only the reload row selected by the scanner and source heap. -/
theorem sourcePhysicalMatcherRow_reload_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion)
    {substitution : Subst} {reload : Atom}
    (rowMember : substitution ∈ physicalDecoratedAssertionMatcherRows
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion))
    (instantiates : instantiateRuleTemplateAtom?
      decoratedDirectAssertionDirective.rule.input substitution
        directAssertionReloadTemplate = some reload) :
    reload =
      (directAssertionContextAtBoundary context state scanner index cursor
        assertion).reloadRow := by
  let space := @sourceDecoratedAssertionBridgeReadySpace source target context
    state ledger scanner index cursor assertion
  have directivePresent : decoratedDirectAssertionDirective.atom ∈ space := by
    simp [space, sourceDecoratedAssertionBridgeReadySpace,
      sourceDecoratedAssertionRequestSpace,
      canonicalDecoratedDirectAssertionSpace,
      decoratedDirectAssertionMatchSlice]
  exact physicalMatcherRow_reload_exact
    (directAssertionContextAtBoundary context state scanner index cursor
      assertion)
    space directivePresent
    (sourceDecoratedAssertionBridgeReadySpace_predecessor_origin context state
      ledger scanner index cursor assertion)
    rowMember instantiates

/-- A retained physical matcher row cannot instantiate a reload carrying a
different source owner or assertion context. -/
theorem sourcePhysicalMatcherRow_rejects_other_reload
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion)
    {substitution : Subst} {reload : Atom}
    (rowMember : substitution ∈ physicalDecoratedAssertionMatcherRows
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion))
    (different : reload ≠
      (directAssertionContextAtBoundary context state scanner index cursor
        assertion).reloadRow) :
    instantiateRuleTemplateAtom?
      decoratedDirectAssertionDirective.rule.input substitution
        directAssertionReloadTemplate ≠ some reload := by
  intro instantiates
  exact different (sourcePhysicalMatcherRow_reload_exact context state ledger
    scanner index cursor assertion rowMember instantiates)

#print axioms pendingReplayOrigin_from_physicalRead
#print axioms physicalMatcherRow_pending_replay_origin
#print axioms physicalMatcherRow_pending_exact
#print axioms physicalMatcherRow_reload_exact
#print axioms sourcePhysicalMatcherRow_reload_exact
#print axioms sourcePhysicalMatcherRow_rejects_other_reload

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionReloadPublication
