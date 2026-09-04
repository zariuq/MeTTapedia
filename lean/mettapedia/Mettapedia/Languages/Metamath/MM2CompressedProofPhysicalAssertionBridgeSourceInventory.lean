import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoff

/-!
# Source assertion bridge inventory

This module records the exact supported executable inventory of the
source-derived assertion workspace enriched with the two normal-handoff
captures.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSourceInventory

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionSourceBoundary
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionScheduleExtension
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionSourceLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoff
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-- Supported scheduler authority in the source workspace before launch. -/
def assertionBridgeInitialDirectives : List SourceExecFact :=
  [decoratedDirectAssertionDirective, compressedProofStepDirective,
   decoratedCursorAssertionDirective, compressedHeapLookupFaultDirective,
   compressedHeapLookupAdvanceDirective]

/-- Supported scheduler authority permitted immediately after launch. -/
def assertionBridgePostLaunchDirectives : List SourceExecFact :=
  [compressedProofStepDirective, decoratedCursorAssertionDirective,
   compressedHeapLookupFaultDirective, compressedHeapLookupAdvanceDirective,
   compressedAssertionRejoinDirective,
   compressedNormalDispatchBridgeDirective]

def SupportedAtomWithin (allowed : List SourceExecFact) (atom : Atom) : Prop :=
  ∀ candidate, extractSupportedSourceExecFact atom = some candidate →
    candidate ∈ allowed

def AssertionBridgeInitialSupportedAtom (atom : Atom) : Prop :=
  SupportedAtomWithin assertionBridgeInitialDirectives atom

def AssertionBridgePostLaunchSupportedAtom (atom : Atom) : Prop :=
  SupportedAtomWithin assertionBridgePostLaunchDirectives atom

private theorem atomsWithin_initial_supported_of_no_supported
    {rows : List Atom}
    (none : cSupportedSourceExecFacts rows = []) :
    AtomsWithin (SupportedAtomWithin assertionBridgeInitialDirectives)
      rows := by
  intro atom atomMember candidate decoded
  have candidateMember : candidate ∈ cSupportedSourceExecFacts rows :=
    List.mem_filterMap.mpr ⟨atom, atomMember, decoded⟩
  have impossible : candidate ∈ ([] : List SourceExecFact) :=
    none ▸ candidateMember
  simp at impossible

private theorem canonicalDecoratedDirectAssertionSpace_initial_supported
    (context : DirectAssertionContext) :
    AtomsWithin (SupportedAtomWithin assertionBridgeInitialDirectives)
      (canonicalDecoratedDirectAssertionSpace context) := by
  intro atom atomMember candidate decoded
  have candidateMember : candidate ∈ cSupportedSourceExecFacts
      (canonicalDecoratedDirectAssertionSpace context) :=
    List.mem_filterMap.mpr ⟨atom, atomMember, decoded⟩
  rw [canonicalDecoratedDirectAssertionSpace_supported context]
    at candidateMember
  exact candidateMember

/-- Every decoded executable atom in the bridge-ready source workspace belongs
to the exact pre-launch scheduler inventory. -/
theorem sourceDecoratedAssertionBridgeReadySpace_supported_within
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) :
    AtomsWithin (SupportedAtomWithin assertionBridgeInitialDirectives)
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion) := by
  intro atom atomMember
  simp only [sourceDecoratedAssertionBridgeReadySpace,
    sourceDecoratedAssertionRequestSpace, List.mem_append] at atomMember
  rcases atomMember with (canonical | additional) | capture
  · exact canonicalDecoratedDirectAssertionSpace_initial_supported
      (@directAssertionContextAtBoundary source target context state scanner
        index cursor assertion) atom canonical
  · exact atomsWithin_initial_supported_of_no_supported
      (@sourceAssertionAdditionalRows_no_supported source target context state
        ledger scanner index assertion) atom additional
  · exact atomsWithin_initial_supported_of_no_supported
      normalHandoffBridgeCaptureRows_no_supported atom capture

/-- Physical erasure discharges one exact decoded authority from a pointwise
supported-atom invariant. -/
theorem morkEraseSupport_supportedAtom_of_selected_or
    (space : List Atom) (selected : SourceExecFact)
    (allowed : SourceExecFact → Prop)
    (within : AtomsWithin
      (fun atom => ∀ candidate,
        extractSupportedSourceExecFact atom = some candidate →
          candidate = selected ∨ allowed candidate)
      space) :
    AtomsWithin
      (fun atom => ∀ candidate,
        extractSupportedSourceExecFact atom = some candidate →
          allowed candidate)
      (morkEraseSupport space selected.atom) := by
  intro atom atomMember candidate decoded
  have sourceMember : atom ∈ space := List.mem_of_mem_filter atomMember
  rcases within atom sourceMember candidate decoded with equal | permitted
  · subst candidate
    have atomExact := extractSupportedSourceExecFact_atom decoded
    rw [← atomExact] at atomMember
    have present : morkSupportContains (morkEraseSupport space selected.atom)
        selected.atom = true :=
      morkSupportContains_eq_true_of_mem atomMember
    have absent := morkSupportContains_morkEraseSupport_self space selected.atom
    have impossible : true = false := present.symm.trans absent
    cases impossible
  · exact permitted

theorem assertionBridgeInitial_selected_or_post
    {candidate : SourceExecFact}
    (member : candidate ∈ assertionBridgeInitialDirectives) :
    candidate = decoratedDirectAssertionDirective ∨
      candidate ∈ assertionBridgePostLaunchDirectives := by
  simp only [assertionBridgeInitialDirectives, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with selected | proof | cursor | fault | advance
  · exact Or.inl selected
  · exact Or.inr (by simp [assertionBridgePostLaunchDirectives, proof])
  · exact Or.inr (by simp [assertionBridgePostLaunchDirectives, cursor])
  · exact Or.inr (by simp [assertionBridgePostLaunchDirectives, fault])
  · exact Or.inr (by simp [assertionBridgePostLaunchDirectives, advance])

/-- Physically erasing the selected launcher removes it from the supported
inventory while preserving all four older verifier shells. -/
theorem sourceAssertionBridgeLaunchLive_supported_within
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) :
    AtomsWithin
      (fun atom => ∀ candidate,
        extractSupportedSourceExecFact atom = some candidate →
          candidate ∈ assertionBridgePostLaunchDirectives)
      (morkEraseSupport
        (@sourceDecoratedAssertionBridgeReadySpace source target context state
          ledger scanner index cursor assertion)
        decoratedDirectAssertionDirective.atom) := by
  let space := @sourceDecoratedAssertionBridgeReadySpace source target context
    state ledger scanner index cursor assertion
  exact @morkEraseSupport_supportedAtom_of_selected_or space
    decoratedDirectAssertionDirective
    (fun candidate => candidate ∈ assertionBridgePostLaunchDirectives)
    (fun atom atomMember candidate decoded =>
      assertionBridgeInitial_selected_or_post
        ((@sourceDecoratedAssertionBridgeReadySpace_supported_within source
          target context state ledger scanner index cursor assertion)
          atom atomMember candidate decoded))

#print axioms sourceDecoratedAssertionBridgeReadySpace_supported_within
#print axioms morkEraseSupport_supportedAtom_of_selected_or
#print axioms sourceAssertionBridgeLaunchLive_supported_within

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSourceInventory
