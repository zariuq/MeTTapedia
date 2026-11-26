import Mettapedia.Languages.MeTTa.PeTTa.EquationEquality
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceBatchExecution
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceInstallation

/-! # Native installation of fresh allocations into retained occurrence work -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceInstallationExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL _root_.Mettapedia.OSLF.MeTTaIL.Syntax CollectionOccurrenceBatch
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit
open CollectionOccurrenceBatchExecution (frameTerm stateTerm)
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_collection_install.metta"
    sha256 "d1892fde9b7cecf4f826095d08629fb0d65892dd0e7e1cedf4261ae601f18a85"

def library : BridgeKit.Library :=
  CollectionOccurrenceSearchExecution.SelectedNativeSource.library

theorem checked : library.check = true := CollectionOccurrenceSearchExecution.SelectedNativeSource.checked

section ProofMetadata
private local instance installationEquationEq : DecidableEq SpaceSemantics.Equation :=
  SpaceSemantics.Equation.decideEq

def installationProofLibrary : Library := ⟨
  RuleExecutionProgram.callFragment ["gslt:automata:append"] RuleExecutionProgram.scopedProgram,
  source.program, ["gslt:occurrence-install:"]⟩
def installationProofHeads (head : String) : Bool := !head.startsWith "gslt:" ||
  installationProofLibrary.owns head || head == "gslt:automata:append"
theorem installationProof_checked : installationProofLibrary.check = true := by decide +kernel
theorem installationProof_agreement : ProgramAgreementOn installationProofHeads
    installationProofLibrary.runtime library.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel
#print axioms installationProof_checked
#print axioms installationProof_agreement
end ProofMetadata

private theorem append_returns {α : Type} (encoder : α → Term) (host : Effects.State)
    (left right : List α) :
    PureReturns library.runtime [] host
      (apply "gslt:automata:append"
        [encoded (encodeList encoder left), encoded (encodeList encoder right)])
      host (encoded (encodeList encoder (left ++ right))) := by
  have metadata := RetainedMatchingWire.scopedPrimitive_agreement
  apply transport_call CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_closed
    CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_agreement (by decide +kernel) (by decide)
    (by rw [← metadata.dispatch _ (by decide +kernel)]; decide +kernel) (by decide)
    ["left", "right"] (by decide) (by rfl)
    (by intro index bounded; have small : index < 2 := by simpa using bounded
        rw [← metadata.demand _ index (by decide +kernel)]; interval_cases index <;> decide +kernel)
  exact CollectionSelectionExecution.scoped_append_returns encoder host left right

/-- The existing installation body appends fresh frames and retains the complete chronological log. -/
theorem install_frames_returns {FrameData PacketData : Type}
    (encodeFrame : FrameData → Term) (encodePacket : PacketData → Term) (host : Effects.State)
    (frames fresh : List FrameData) (log : List PacketData) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-install:append"
        [encoded (encodeList encodeFrame fresh), encoded (.application "RecursiveOccurrenceBatch"
          [encodeList encodeFrame frames, encodeList encodePacket log])])
      host (encoded (.application "RecursiveOccurrenceBatch"
        [encodeList encodeFrame (frames ++ fresh), encodeList encodePacket log])) := by
  have joined := append_returns encodeFrame host frames fresh
  metta_call_in installationProof_checked using installationProof_agreement
  metta_eval [joined] with installationProof_checked in installationProof_agreement unfolding
    [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
      CettaWireAtom.encode, CettaWireAtom.encodeMany]

@[metta_head "gslt:occurrence-install:append"]
theorem install_returns (host : Effects.State) {plan : GeneralExecutionAdmission.Plan}
    {bound : List TypeExpr} {expected : TypeExpr} {sourcePattern : Pattern}
    (allocations : List (Allocation plan bound expected sourcePattern))
    (batch : State plan bound expected sourcePattern) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-install:append"
        [encoded (encodeList frameTerm (allocations.map Frame.initial)), encoded (stateTerm batch)])
      host (encoded (stateTerm (batch.install allocations))) := by
  have initial : Frame.initialWith (ordinarySeedProfile plan bound expected sourcePattern) =
      Frame.initial := by
    funext allocation
    exact Frame.initialWith_ordinary allocation
  simpa only [State.install, State.installWith, initial, stateTerm] using
    install_frames_returns frameTerm CollectionOccurrenceBatchExecution.publicationTerm host
      batch.frames (allocations.map Frame.initial) batch.log

namespace Canonical
variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {sourcePattern : Pattern}

/-- The same body preserves the original canonical histories and full packet account. -/
theorem install_returns (host : Effects.State)
    (allocations : List (Allocation plan bound expected (CanonicalBags.canon sourcePattern)))
    (batch : State plan bound expected (CanonicalBags.canon sourcePattern)
      RecursiveCollectionHandoff.canonicalMatchingExecution) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-install:append"
        [encoded (encodeList CollectionOccurrenceBatchExecution.Canonical.frameTerm (allocations.map Frame.initialCanonical)),
          encoded (CollectionOccurrenceBatchExecution.Canonical.stateTerm batch)]) host
      (encoded (CollectionOccurrenceBatchExecution.Canonical.stateTerm
        (batch.installWith (canonicalSeedProfile plan bound expected sourcePattern) allocations))) := by
  have initial : Frame.initialWith (canonicalSeedProfile plan bound expected sourcePattern) =
      Frame.initialCanonical := by
    funext allocation
    exact Frame.initialWith_canonical allocation
  simpa only [State.installWith, initial,
    CollectionOccurrenceBatchExecution.Canonical.stateTerm] using
    install_frames_returns CollectionOccurrenceBatchExecution.Canonical.frameTerm
      CollectionOccurrenceBatchExecution.Canonical.publicationTerm host batch.frames
      (allocations.map Frame.initialCanonical) batch.log
end Canonical

#print axioms append_returns
#print axioms install_frames_returns
#print axioms install_returns
#print axioms Canonical.install_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceInstallationExecution
