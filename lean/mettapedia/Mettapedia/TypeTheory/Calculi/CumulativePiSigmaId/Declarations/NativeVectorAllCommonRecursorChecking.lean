import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveConversionReplay
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllCommonRecursorEvidence
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllUniverseMaps

/-!
# Checked projections and evidence maps in the common recursor profile

Finite evidence is replayed against the two requested projection programs and
against their actual types. Both existing evidence-universe maps include into
this same profile. These component typings do not assert that projection
commutes with an evidence-universe map.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllCommonRecursorProfile
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Declaration
open NativeVectorAll.ResultView

namespace Projection

local instance : DecidableRel rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel rules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def lowerReplayed : Bool := FormationSensitiveElaboration.replay rules decoder .nil
  (programme resultContainerLevel) (programmeType resultContainerLevel) Evidence.lowerSubmission

def upperReplayed : Bool := FormationSensitiveElaboration.replay rules decoder .nil
  (programme evidenceUpperLevel) (programmeType evidenceUpperLevel) Evidence.upperSubmission

set_option maxRecDepth 8192 in
theorem lower_replayed : lowerReplayed = true := by
  rw [lowerReplayed, ← FormationSensitiveElaboration.replayWithSyntaxConversions_eq]
  decide +kernel

set_option maxRecDepth 8192 in
theorem upper_replayed : upperReplayed = true := by
  rw [upperReplayed, ← FormationSensitiveElaboration.replayWithSyntaxConversions_eq]
  decide +kernel

theorem lower_typed : FormationSensitive.Judgment rules .nil
    OriginalInputUniverses.program OriginalInputUniverses.programType := by
  have typed := FormationSensitiveElaboration.replay_sound rules decoder lower_replayed
  rw [lower_programme_readback, lower_type_readback] at typed
  exact typed

theorem upper_typed : FormationSensitive.Judgment rules .nil
    (programme evidenceUpperLevel) (programmeType evidenceUpperLevel) :=
  FormationSensitiveElaboration.replay_sound rules decoder upper_replayed

namespace Controls

set_option maxRecDepth 8192 in
/-- A certificate for the upper-evidence program cannot certify the lower request. -/
theorem exchanged_submission_refused : FormationSensitiveElaboration.replay rules decoder .nil
    (programme resultContainerLevel) (programmeType resultContainerLevel)
    Evidence.upperSubmission = false := by decide +kernel

end Controls
end Projection

/-- The two evidence maps and the projection programs use one actual signature. -/
theorem forward_formed : FormationSensitive.Judgment rules NativeVectorAll.Universes.context
    NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.forward
    NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.forwardType :=
  NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.forward_formed.monoSignature
    (Signature.merge_left lower output)

theorem backward_formed : FormationSensitive.Judgment rules NativeVectorAll.Universes.context
    NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.backward
    NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.backwardType :=
  NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.backward_formed.monoSignature
    (Signature.merge_left lower output)

#print axioms Projection.lower_typed
#print axioms Projection.upper_typed
#print axioms Projection.Controls.exchanged_submission_refused
#print axioms forward_formed
#print axioms backward_formed

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllCommonRecursorProfile
