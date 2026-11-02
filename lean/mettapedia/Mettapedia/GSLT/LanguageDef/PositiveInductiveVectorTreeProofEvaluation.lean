import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuestAdmission
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaborationComponents
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionSearchProjection

/-!
# Exact candidate projection for VectorTree evaluation proofs

The original normalization choice observes only a bounded candidate's term.
The certified projection computes exactly that field without constructing its
unobserved recipe. The choices records are equal at every scope, fuel and
input; all other fields, including conversion production, are retained.

This equality is used to check the original endpoint Booleans. It changes
neither the source producer nor the independent publication replay.
-/

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.ProofEvaluation

open Presentation FormationSensitiveElaboration NativeNaturalVectorFamilies

local instance : DecidableRel inventoryRules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred inventoryRules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (inventoryRules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel inventoryRules.cumulative :=
  fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))
local instance : DecidableRel inventoryRules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def choices : FormationSensitiveElaboration.Choices Tower.Head inventoryDecoder.Code :=
  { inventoryChoices with normalize := fun fuel term =>
      StructuralConversionSearch.termProjection inventoryDecoder.decode inventorySearchRoot fuel term }

theorem choices_exact : inventoryChoices = choices := by
  have normalizationExact : (@inventoryChoices.normalize) =
      (fun {n} fuel (term : Tower.Tm n) =>
        StructuralConversionSearch.termProjection inventoryDecoder.decode inventorySearchRoot fuel term) := by
    funext n fuel term
    change (match StructuralConversionSearch.normalize inventoryDecoder inventorySearchRoot
      (headEq := inventoryRules.headEq) fuel term with
      | none => term
      | some candidate => candidate.term) = _
    rw [StructuralConversionSearch.normalize_eq_some_produce]
    exact StructuralConversionSearch.produce_term inventoryDecoder.decode inventorySearchRoot fuel term
  exact congrArg (fun normalize : {n : Nat} → Nat → Tower.Tm n → Tower.Tm n =>
    {inventoryChoices with normalize := normalize}) normalizationExact

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

private theorem motiveFormation :
    formationReplayAccepted inventoryRules inventoryDecoder inventoryChoices 256
      .nil motiveType = true := by
  rw [choices_exact]
  decide +kernel

private theorem solvedFormation :
    formationReplayAccepted inventoryRules inventoryDecoder inventoryChoices 256
      contextP solvedCaseType = true := by
  rw [choices_exact]
  decide +kernel

private theorem branchFormation :
    formationReplayAccepted inventoryRules inventoryDecoder inventoryChoices 256
      contextPZ branchCaseType = true := by
  rw [choices_exact]
  decide +kernel

private theorem numberFormation :
    formationReplayAccepted inventoryRules inventoryDecoder inventoryChoices 256
      contextPZB natTm = true := by
  rw [choices_exact]
  decide +kernel

private theorem childrenFormation :
    formationReplayAccepted inventoryRules inventoryDecoder inventoryChoices 256
      branchContextN (vecApp treeTm (.var 0)) = true := by
  rw [choices_exact]
  decide +kernel

private theorem extendAccepted {n : Nat} (ambient : Tower.Ctx n) (type : Tower.Tm n)
    (prior : contextReplayAccepted inventoryRules inventoryDecoder inventoryChoices 256 ambient = true)
    (formed : formationReplayAccepted inventoryRules inventoryDecoder inventoryChoices 256 ambient type = true) :
    contextReplayAccepted inventoryRules inventoryDecoder inventoryChoices 256 (.snoc ambient type) = true :=
  (contextReplayAccepted_snoc inventoryRules inventoryDecoder inventoryChoices 256 ambient type).trans
    (congrArg₂ Bool.and prior formed)

/-- Reuse the complete original telescope check, including every assumption
unused by a particular endpoint. -/
theorem context_accepted :
    contextReplayAccepted inventoryRules inventoryDecoder inventoryChoices 256 branchContext = true := by
  have first : contextReplayAccepted inventoryRules inventoryDecoder inventoryChoices 256 contextP = true :=
    extendAccepted .nil motiveType
      (contextReplayAccepted_nil inventoryRules inventoryDecoder inventoryChoices 256) motiveFormation
  have second : contextReplayAccepted inventoryRules inventoryDecoder inventoryChoices 256 contextPZ = true :=
    extendAccepted contextP solvedCaseType first solvedFormation
  have third : contextReplayAccepted inventoryRules inventoryDecoder inventoryChoices 256 contextPZB = true :=
    extendAccepted contextPZ branchCaseType second branchFormation
  have fourth : contextReplayAccepted inventoryRules inventoryDecoder inventoryChoices 256 branchContextN = true :=
    extendAccepted contextPZB natTm third numberFormation
  exact extendAccepted branchContextN (vecApp treeTm (.var 0)) fourth childrenFormation

/-- The shared telescope has been produced and replayed above; each endpoint
still runs its own original term producer and term replay. -/
theorem branch_endpoint_eq_termReplay (term type : Tower.Tm 5) :
    endpointAccepted branchContext term type =
      termReplayAccepted inventoryRules inventoryDecoder inventoryChoices 256 branchContext term type := by
  exact (elaborate_isSome_eq_components inventoryRules inventoryDecoder inventoryChoices 256
    branchContext term type).trans
      (congrArg (fun admitted => admitted &&
        termReplayAccepted inventoryRules inventoryDecoder inventoryChoices 256 branchContext term type)
        context_accepted)

#print axioms choices_exact
#print axioms context_accepted
#print axioms branch_endpoint_eq_termReplay

end Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.ProofEvaluation
