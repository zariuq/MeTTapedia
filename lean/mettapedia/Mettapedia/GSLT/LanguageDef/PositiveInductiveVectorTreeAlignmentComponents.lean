import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveAlignmentCheckpoints
import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeProducerChecks
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaborationCheckpoints
/-!
# Actual Vector-tree alignment gates

The bounded normalization and non-reflexive alignment retain original target
formation, universe and cumulative policies, and conversion-code validation.
The endpoint acceptance of the complete branch bundle is a separate obligation.
-/

set_option autoImplicit false
set_option Elab.async false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest
open Presentation ProducerEvidence
namespace Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.BranchAlignmentComponents
local instance : DecidableRel inventoryRules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred inventoryRules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (inventoryRules.join u v w) :=
  fun h u v => inferInstanceAs (Decidable (Tower.rules.join h u v))
local instance : DecidableRel inventoryRules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel inventoryRules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def viewType2 : Tower.Tm 5 :=
  (.pi (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero)) (.pi (.pi (.const `CumulativeTower.Nat) (.pi (.const `Generated.VectorTree) (.pi (.app (.app (.const `CumulativeTower.Vec) (.const `Generated.VectorTree)) (.var 1)) (.pi (.app (.app (.app (.app (.app (.app (.const `CumulativeTower.Vec.eliminate) (.const `Generated.VectorTree)) (.lam (.lam (.head (.sort (.param 0)))))) (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero))) (.lam (.lam (.lam (.lam (.sigma (.app (.var 12) (.var 2)) (.var 1))))))) (.var 2)) (.var 0)) (.sigma (.app (.var 9) (.var 2)) (.app (.app (.app (.app (.app (.app (.const `CumulativeTower.Vec.eliminate) (.const `Generated.VectorTree)) (.lam (.lam (.head (.sort (.param 0)))))) (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero))) (.lam (.lam (.lam (.lam (.sigma (.app (.var 14) (.var 2)) (.var 1))))))) (.var 4)) (.var 2))))))) (.pi (.const `CumulativeTower.Nat) (.pi (.app (.app (.const `CumulativeTower.Vec) (.const `Generated.VectorTree)) (.var 0)) (.app (.app (.app (.app (.app (.app (.const `CumulativeTower.Vec.eliminate) (.const `Generated.VectorTree)) (.lam (.lam (.head (.sort (.param 0)))))) (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero))) (.lam (.lam (.lam (.lam (.sigma (.app (.var 12) (.var 2)) (.var 1))))))) (.var 1)) (.var 0))))))

def thirdDomain : Tower.Tm 5 :=
  match viewType2 with | .pi domain _ => domain | _ => .head .legacyGround
def thirdBody : Tower.Tm 6 :=
  match viewType2 with | .pi _ body => body | _ => .head .legacyGround
theorem view2_shape : viewType2 = .pi thirdDomain thirdBody := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem third_normalization : inventoryChoices.normalize 251 candidateType2 = viewType2 := by
  rw [evaluationChoices_exact]
  decide +kernel

private theorem conversion_observation (fuel : Nat) {n : Nat} (source target : Tower.Tm n) :
    FormationSensitiveElaboration.conversionReplayAccepted inventoryRules inventoryDecoder
      inventoryChoices fuel source target =
      (inventoryChoices.conversion fuel source target).isSome := by
  have checked (recipe : StructuralConversionCode.Code Tower.Head inventoryDecoder.Code n)
      (produced : inventoryChoices.conversion fuel source target = some recipe) :
      recipe.check inventoryRules.headEq inventoryDecoder.decode source target = true := by
    change StructuralConversionSearch.compare inventoryDecoder inventorySearchRoot
      (headEq := inventoryRules.headEq) fuel source target = some recipe at produced
    dsimp only [StructuralConversionSearch.compare] at produced
    cases matched : StructuralConversionSearch.compareShape (RootCode := inventoryDecoder.Code)
        (StructuralConversionSearch.produce inventoryDecoder.decode inventorySearchRoot fuel source).term
        (StructuralConversionSearch.produce inventoryDecoder.decode inventorySearchRoot fuel target).term with
    | none => simp [matched] at produced
    | some middle =>
      simp only [matched,Option.bind_eq_bind,Option.bind_some] at produced
      split at produced
      · rename_i accepted
        cases Option.some.inj produced
        exact accepted
      · cases produced
  unfold FormationSensitiveElaboration.conversionReplayAccepted
  cases produced : inventoryChoices.conversion fuel source target with
  | none => rfl
  | some recipe => exact checked recipe produced

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem third_guard : FormationSensitiveElaboration.alignReplayGuard inventoryRules inventoryDecoder
    inventoryChoices 251 branchContext candidateType2 viewType2 = true := by
  unfold FormationSensitiveElaboration.alignReplayGuard
  dsimp only
  rw [conversion_observation]
  rw [evaluationChoices_exact]
  decide +kernel

set_option maxHeartbeats 3000000 in
theorem term_target_refused : FormationSensitiveElaboration.alignReplayGuard inventoryRules inventoryDecoder
    inventoryChoices 251 branchContext candidateType2 (.var 0) = false := by
  decide +kernel

#print axioms third_normalization
#print axioms third_guard
#print axioms term_target_refused
end Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.BranchAlignmentComponents
