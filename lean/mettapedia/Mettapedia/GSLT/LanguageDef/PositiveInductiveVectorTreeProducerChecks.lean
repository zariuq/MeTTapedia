import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaborationProjection
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaborationCheckpoints
import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeProofEvaluation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionSearchComparison

/-!
# Original VectorTree bundle production checkpoints

Each application prefix retains the original source term, telescope, choices
and recursive fuel. The displayed type data is justified by an exact checked
projection equation. The final result proves success of the original code
producer at fuel 256. Publication still requires replay of that original
produced code against the original requested type.
-/

set_option autoImplicit false
set_option Elab.async false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest
open Presentation
namespace Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.ProducerEvidence
local instance : DecidableRel inventoryRules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

private def comparison {n : Nat} (fuel : Nat) (left right : Tower.Tm n) :
    Option (StructuralConversionCode.Code Tower.Head inventoryDecoder.Code n) := do
  let first := StructuralConversionSearch.termProjection inventoryDecoder.decode inventorySearchRoot fuel left
  let second := StructuralConversionSearch.termProjection inventoryDecoder.decode inventorySearchRoot fuel right
  let middle ← StructuralConversionSearch.compareShape first second
  let recipe := StructuralConversionCode.Code.trans
    (StructuralConversionSearch.produce inventoryDecoder.decode inventorySearchRoot fuel left).recipe
    (.trans middle (.symm
      (StructuralConversionSearch.produce inventoryDecoder.decode inventorySearchRoot fuel right).recipe))
  if middle.check inventoryRules.headEq inventoryDecoder.decode first second then some recipe else none

private def choices : FormationSensitiveElaboration.Choices Tower.Head inventoryDecoder.Code :=
  {ProofEvaluation.choices with conversion := comparison}

private theorem choices_exact : inventoryChoices = choices := by
  apply ProofEvaluation.choices_exact.trans
  have conversionExact : (@ProofEvaluation.choices.conversion) = (@comparison) := by
    funext n fuel left right
    change StructuralConversionSearch.compare inventoryDecoder inventorySearchRoot
      (headEq := inventoryRules.headEq) fuel left right = _
    exact StructuralConversionSearch.compare_eq_projected_middle_check inventoryRules.headEq
      inventoryDecoder inventorySearchRoot fuel left right
  exact congrArg
    (fun conversion : {n : Nat} → Nat → Tower.Tm n → Tower.Tm n →
        Option (StructuralConversionCode.Code Tower.Head inventoryDecoder.Code n) =>
      {ProofEvaluation.choices with conversion := conversion}) conversionExact

#print axioms choices_exact
end Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.ProducerEvidence

namespace Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.ProducerEvidence
open NativeNaturalVectorFamilies
def arguments : List (Tower.Tm 5) :=
  [treeTm, NativeVectorAll.allEvidenceMotive treeTm (.var 4), NativeVectorAll.unitEvidence,
    NativeVectorAll.allEvidenceConsCase (recursiveWitness (.var 4) (.var 3) (.var 2)), .var 1, .var 0]
def applicationPrefix : Nat → Tower.Tm 5
  | 0 => .const vecEliminateName
  | i+1 => .app (applicationPrefix i) (arguments[i]?.getD (.var 0))
theorem original_term : applicationPrefix 6 = branchBundle := rfl

def candidateType0 : Tower.Tm 5 :=
  (.pi (.head (.sort (.param 0))) (.pi (.pi (.const `CumulativeTower.Nat) (.pi (.app (.app (.const `CumulativeTower.Vec) (.var 1)) (.var 0)) (.head (.sort (.succ (.param 0)))))) (.pi (.app (.app (.var 0) (.const `CumulativeTower.Nat.zero)) (.app (.const `CumulativeTower.Vec.nil) (.var 1))) (.pi (.pi (.const `CumulativeTower.Nat) (.pi (.var 3) (.pi (.app (.app (.const `CumulativeTower.Vec) (.var 4)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 0)) (.app (.app (.var 5) (.app (.const `CumulativeTower.Nat.succ) (.var 3))) (.app (.app (.app (.app (.const `CumulativeTower.Vec.cons) (.var 6)) (.var 3)) (.var 2)) (.var 1))))))) (.pi (.const `CumulativeTower.Nat) (.pi (.app (.app (.const `CumulativeTower.Vec) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0))))))))

def candidateType1 : Tower.Tm 5 :=
  (.pi (.pi (.const `CumulativeTower.Nat) (.pi (.app (.app (.const `CumulativeTower.Vec) (.const `Generated.VectorTree)) (.var 0)) (.head (.sort (.succ (.param 0)))))) (.pi (.app (.app (.var 0) (.const `CumulativeTower.Nat.zero)) (.app (.const `CumulativeTower.Vec.nil) (.const `Generated.VectorTree))) (.pi (.pi (.const `CumulativeTower.Nat) (.pi (.const `Generated.VectorTree) (.pi (.app (.app (.const `CumulativeTower.Vec) (.const `Generated.VectorTree)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 0)) (.app (.app (.var 5) (.app (.const `CumulativeTower.Nat.succ) (.var 3))) (.app (.app (.app (.app (.const `CumulativeTower.Vec.cons) (.const `Generated.VectorTree)) (.var 3)) (.var 2)) (.var 1))))))) (.pi (.const `CumulativeTower.Nat) (.pi (.app (.app (.const `CumulativeTower.Vec) (.const `Generated.VectorTree)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))

def candidateType2 : Tower.Tm 5 :=
  (.pi (.app (.app (.lam (.lam (.app (.app (.app (.app (.app (.app (.const `CumulativeTower.Vec.eliminate) (.const `Generated.VectorTree)) (.lam (.lam (.head (.sort (.param 0)))))) (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero))) (.lam (.lam (.lam (.lam (.sigma (.app (.var 10) (.var 2)) (.var 1))))))) (.var 1)) (.var 0)))) (.const `CumulativeTower.Nat.zero)) (.app (.const `CumulativeTower.Vec.nil) (.const `Generated.VectorTree))) (.pi (.pi (.const `CumulativeTower.Nat) (.pi (.const `Generated.VectorTree) (.pi (.app (.app (.const `CumulativeTower.Vec) (.const `Generated.VectorTree)) (.var 1)) (.pi (.app (.app (.lam (.lam (.app (.app (.app (.app (.app (.app (.const `CumulativeTower.Vec.eliminate) (.const `Generated.VectorTree)) (.lam (.lam (.head (.sort (.param 0)))))) (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero))) (.lam (.lam (.lam (.lam (.sigma (.app (.var 14) (.var 2)) (.var 1))))))) (.var 1)) (.var 0)))) (.var 2)) (.var 0)) (.app (.app (.lam (.lam (.app (.app (.app (.app (.app (.app (.const `CumulativeTower.Vec.eliminate) (.const `Generated.VectorTree)) (.lam (.lam (.head (.sort (.param 0)))))) (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero))) (.lam (.lam (.lam (.lam (.sigma (.app (.var 15) (.var 2)) (.var 1))))))) (.var 1)) (.var 0)))) (.app (.const `CumulativeTower.Nat.succ) (.var 3))) (.app (.app (.app (.app (.const `CumulativeTower.Vec.cons) (.const `Generated.VectorTree)) (.var 3)) (.var 2)) (.var 1))))))) (.pi (.const `CumulativeTower.Nat) (.pi (.app (.app (.const `CumulativeTower.Vec) (.const `Generated.VectorTree)) (.var 0)) (.app (.app (.lam (.lam (.app (.app (.app (.app (.app (.app (.const `CumulativeTower.Vec.eliminate) (.const `Generated.VectorTree)) (.lam (.lam (.head (.sort (.param 0)))))) (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero))) (.lam (.lam (.lam (.lam (.sigma (.app (.var 14) (.var 2)) (.var 1))))))) (.var 1)) (.var 0)))) (.var 1)) (.var 0))))))

def candidateType3 : Tower.Tm 5 :=
  (.pi (.pi (.const `CumulativeTower.Nat) (.pi (.const `Generated.VectorTree) (.pi (.app (.app (.const `CumulativeTower.Vec) (.const `Generated.VectorTree)) (.var 1)) (.pi (.app (.app (.app (.app (.app (.app (.const `CumulativeTower.Vec.eliminate) (.const `Generated.VectorTree)) (.lam (.lam (.head (.sort (.param 0)))))) (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero))) (.lam (.lam (.lam (.lam (.sigma (.app (.var 11) (.var 2)) (.var 1))))))) (.var 2)) (.var 0)) (.sigma (.app (.var 8) (.var 2)) (.app (.app (.app (.app (.app (.app (.const `CumulativeTower.Vec.eliminate) (.const `Generated.VectorTree)) (.lam (.lam (.head (.sort (.param 0)))))) (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero))) (.lam (.lam (.lam (.lam (.sigma (.app (.var 13) (.var 2)) (.var 1))))))) (.var 4)) (.var 2))))))) (.pi (.const `CumulativeTower.Nat) (.pi (.app (.app (.const `CumulativeTower.Vec) (.const `Generated.VectorTree)) (.var 0)) (.app (.app (.app (.app (.app (.app (.const `CumulativeTower.Vec.eliminate) (.const `Generated.VectorTree)) (.lam (.lam (.head (.sort (.param 0)))))) (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero))) (.lam (.lam (.lam (.lam (.sigma (.app (.var 11) (.var 2)) (.var 1))))))) (.var 1)) (.var 0)))))

def candidateType4 : Tower.Tm 5 :=
  (.pi (.const `CumulativeTower.Nat) (.pi (.app (.app (.const `CumulativeTower.Vec) (.const `Generated.VectorTree)) (.var 0)) (.app (.app (.app (.app (.app (.app (.const `CumulativeTower.Vec.eliminate) (.const `Generated.VectorTree)) (.lam (.lam (.head (.sort (.param 0)))))) (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero))) (.lam (.lam (.lam (.lam (.sigma (.app (.var 10) (.var 2)) (.var 1))))))) (.var 1)) (.var 0))))

def candidateType5 : Tower.Tm 5 :=
  (.pi (.app (.app (.const `CumulativeTower.Vec) (.const `Generated.VectorTree)) (.var 1)) (.app (.app (.app (.app (.app (.app (.const `CumulativeTower.Vec.eliminate) (.const `Generated.VectorTree)) (.lam (.lam (.head (.sort (.param 0)))))) (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero))) (.lam (.lam (.lam (.lam (.sigma (.app (.var 9) (.var 2)) (.var 1))))))) (.var 2)) (.var 0)))

def candidateType6 : Tower.Tm 5 :=
  (.app (.app (.app (.app (.app (.app (.const `CumulativeTower.Vec.eliminate) (.const `Generated.VectorTree)) (.lam (.lam (.head (.sort (.param 0)))))) (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero))) (.lam (.lam (.lam (.lam (.sigma (.app (.var 8) (.var 2)) (.var 1))))))) (.var 1)) (.var 0))


local instance : DecidableRel inventoryRules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))
private def applicationSearch {n : Nat} (term : Tower.Tm n) : Option (inventoryDecoder.Code n) :=
  match term with
  | .app _ _ => inventorySearchRoot term
  | _ => none
private theorem applicationSearch_exact : @inventorySearchRoot = @applicationSearch := by
  funext n term
  cases term <;> rfl
private def choicesAt (search : {n : Nat} → Tower.Tm n → Option (inventoryDecoder.Code n)) :
    FormationSensitiveElaboration.Choices Tower.Head inventoryDecoder.Code :=
  { inventoryChoices with
    normalize := fun fuel term => StructuralConversionSearch.termProjection inventoryDecoder.decode search fuel term
    conversion := fun fuel left right => do
      let first := StructuralConversionSearch.termProjection inventoryDecoder.decode search fuel left
      let second := StructuralConversionSearch.termProjection inventoryDecoder.decode search fuel right
      let middle ← StructuralConversionSearch.compareShape first second
      let recipe := StructuralConversionCode.Code.trans
        (StructuralConversionSearch.produce inventoryDecoder.decode search fuel left).recipe
        (.trans middle (.symm (StructuralConversionSearch.produce inventoryDecoder.decode search fuel right).recipe))
      if middle.check inventoryRules.headEq inventoryDecoder.decode first second then some recipe else none }
private theorem filteredChoices_exact : inventoryChoices = choicesAt applicationSearch := by
  have original : inventoryChoices = choicesAt inventorySearchRoot := choices_exact
  exact original.trans (congrArg choicesAt applicationSearch_exact)

/-- The complete evaluation choices are equal to the original choices as
functions, including the complete returned conversion recipes. -/
def evaluationChoices : FormationSensitiveElaboration.Choices Tower.Head inventoryDecoder.Code :=
  choicesAt applicationSearch

theorem evaluationChoices_exact : inventoryChoices = evaluationChoices := filteredChoices_exact
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

theorem checkedPrefix0 :
    FormationSensitiveElaboration.typeProjection inventoryRules inventoryChoices
      249 branchContext (applicationPrefix 0) = some candidateType0 := by
  rw [filteredChoices_exact]
  decide +kernel

#print axioms checkedPrefix0

theorem checkedPrefix1 :
    FormationSensitiveElaboration.typeProjection inventoryRules inventoryChoices
      250 branchContext (applicationPrefix 1) = some candidateType1 := by
  change FormationSensitiveElaboration.typeProjection inventoryRules inventoryChoices
    250 branchContext (.app (.const vecEliminateName) treeTm) = some candidateType1
  rw [FormationSensitiveElaboration.typeProjection.eq_def]
  dsimp only
  have prior := checkedPrefix0
  change FormationSensitiveElaboration.typeProjection inventoryRules inventoryChoices
    249 branchContext (.const vecEliminateName) = some candidateType0 at prior
  rw [prior, filteredChoices_exact]
  decide +kernel

#print axioms checkedPrefix1

theorem checkedPrefix2 :
    FormationSensitiveElaboration.typeProjection inventoryRules inventoryChoices
      251 branchContext (applicationPrefix 2) = some candidateType2 := by
  change FormationSensitiveElaboration.typeProjection inventoryRules inventoryChoices
    251 branchContext (.app (.app (.const vecEliminateName) treeTm) (NativeVectorAll.allEvidenceMotive treeTm (.var 4))) = some candidateType2
  rw [FormationSensitiveElaboration.typeProjection.eq_def]
  dsimp only
  have prior := checkedPrefix1
  change FormationSensitiveElaboration.typeProjection inventoryRules inventoryChoices
    250 branchContext (.app (.const vecEliminateName) treeTm) = some candidateType1 at prior
  rw [prior, filteredChoices_exact]
  decide +kernel

#print axioms checkedPrefix2

theorem checkedPrefix3 :
    FormationSensitiveElaboration.typeProjection inventoryRules inventoryChoices
      252 branchContext (applicationPrefix 3) = some candidateType3 := by
  change FormationSensitiveElaboration.typeProjection inventoryRules inventoryChoices
    252 branchContext (.app (.app (.app (.const vecEliminateName) treeTm) (NativeVectorAll.allEvidenceMotive treeTm (.var 4))) NativeVectorAll.unitEvidence) = some candidateType3
  rw [FormationSensitiveElaboration.typeProjection.eq_def]
  dsimp only
  have prior := checkedPrefix2
  change FormationSensitiveElaboration.typeProjection inventoryRules inventoryChoices
    251 branchContext (.app (.app (.const vecEliminateName) treeTm) (NativeVectorAll.allEvidenceMotive treeTm (.var 4))) = some candidateType2 at prior
  rw [prior, filteredChoices_exact]
  decide +kernel

#print axioms checkedPrefix3

theorem checkedPrefix4 :
    FormationSensitiveElaboration.typeProjection inventoryRules inventoryChoices
      253 branchContext (applicationPrefix 4) = some candidateType4 := by
  change FormationSensitiveElaboration.typeProjection inventoryRules inventoryChoices
    253 branchContext (.app (.app (.app (.app (.const vecEliminateName) treeTm) (NativeVectorAll.allEvidenceMotive treeTm (.var 4))) NativeVectorAll.unitEvidence) (NativeVectorAll.allEvidenceConsCase (recursiveWitness (.var 4) (.var 3) (.var 2)))) = some candidateType4
  rw [FormationSensitiveElaboration.typeProjection.eq_def]
  dsimp only
  have prior := checkedPrefix3
  change FormationSensitiveElaboration.typeProjection inventoryRules inventoryChoices
    252 branchContext (.app (.app (.app (.const vecEliminateName) treeTm) (NativeVectorAll.allEvidenceMotive treeTm (.var 4))) NativeVectorAll.unitEvidence) = some candidateType3 at prior
  rw [prior, filteredChoices_exact]
  decide +kernel

#print axioms checkedPrefix4

theorem checkedPrefix5 :
    FormationSensitiveElaboration.typeProjection inventoryRules inventoryChoices
      254 branchContext (applicationPrefix 5) = some candidateType5 := by
  change FormationSensitiveElaboration.typeProjection inventoryRules inventoryChoices
    254 branchContext (.app (.app (.app (.app (.app (.const vecEliminateName) treeTm) (NativeVectorAll.allEvidenceMotive treeTm (.var 4))) NativeVectorAll.unitEvidence) (NativeVectorAll.allEvidenceConsCase (recursiveWitness (.var 4) (.var 3) (.var 2)))) (.var 1)) = some candidateType5
  rw [FormationSensitiveElaboration.typeProjection.eq_def]
  dsimp only
  have prior := checkedPrefix4
  change FormationSensitiveElaboration.typeProjection inventoryRules inventoryChoices
    253 branchContext (.app (.app (.app (.app (.const vecEliminateName) treeTm) (NativeVectorAll.allEvidenceMotive treeTm (.var 4))) NativeVectorAll.unitEvidence) (NativeVectorAll.allEvidenceConsCase (recursiveWitness (.var 4) (.var 3) (.var 2)))) = some candidateType4 at prior
  rw [prior, filteredChoices_exact]
  decide +kernel

#print axioms checkedPrefix5

theorem checkedPrefix6 :
    FormationSensitiveElaboration.typeProjection inventoryRules inventoryChoices
      255 branchContext (applicationPrefix 6) = some candidateType6 := by
  change FormationSensitiveElaboration.typeProjection inventoryRules inventoryChoices
    255 branchContext (.app (.app (.app (.app (.app (.app (.const vecEliminateName) treeTm) (NativeVectorAll.allEvidenceMotive treeTm (.var 4))) NativeVectorAll.unitEvidence) (NativeVectorAll.allEvidenceConsCase (recursiveWitness (.var 4) (.var 3) (.var 2)))) (.var 1)) (.var 0)) = some candidateType6
  rw [FormationSensitiveElaboration.typeProjection.eq_def]
  dsimp only
  have prior := checkedPrefix5
  change FormationSensitiveElaboration.typeProjection inventoryRules inventoryChoices
    254 branchContext (.app (.app (.app (.app (.app (.const vecEliminateName) treeTm) (NativeVectorAll.allEvidenceMotive treeTm (.var 4))) NativeVectorAll.unitEvidence) (NativeVectorAll.allEvidenceConsCase (recursiveWitness (.var 4) (.var 3) (.var 2)))) (.var 1)) = some candidateType5 at prior
  rw [prior, filteredChoices_exact]
  decide +kernel

#print axioms checkedPrefix6

theorem actualProducer_present :
    (FormationSensitiveElaboration.check inventoryRules inventoryChoices 256
      branchContext branchBundle branchBundleType).isSome = true := by
  rw [FormationSensitiveElaboration.check_success inventoryRules inventoryChoices]
  unfold FormationSensitiveElaboration.checkProjection
  rw [FormationSensitiveElaboration.checkPresence.eq_def]
  dsimp only
  have prior := checkedPrefix6
  change FormationSensitiveElaboration.typeProjection inventoryRules inventoryChoices
    255 branchContext branchBundle = some candidateType6 at prior
  rw [prior, filteredChoices_exact]
  decide +kernel

#print axioms actualProducer_present
end Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.ProducerEvidence
