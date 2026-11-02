import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAll
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllTypeEvidence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveSignaturePreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaborationComponents
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionSearchProjection
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionSearchComparison
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaborationProjection
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaborationCheckpoints

/-!
# Retained producer and replay components for native Vector `All`

The source eliminator is applied to its element and motive with the original
bounded producer. Literal type candidates are checked by exact projection
equations. Each retained code is identified with the original producer's
output and replayed independently. The later base, method, length and vector
applications remain separate obligations.

Closed retained-code constants are proof-only receipts, rather than import
initializers that execute the example. Executable certificate production
remains available through the original synthesis and checking functions.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.ReplayComponents

open Presentation RussellTarski
open NativeNaturalVectorFamilies
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll

local instance : DecidableRel NativeVectorAll.rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred NativeVectorAll.rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (NativeVectorAll.rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel NativeVectorAll.rules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel NativeVectorAll.rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

private def proofEvaluationChoices : FormationSensitiveElaboration.Choices Tower.Head NativeVectorAll.decoder.Code :=
  { NativeVectorAll.choices with normalize := fun fuel term =>
      StructuralConversionSearch.termProjection NativeVectorAll.decoder.decode NativeVectorAll.searchRoot fuel term }

private theorem proofEvaluationChoices_exact : NativeVectorAll.choices = proofEvaluationChoices := by
  have normalizationExact : (@NativeVectorAll.choices.normalize) =
      (fun {n} fuel (term : Tower.Tm n) =>
        StructuralConversionSearch.termProjection NativeVectorAll.decoder.decode NativeVectorAll.searchRoot fuel term) := by
    funext n fuel term
    change (match StructuralConversionSearch.normalize NativeVectorAll.decoder NativeVectorAll.searchRoot
      (headEq := NativeVectorAll.rules.headEq) fuel term with
      | none => term
      | some candidate => candidate.term) = _
    rw [StructuralConversionSearch.normalize_eq_some_produce]
    exact StructuralConversionSearch.produce_term NativeVectorAll.decoder.decode NativeVectorAll.searchRoot fuel term
  exact congrArg (fun normalize : {n : Nat} → Nat → Tower.Tm n → Tower.Tm n =>
    {NativeVectorAll.choices with normalize := normalize}) normalizationExact

private def proofConversion {n : Nat} (fuel : Nat) (left right : Tower.Tm n) :
    Option (StructuralConversionCode.Code Tower.Head NativeVectorAll.decoder.Code n) := do
  let first := StructuralConversionSearch.termProjection NativeVectorAll.decoder.decode NativeVectorAll.searchRoot fuel left
  let second := StructuralConversionSearch.termProjection NativeVectorAll.decoder.decode NativeVectorAll.searchRoot fuel right
  let middle ← StructuralConversionSearch.compareShape first second
  let recipe := StructuralConversionCode.Code.trans
    (StructuralConversionSearch.produce NativeVectorAll.decoder.decode NativeVectorAll.searchRoot fuel left).recipe
    (.trans middle (.symm
      (StructuralConversionSearch.produce NativeVectorAll.decoder.decode NativeVectorAll.searchRoot fuel right).recipe))
  if middle.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode first second then some recipe else none

private def comparisonEvaluationChoices : FormationSensitiveElaboration.Choices Tower.Head NativeVectorAll.decoder.Code :=
  { proofEvaluationChoices with conversion := proofConversion }

private theorem comparisonEvaluationChoices_exact : NativeVectorAll.choices = comparisonEvaluationChoices := by
  have comparisonExact : (@proofEvaluationChoices.conversion) = @proofConversion := by
    funext n fuel left right
    change StructuralConversionSearch.compare NativeVectorAll.decoder NativeVectorAll.searchRoot
      (headEq := NativeVectorAll.rules.headEq) fuel left right = _
    exact StructuralConversionSearch.compare_eq_projected_middle_check NativeVectorAll.rules.headEq
      NativeVectorAll.decoder NativeVectorAll.searchRoot fuel left right
  exact proofEvaluationChoices_exact.trans
    (congrArg (fun comparison : {n : Nat} → Nat → Tower.Tm n → Tower.Tm n →
      Option (StructuralConversionCode.Code Tower.Head NativeVectorAll.decoder.Code n) =>
        {proofEvaluationChoices with conversion := comparison}) comparisonExact)

private def arguments : List (Tower.Tm 5) :=
  [.var 4, allEvidenceMotive (.var 4) (.var 3), unitEvidence,
    allEvidenceConsCase (.var 2), .var 1, .var 0]

private def applicationPrefix : Nat → Tower.Tm 5
  | 0 => .const vecEliminateName
  | i+1 => .app (applicationPrefix i) (arguments[i]?.getD (.var 0))

private def candidateType0 : Tower.Tm 5 :=
  (.pi (.head (.sort (.param 0))) (.pi (.pi (.const `CumulativeTower.Nat) (.pi (.app (.app (.const `CumulativeTower.Vec) (.var 1)) (.var 0)) (.head (.sort (.succ (.param 0)))))) (.pi (.app (.app (.var 0) (.const `CumulativeTower.Nat.zero)) (.app (.const `CumulativeTower.Vec.nil) (.var 1))) (.pi (.pi (.const `CumulativeTower.Nat) (.pi (.var 3) (.pi (.app (.app (.const `CumulativeTower.Vec) (.var 4)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 0)) (.app (.app (.var 5) (.app (.const `CumulativeTower.Nat.succ) (.var 3))) (.app (.app (.app (.app (.const `CumulativeTower.Vec.cons) (.var 6)) (.var 3)) (.var 2)) (.var 1))))))) (.pi (.const `CumulativeTower.Nat) (.pi (.app (.app (.const `CumulativeTower.Vec) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0))))))))

private def candidateType1 : Tower.Tm 5 :=
  (.pi (.pi (.const `CumulativeTower.Nat) (.pi (.app (.app (.const `CumulativeTower.Vec) (.var 5)) (.var 0)) (.head (.sort (.succ (.param 0)))))) (.pi (.app (.app (.var 0) (.const `CumulativeTower.Nat.zero)) (.app (.const `CumulativeTower.Vec.nil) (.var 5))) (.pi (.pi (.const `CumulativeTower.Nat) (.pi (.var 7) (.pi (.app (.app (.const `CumulativeTower.Vec) (.var 8)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 0)) (.app (.app (.var 5) (.app (.const `CumulativeTower.Nat.succ) (.var 3))) (.app (.app (.app (.app (.const `CumulativeTower.Vec.cons) (.var 10)) (.var 3)) (.var 2)) (.var 1))))))) (.pi (.const `CumulativeTower.Nat) (.pi (.app (.app (.const `CumulativeTower.Vec) (.var 8)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))

private def candidateType2 : Tower.Tm 5 :=
  (.pi (.app (.app (.lam (.lam (.app (.app (.app (.app (.app (.app (.const `CumulativeTower.Vec.eliminate) (.var 6)) (.lam (.lam (.head (.sort (.param 0)))))) (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero))) (.lam (.lam (.lam (.lam (.sigma (.app (.var 9) (.var 2)) (.var 1))))))) (.var 1)) (.var 0)))) (.const `CumulativeTower.Nat.zero)) (.app (.const `CumulativeTower.Vec.nil) (.var 4))) (.pi (.pi (.const `CumulativeTower.Nat) (.pi (.var 6) (.pi (.app (.app (.const `CumulativeTower.Vec) (.var 7)) (.var 1)) (.pi (.app (.app (.lam (.lam (.app (.app (.app (.app (.app (.app (.const `CumulativeTower.Vec.eliminate) (.var 10)) (.lam (.lam (.head (.sort (.param 0)))))) (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero))) (.lam (.lam (.lam (.lam (.sigma (.app (.var 13) (.var 2)) (.var 1))))))) (.var 1)) (.var 0)))) (.var 2)) (.var 0)) (.app (.app (.lam (.lam (.app (.app (.app (.app (.app (.app (.const `CumulativeTower.Vec.eliminate) (.var 11)) (.lam (.lam (.head (.sort (.param 0)))))) (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero))) (.lam (.lam (.lam (.lam (.sigma (.app (.var 14) (.var 2)) (.var 1))))))) (.var 1)) (.var 0)))) (.app (.const `CumulativeTower.Nat.succ) (.var 3))) (.app (.app (.app (.app (.const `CumulativeTower.Vec.cons) (.var 9)) (.var 3)) (.var 2)) (.var 1))))))) (.pi (.const `CumulativeTower.Nat) (.pi (.app (.app (.const `CumulativeTower.Vec) (.var 7)) (.var 0)) (.app (.app (.lam (.lam (.app (.app (.app (.app (.app (.app (.const `CumulativeTower.Vec.eliminate) (.var 10)) (.lam (.lam (.head (.sort (.param 0)))))) (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero))) (.lam (.lam (.lam (.lam (.sigma (.app (.var 13) (.var 2)) (.var 1))))))) (.var 1)) (.var 0)))) (.var 1)) (.var 0))))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem checkedPrefix0 :
    FormationSensitiveElaboration.typeProjection NativeVectorAll.rules NativeVectorAll.choices
      121 contextAPWNV (applicationPrefix 0) = some candidateType0 := by
  rw [comparisonEvaluationChoices_exact]
  decide +kernel

#print axioms checkedPrefix0

private theorem prefix0_present :
    (FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices
      121 contextAPWNV (applicationPrefix 0)).isSome = true := by
  have equality := (FormationSensitiveElaboration.synth_type NativeVectorAll.rules NativeVectorAll.choices
    121 contextAPWNV (applicationPrefix 0)).trans checkedPrefix0
  have presence := congrArg Option.isSome equality
  simpa only [Option.isSome_map,Option.isSome_some] using presence

private noncomputable def actualInferred0 :=
  (FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices
    121 contextAPWNV (applicationPrefix 0)).get prefix0_present

private theorem actualInferred0_origin :
    FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices
      121 contextAPWNV (applicationPrefix 0) = some actualInferred0 :=
  Option.eq_some_of_isSome prefix0_present

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem actualInferred0_replay :
    StructuralTypingReplay.check (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code) NativeVectorAll.rules
      (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
      contextAPWNV (applicationPrefix 0) candidateType0 actualInferred0.evidence = true := by
  unfold actualInferred0
  rw [Option.get_congr (ho := prefix0_present)
    (congrArg (fun selected => FormationSensitiveElaboration.synth NativeVectorAll.rules
      selected 121 contextAPWNV (applicationPrefix 0)) comparisonEvaluationChoices_exact)]
  decide +kernel

#print axioms actualInferred0_replay

private theorem actualInferred0_type : actualInferred0.type = candidateType0 := by
  have equality := FormationSensitiveElaboration.synth_type NativeVectorAll.rules NativeVectorAll.choices
    121 contextAPWNV (applicationPrefix 0)
  rw [actualInferred0_origin,checkedPrefix0,Option.map_some] at equality
  exact Option.some.inj equality

private def firstDomain : Tower.Tm 5 :=
  match candidateType0 with | .pi domain _ => domain | _ => .head .legacyGround
private def firstBody : Tower.Tm 6 :=
  match candidateType0 with | .pi _ body => body | _ => .head .legacyGround

private theorem candidate0_shape : candidateType0 = .pi firstDomain firstBody := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem first_normalization :
    NativeVectorAll.choices.normalize 121 candidateType0 = .pi firstDomain firstBody := by
  rw [comparisonEvaluationChoices_exact]
  decide +kernel

private theorem first_alignment :
    FormationSensitiveElaboration.align NativeVectorAll.rules NativeVectorAll.choices
      121 contextAPWNV (applicationPrefix 0) candidateType0 (.pi firstDomain firstBody)
      actualInferred0.evidence = some actualInferred0.evidence := by
  rw [← candidate0_shape]
  simp [FormationSensitiveElaboration.align]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem first_argument :
    FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
      121 contextAPWNV (.var 4) firstDomain = some (.var) := by
  rfl

private theorem synth_application_of {Head : Type} {RootCode : Nat → Type}
    (R : Rules Head) (choices : FormationSensitiveElaboration.Choices Head RootCode) [DecidableEq Head]
    (fuel : Nat) {n : Nat} (context : Ctx Head n) (function argument : Tm Head n)
    (notLambda : ∀ body, function ≠ .lam body)
    (inferred : FormationSensitiveElaboration.Inferred Head RootCode n)
    (domain : Tm Head n) (body : Tm Head (n+1))
    (functionCode argumentCode : FormationSensitiveElaboration.Code Head RootCode n)
    (prior : FormationSensitiveElaboration.synth R choices fuel context function = some inferred)
    (view : choices.normalize fuel inferred.type = .pi domain body)
    (aligned : FormationSensitiveElaboration.align R choices fuel context function inferred.type
      (.pi domain body) inferred.evidence = some functionCode)
    (checked : FormationSensitiveElaboration.check R choices fuel context argument domain = some argumentCode) :
    FormationSensitiveElaboration.synth R choices (fuel+1) context (.app function argument) =
      some ⟨inst0 argument body,.appElim domain body functionCode argumentCode⟩ := by
  cases function <;> try { exact False.elim (notLambda _ rfl) }
  all_goals simp only [FormationSensitiveElaboration.synth,prior,Option.bind_eq_bind,Option.bind_some,
    view,aligned,checked,Option.pure_def]

private noncomputable def actualCode1 : FormationSensitiveElaboration.Code Tower.Head NativeVectorAll.decoder.Code 5 :=
  .appElim firstDomain firstBody actualInferred0.evidence .var

private theorem originalPrefix1 :
    FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices
      122 contextAPWNV (applicationPrefix 1) = some ⟨candidateType1,actualCode1⟩ := by
  have termEq : applicationPrefix 1 = .app (applicationPrefix 0) (.var 4) := rfl
  rw [termEq]
  have view := first_normalization
  rw [← actualInferred0_type] at view
  have aligned := first_alignment
  rw [← actualInferred0_type] at aligned
  have application := synth_application_of NativeVectorAll.rules NativeVectorAll.choices
    121 contextAPWNV (applicationPrefix 0) (.var 4) (by intro body; change ¬Tm.const vecEliminateName = .lam body; intro h; cases h)
    actualInferred0 firstDomain firstBody actualInferred0.evidence .var
    actualInferred0_origin view aligned first_argument
  have result : inst0 (.var (4 : Fin 5)) firstBody = candidateType1 := by decide +kernel
  simpa only [actualCode1,result] using application

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem actualCode1_replay :
    StructuralTypingReplay.check (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code) NativeVectorAll.rules
      (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
      contextAPWNV (applicationPrefix 1) candidateType1 actualCode1 = true := by
  have termEq : applicationPrefix 1 = .app (applicationPrefix 0) (.var 4) := rfl
  rw [termEq]
  unfold actualCode1
  rw [StructuralTypingReplay.check]
  have previous := actualInferred0_replay
  rw [candidate0_shape] at previous
  rw [previous]
  decide +kernel

#print axioms originalPrefix1
#print axioms actualCode1_replay

private def secondDomain : Tower.Tm 5 :=
  match candidateType1 with | .pi domain _ => domain | _ => .head .legacyGround
private def secondBody : Tower.Tm 6 :=
  match candidateType1 with | .pi _ body => body | _ => .head .legacyGround

private theorem candidate1_shape : candidateType1 = .pi secondDomain secondBody := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem second_normalization :
    NativeVectorAll.choices.normalize 122 candidateType1 = .pi secondDomain secondBody := by
  rw [comparisonEvaluationChoices_exact]
  decide +kernel

private theorem second_alignment :
    FormationSensitiveElaboration.align NativeVectorAll.rules NativeVectorAll.choices
      122 contextAPWNV (applicationPrefix 1) candidateType1 (.pi secondDomain secondBody)
      actualCode1 = some actualCode1 := by
  rw [← candidate1_shape]
  simp [FormationSensitiveElaboration.align]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem motive_present :
    (FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
      122 contextAPWNV (allEvidenceMotive (.var 4) (.var 3)) secondDomain).isSome = true := by
  rw [FormationSensitiveElaboration.check_success,comparisonEvaluationChoices_exact]
  decide +kernel

private noncomputable def actualMotiveCode := FormationSensitiveElaboration.producedTermCode NativeVectorAll.rules
  NativeVectorAll.choices 122 contextAPWNV (allEvidenceMotive (.var 4) (.var 3)) secondDomain motive_present

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem actualMotiveCode_replay :
    StructuralTypingReplay.check (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code) NativeVectorAll.rules
      (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
      contextAPWNV (allEvidenceMotive (.var 4) (.var 3)) secondDomain actualMotiveCode = true := by
  unfold actualMotiveCode FormationSensitiveElaboration.producedTermCode
  rw [Option.get_congr (ho := motive_present)
    (congrArg (fun selected => FormationSensitiveElaboration.check NativeVectorAll.rules
      selected 122 contextAPWNV (allEvidenceMotive (.var 4) (.var 3)) secondDomain)
      comparisonEvaluationChoices_exact)]
  decide +kernel

private noncomputable def actualCode2 : FormationSensitiveElaboration.Code Tower.Head NativeVectorAll.decoder.Code 5 :=
  .appElim secondDomain secondBody actualCode1 actualMotiveCode

private theorem originalPrefix2 :
    FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices
      123 contextAPWNV (applicationPrefix 2) = some ⟨candidateType2,actualCode2⟩ := by
  have termEq : applicationPrefix 2 = .app (applicationPrefix 1) (allEvidenceMotive (.var 4) (.var 3)) := rfl
  rw [termEq]
  have application := synth_application_of NativeVectorAll.rules NativeVectorAll.choices
    122 contextAPWNV (applicationPrefix 1) (allEvidenceMotive (.var 4) (.var 3))
    (by intro body; change ¬Tm.app (.const vecEliminateName) (.var 4) = .lam body; intro h; cases h)
    ⟨candidateType1,actualCode1⟩ secondDomain secondBody actualCode1 actualMotiveCode
    originalPrefix1 second_normalization second_alignment
    (FormationSensitiveElaboration.producedTermCode_origin NativeVectorAll.rules NativeVectorAll.choices
      122 contextAPWNV (allEvidenceMotive (.var 4) (.var 3)) secondDomain motive_present)
  have result : inst0 (allEvidenceMotive (.var (4 : Fin 5)) (.var 3)) secondBody = candidateType2 := by decide +kernel
  simpa only [actualCode2,result] using application

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem actualCode2_replay :
    StructuralTypingReplay.check (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code) NativeVectorAll.rules
      (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
      contextAPWNV (applicationPrefix 2) candidateType2 actualCode2 = true := by
  have termEq : applicationPrefix 2 = .app (applicationPrefix 1) (allEvidenceMotive (.var 4) (.var 3)) := rfl
  rw [termEq]
  unfold actualCode2
  rw [StructuralTypingReplay.check]
  have previous := actualCode1_replay
  rw [candidate1_shape] at previous
  rw [previous,actualMotiveCode_replay]
  decide +kernel

#print axioms originalPrefix2
#print axioms actualCode2_replay
def motiveApplication : Tower.Tm 5 := applicationPrefix 2
def motiveApplicationType : Tower.Tm 5 := candidateType2
noncomputable def motiveApplicationCode : FormationSensitiveElaboration.Code Tower.Head NativeVectorAll.decoder.Code 5 :=
  actualCode2
def evaluationChoices : FormationSensitiveElaboration.Choices Tower.Head NativeVectorAll.decoder.Code :=
  comparisonEvaluationChoices

theorem choices_for_proof_evaluation : NativeVectorAll.choices = evaluationChoices :=
  comparisonEvaluationChoices_exact

theorem motiveApplication_source : motiveApplication =
    .app (.app (.const vecEliminateName) (.var 4)) (allEvidenceMotive (.var 4) (.var 3)) := rfl

theorem motiveApplication_produced :
    FormationSensitiveElaboration.synth NativeVectorAll.rules NativeVectorAll.choices
      123 contextAPWNV motiveApplication = some ⟨motiveApplicationType,motiveApplicationCode⟩ := by
  unfold motiveApplication motiveApplicationType motiveApplicationCode
  exact originalPrefix2

theorem motiveApplication_replay :
    StructuralTypingReplay.check (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code) NativeVectorAll.rules
      (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
      contextAPWNV motiveApplication motiveApplicationType motiveApplicationCode = true := by
  unfold motiveApplication motiveApplicationType motiveApplicationCode
  exact actualCode2_replay

#print axioms motiveApplication_produced
#print axioms motiveApplication_replay

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.ReplayComponents
