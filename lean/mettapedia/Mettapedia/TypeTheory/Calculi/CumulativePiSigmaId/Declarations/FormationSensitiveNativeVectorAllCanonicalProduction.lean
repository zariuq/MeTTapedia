import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllMethodComponents

/-!
# Actual production for the two-position closed Vector All control

Literal inferred-type candidates are checked against the original producer
through exact projection equations. The original final check still uses
fuel 128 and the original two-position source. Production success alone does
not establish independent replay or publication.
-/

set_option autoImplicit false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.CanonicalChecking
open Presentation RussellTarski
open NativeNaturalVectorFamilies CanonicalAdequacy
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
def predicate : Tower.Tm 0 := .lam (.id natTm (.var 0) (.var 0))
def witness : Tower.Tm 0 := .lam (.refl (.var 0))
def values : List (Tower.Tm 0) := [zeroTm,succApp zeroTm]
def type : Tower.Tm 0 := allType natTm predicate (numeral values.length) (encodeVector natTm values)
def evidence : Tower.Tm 0 := allEvidence natTm predicate witness (numeral values.length) (encodeVector natTm values)

private def candidateType0 : Tower.Tm 0 :=
  (.pi (.head (.sort (.param 0))) (.pi (.pi (.const `CumulativeTower.Nat) (.pi (.app (.app (.const `CumulativeTower.Vec) (.var 1)) (.var 0)) (.head (.sort (.succ (.param 0)))))) (.pi (.app (.app (.var 0) (.const `CumulativeTower.Nat.zero)) (.app (.const `CumulativeTower.Vec.nil) (.var 1))) (.pi (.pi (.const `CumulativeTower.Nat) (.pi (.var 3) (.pi (.app (.app (.const `CumulativeTower.Vec) (.var 4)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 0)) (.app (.app (.var 5) (.app (.const `CumulativeTower.Nat.succ) (.var 3))) (.app (.app (.app (.app (.const `CumulativeTower.Vec.cons) (.var 6)) (.var 3)) (.var 2)) (.var 1))))))) (.pi (.const `CumulativeTower.Nat) (.pi (.app (.app (.const `CumulativeTower.Vec) (.var 4)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0))))))))

private def candidateType1 : Tower.Tm 0 :=
  (.pi (.pi (.const `CumulativeTower.Nat) (.pi (.app (.app (.const `CumulativeTower.Vec) (.const `CumulativeTower.Nat)) (.var 0)) (.head (.sort (.succ (.param 0)))))) (.pi (.app (.app (.var 0) (.const `CumulativeTower.Nat.zero)) (.app (.const `CumulativeTower.Vec.nil) (.const `CumulativeTower.Nat))) (.pi (.pi (.const `CumulativeTower.Nat) (.pi (.const `CumulativeTower.Nat) (.pi (.app (.app (.const `CumulativeTower.Vec) (.const `CumulativeTower.Nat)) (.var 1)) (.pi (.app (.app (.var 4) (.var 2)) (.var 0)) (.app (.app (.var 5) (.app (.const `CumulativeTower.Nat.succ) (.var 3))) (.app (.app (.app (.app (.const `CumulativeTower.Vec.cons) (.const `CumulativeTower.Nat)) (.var 3)) (.var 2)) (.var 1))))))) (.pi (.const `CumulativeTower.Nat) (.pi (.app (.app (.const `CumulativeTower.Vec) (.const `CumulativeTower.Nat)) (.var 0)) (.app (.app (.var 4) (.var 1)) (.var 0)))))))

private def candidateType2 : Tower.Tm 0 :=
  (.pi (.app (.app (.lam (.lam (.app (.app (.app (.app (.app (.app (.const `CumulativeTower.Vec.eliminate) (.const `CumulativeTower.Nat)) (.lam (.lam (.head (.sort (.param 0)))))) (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero))) (.lam (.lam (.lam (.lam (.sigma (.app (.lam (.id (.const `CumulativeTower.Nat) (.var 0) (.var 0))) (.var 2)) (.var 1))))))) (.var 1)) (.var 0)))) (.const `CumulativeTower.Nat.zero)) (.app (.const `CumulativeTower.Vec.nil) (.const `CumulativeTower.Nat))) (.pi (.pi (.const `CumulativeTower.Nat) (.pi (.const `CumulativeTower.Nat) (.pi (.app (.app (.const `CumulativeTower.Vec) (.const `CumulativeTower.Nat)) (.var 1)) (.pi (.app (.app (.lam (.lam (.app (.app (.app (.app (.app (.app (.const `CumulativeTower.Vec.eliminate) (.const `CumulativeTower.Nat)) (.lam (.lam (.head (.sort (.param 0)))))) (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero))) (.lam (.lam (.lam (.lam (.sigma (.app (.lam (.id (.const `CumulativeTower.Nat) (.var 0) (.var 0))) (.var 2)) (.var 1))))))) (.var 1)) (.var 0)))) (.var 2)) (.var 0)) (.app (.app (.lam (.lam (.app (.app (.app (.app (.app (.app (.const `CumulativeTower.Vec.eliminate) (.const `CumulativeTower.Nat)) (.lam (.lam (.head (.sort (.param 0)))))) (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero))) (.lam (.lam (.lam (.lam (.sigma (.app (.lam (.id (.const `CumulativeTower.Nat) (.var 0) (.var 0))) (.var 2)) (.var 1))))))) (.var 1)) (.var 0)))) (.app (.const `CumulativeTower.Nat.succ) (.var 3))) (.app (.app (.app (.app (.const `CumulativeTower.Vec.cons) (.const `CumulativeTower.Nat)) (.var 3)) (.var 2)) (.var 1))))))) (.pi (.const `CumulativeTower.Nat) (.pi (.app (.app (.const `CumulativeTower.Vec) (.const `CumulativeTower.Nat)) (.var 0)) (.app (.app (.lam (.lam (.app (.app (.app (.app (.app (.app (.const `CumulativeTower.Vec.eliminate) (.const `CumulativeTower.Nat)) (.lam (.lam (.head (.sort (.param 0)))))) (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero))) (.lam (.lam (.lam (.lam (.sigma (.app (.lam (.id (.const `CumulativeTower.Nat) (.var 0) (.var 0))) (.var 2)) (.var 1))))))) (.var 1)) (.var 0)))) (.var 1)) (.var 0))))))

private def candidateType3 : Tower.Tm 0 :=
  (.pi (.pi (.const `CumulativeTower.Nat) (.pi (.const `CumulativeTower.Nat) (.pi (.app (.app (.const `CumulativeTower.Vec) (.const `CumulativeTower.Nat)) (.var 1)) (.pi (.app (.app (.app (.app (.app (.app (.const `CumulativeTower.Vec.eliminate) (.const `CumulativeTower.Nat)) (.lam (.lam (.head (.sort (.param 0)))))) (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero))) (.lam (.lam (.lam (.lam (.sigma (.id (.const `CumulativeTower.Nat) (.var 2) (.var 2)) (.var 1))))))) (.var 2)) (.var 0)) (.sigma (.id (.const `CumulativeTower.Nat) (.var 2) (.var 2)) (.app (.app (.app (.app (.app (.app (.const `CumulativeTower.Vec.eliminate) (.const `CumulativeTower.Nat)) (.lam (.lam (.head (.sort (.param 0)))))) (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero))) (.lam (.lam (.lam (.lam (.sigma (.id (.const `CumulativeTower.Nat) (.var 2) (.var 2)) (.var 1))))))) (.var 4)) (.var 2))))))) (.pi (.const `CumulativeTower.Nat) (.pi (.app (.app (.const `CumulativeTower.Vec) (.const `CumulativeTower.Nat)) (.var 0)) (.app (.app (.app (.app (.app (.app (.const `CumulativeTower.Vec.eliminate) (.const `CumulativeTower.Nat)) (.lam (.lam (.head (.sort (.param 0)))))) (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero))) (.lam (.lam (.lam (.lam (.sigma (.id (.const `CumulativeTower.Nat) (.var 2) (.var 2)) (.var 1))))))) (.var 1)) (.var 0)))))

private def candidateType4 : Tower.Tm 0 :=
  (.pi (.const `CumulativeTower.Nat) (.pi (.app (.app (.const `CumulativeTower.Vec) (.const `CumulativeTower.Nat)) (.var 0)) (.app (.app (.app (.app (.app (.app (.const `CumulativeTower.Vec.eliminate) (.const `CumulativeTower.Nat)) (.lam (.lam (.head (.sort (.param 0)))))) (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero))) (.lam (.lam (.lam (.lam (.sigma (.id (.const `CumulativeTower.Nat) (.var 2) (.var 2)) (.var 1))))))) (.var 1)) (.var 0))))

private def candidateType5 : Tower.Tm 0 :=
  (.pi (.app (.app (.const `CumulativeTower.Vec) (.const `CumulativeTower.Nat)) (.app (.const `CumulativeTower.Nat.succ) (.app (.const `CumulativeTower.Nat.succ) (.const `CumulativeTower.Nat.zero)))) (.app (.app (.app (.app (.app (.app (.const `CumulativeTower.Vec.eliminate) (.const `CumulativeTower.Nat)) (.lam (.lam (.head (.sort (.param 0)))))) (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero))) (.lam (.lam (.lam (.lam (.sigma (.id (.const `CumulativeTower.Nat) (.var 2) (.var 2)) (.var 1))))))) (.app (.const `CumulativeTower.Nat.succ) (.app (.const `CumulativeTower.Nat.succ) (.const `CumulativeTower.Nat.zero)))) (.var 0)))

private def candidateType6 : Tower.Tm 0 :=
  (.app (.app (.app (.app (.app (.app (.const `CumulativeTower.Vec.eliminate) (.const `CumulativeTower.Nat)) (.lam (.lam (.head (.sort (.param 0)))))) (.id (.const `CumulativeTower.Nat) (.const `CumulativeTower.Nat.zero) (.const `CumulativeTower.Nat.zero))) (.lam (.lam (.lam (.lam (.sigma (.id (.const `CumulativeTower.Nat) (.var 2) (.var 2)) (.var 1))))))) (.app (.const `CumulativeTower.Nat.succ) (.app (.const `CumulativeTower.Nat.succ) (.const `CumulativeTower.Nat.zero)))) (.app (.app (.app (.app (.const `CumulativeTower.Vec.cons) (.const `CumulativeTower.Nat)) (.app (.const `CumulativeTower.Nat.succ) (.const `CumulativeTower.Nat.zero))) (.const `CumulativeTower.Nat.zero)) (.app (.app (.app (.app (.const `CumulativeTower.Vec.cons) (.const `CumulativeTower.Nat)) (.const `CumulativeTower.Nat.zero)) (.app (.const `CumulativeTower.Nat.succ) (.const `CumulativeTower.Nat.zero))) (.app (.const `CumulativeTower.Vec.nil) (.const `CumulativeTower.Nat)))))

private theorem projection_application_eq {Head : Type} {RootCode : Nat → Type}
    (R : Rules Head) (choices : FormationSensitiveElaboration.Choices Head RootCode) [DecidableEq Head]
    (fuel : Nat) {n : Nat} (context : Ctx Head n) (function argument type : Tm Head n)
    (notLambda : ∀ body, function ≠ .lam body)
    (prior : FormationSensitiveElaboration.typeProjection R choices fuel context function = some type) :
    FormationSensitiveElaboration.typeProjection R choices (fuel+1) context (.app function argument) =
      (let viewed := choices.normalize fuel type
       match viewed with
       | .pi domain body => do
           let _ ← FormationSensitiveElaboration.alignPresence R choices fuel context function type viewed
           let _ ← FormationSensitiveElaboration.checkPresence R choices fuel context argument domain
           pure (inst0 argument body)
       | _ => none) := by
  cases function <;> try { exact False.elim (notLambda _ rfl) }
  all_goals
    simp only [FormationSensitiveElaboration.typeProjection,prior,Option.bind_eq_bind,Option.bind_some]
    cases choices.normalize fuel type <;> rfl

private def source0 : Tower.Tm 0 := .const vecEliminateName
private def source1 : Tower.Tm 0 := .app source0 natTm
private def source2 : Tower.Tm 0 := .app source1 (allEvidenceMotive natTm predicate)
private def source3 : Tower.Tm 0 := .app source2 unitEvidence
private def source4 : Tower.Tm 0 := .app source3 (allEvidenceConsCase witness)
private def source5 : Tower.Tm 0 := .app source4 (numeral values.length)
private def source6 : Tower.Tm 0 := .app source5 (encodeVector natTm values)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem projected0 : FormationSensitiveElaboration.typeProjection NativeVectorAll.rules NativeVectorAll.choices
    121 .nil source0 = some candidateType0 := by
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem projected1 : FormationSensitiveElaboration.typeProjection NativeVectorAll.rules NativeVectorAll.choices
    122 .nil source1 = some candidateType1 := by
  have notLambda : ∀ body : Tower.Tm 1, source0 ≠ .lam body := by intro body h; cases h
  unfold source1
  rw [projection_application_eq NativeVectorAll.rules NativeVectorAll.choices 121 .nil source0 natTm
    candidateType0 notLambda projected0,ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem projected2 : FormationSensitiveElaboration.typeProjection NativeVectorAll.rules NativeVectorAll.choices
    123 .nil source2 = some candidateType2 := by
  have notLambda : ∀ body : Tower.Tm 1, source1 ≠ .lam body := by intro body h; cases h
  unfold source2
  rw [projection_application_eq NativeVectorAll.rules NativeVectorAll.choices 122 .nil source1
    (allEvidenceMotive natTm predicate) candidateType1 notLambda projected1,ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem projected3 : FormationSensitiveElaboration.typeProjection NativeVectorAll.rules NativeVectorAll.choices
    124 .nil source3 = some candidateType3 := by
  have notLambda : ∀ body : Tower.Tm 1, source2 ≠ .lam body := by intro body h; cases h
  unfold source3
  rw [projection_application_eq NativeVectorAll.rules NativeVectorAll.choices 123 .nil source2
    unitEvidence candidateType2 notLambda projected2,ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem projected4 : FormationSensitiveElaboration.typeProjection NativeVectorAll.rules NativeVectorAll.choices
    125 .nil source4 = some candidateType4 := by
  have notLambda : ∀ body : Tower.Tm 1, source3 ≠ .lam body := by intro body h; cases h
  unfold source4
  rw [projection_application_eq NativeVectorAll.rules NativeVectorAll.choices 124 .nil source3
    (allEvidenceConsCase witness) candidateType3 notLambda projected3,ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem projected5 : FormationSensitiveElaboration.typeProjection NativeVectorAll.rules NativeVectorAll.choices
    126 .nil source5 = some candidateType5 := by
  have notLambda : ∀ body : Tower.Tm 1, source4 ≠ .lam body := by intro body h; cases h
  unfold source5
  rw [projection_application_eq NativeVectorAll.rules NativeVectorAll.choices 125 .nil source4
    (numeral values.length) candidateType4 notLambda projected4,ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem projected6 : FormationSensitiveElaboration.typeProjection NativeVectorAll.rules NativeVectorAll.choices
    127 .nil source6 = some candidateType6 := by
  have notLambda : ∀ body : Tower.Tm 1, source5 ≠ .lam body := by intro body h; cases h
  unfold source6
  rw [projection_application_eq NativeVectorAll.rules NativeVectorAll.choices 126 .nil source5
    (encodeVector natTm values) candidateType5 notLambda projected5,ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

#print axioms projected6

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem actual_producer_present :
    (FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices 128 .nil evidence type).isSome = true := by
  rw [FormationSensitiveElaboration.check_success]
  unfold FormationSensitiveElaboration.checkProjection
  rw [FormationSensitiveElaboration.checkPresence.eq_def]
  dsimp only
  have prior := projected6
  change FormationSensitiveElaboration.typeProjection NativeVectorAll.rules NativeVectorAll.choices
    127 .nil evidence = some candidateType6 at prior
  rw [prior,ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

#print axioms actual_producer_present

theorem producer_present :
    (FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices 128 .nil evidence type).isSome = true :=
  actual_producer_present

def applicationPrefix (index : Fin 7) : Tower.Tm 0 :=
  match index.val with
  | 0 => source0 | 1 => source1 | 2 => source2 | 3 => source3
  | 4 => source4 | 5 => source5 | _ => source6

def prefixType (index : Fin 7) : Tower.Tm 0 :=
  match index.val with
  | 0 => candidateType0 | 1 => candidateType1 | 2 => candidateType2 | 3 => candidateType3
  | 4 => candidateType4 | 5 => candidateType5 | _ => candidateType6

theorem prefix_projected (index : Fin 7) :
    FormationSensitiveElaboration.typeProjection NativeVectorAll.rules NativeVectorAll.choices
      (121+index.val) .nil (applicationPrefix index) = some (prefixType index) := by
  fin_cases index
  · exact projected0
  · exact projected1
  · exact projected2
  · exact projected3
  · exact projected4
  · exact projected5
  · exact projected6

theorem prefix0_source : applicationPrefix 0 = .const vecEliminateName := rfl
theorem prefix1_source : applicationPrefix 1 = .app (applicationPrefix 0) natTm := rfl
theorem prefix2_source : applicationPrefix 2 = .app (applicationPrefix 1) (allEvidenceMotive natTm predicate) := rfl
theorem prefix3_source : applicationPrefix 3 = .app (applicationPrefix 2) unitEvidence := rfl
theorem prefix4_source : applicationPrefix 4 = .app (applicationPrefix 3) (allEvidenceConsCase witness) := rfl
theorem prefix5_source : applicationPrefix 5 = .app (applicationPrefix 4) (numeral values.length) := rfl
theorem prefix6_source : applicationPrefix 6 = .app (applicationPrefix 5) (encodeVector natTm values) := rfl
theorem complete_source : applicationPrefix 6 = evidence := rfl

#print axioms producer_present
#print axioms prefix_projected
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.CanonicalChecking
