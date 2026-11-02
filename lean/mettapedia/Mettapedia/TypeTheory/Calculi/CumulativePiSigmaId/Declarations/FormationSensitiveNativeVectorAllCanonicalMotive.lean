import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllCanonicalProduction

/-!
# Original closed Vector All motive replay

The original two-lambda motive is checked at its actual recursor-argument
type. Actual formation, body replay and alignment observations compose the
original producer/replay result, retaining the actual produced certificate.
-/

set_option autoImplicit false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.CanonicalChecking.Motive
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
def motiveType : Tower.Tm 0 := match CanonicalChecking.prefixType 1 with | .pi a _ => a | _ => .head .legacyGround
private def domain0 : Tower.Tm 0 := match motiveType with | .pi a _ => a | _ => .head .legacyGround
private def type1 : Tower.Tm 1 := match motiveType with | .pi _ b => b | _ => .head .legacyGround
private def context1 : Tower.Ctx 1 := .snoc .nil domain0
private def domain1 : Tower.Tm 1 := match type1 with | .pi a _ => a | _ => .head .legacyGround
private def type2 : Tower.Tm 2 := match type1 with | .pi _ b => b | _ => .head .legacyGround
private def context2 : Tower.Ctx 2 := .snoc context1 domain1

private def body : Tower.Tm 2 := allType natTm (weaken2 predicate) (.var 1) (.var 0)

private def motiveSource : Tower.Tm 0 := .lam (.lam body)
private theorem motiveSource_eq : motiveSource = allEvidenceMotive natTm predicate := rfl
private theorem shape0 : motiveType = .pi domain0 type1 := rfl
private theorem shape1 : type1 = .pi domain1 type2 := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem view0 : NativeVectorAll.choices.normalize 121 motiveType = .pi domain0 type1 := by
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem view1 : NativeVectorAll.choices.normalize 120 type1 = .pi domain1 type2 := by
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem formation0 : FormationSensitiveElaboration.formationReplayAccepted NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 121 .nil motiveType = true := by
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem formation1 : FormationSensitiveElaboration.formationReplayAccepted NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 120 context1 type1 = true := by
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem body_replay : FormationSensitiveElaboration.termReplayAccepted NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 120 context2 body type2 = true := by
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

#print axioms formation0
#print axioms body_replay

private theorem guard0 : FormationSensitiveElaboration.alignReplayGuard NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 121 .nil (.pi domain0 type1) motiveType = true := by
  rw [← shape0]
  simp [FormationSensitiveElaboration.alignReplayGuard]
private theorem guard1 : FormationSensitiveElaboration.alignReplayGuard NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 120 context1 (.pi domain1 type2) type1 = true := by
  rw [← shape1]
  simp [FormationSensitiveElaboration.alignReplayGuard]

private theorem inner_replay : FormationSensitiveElaboration.termReplayAccepted NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 121 context1 (.lam body) type1 = true := by
  have formation := formation1
  rw [shape1] at formation
  exact (FormationSensitiveElaboration.lambda_replay_factor NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 120 context1 body type1 domain1 type2 view1).trans
      (congrArg₂ Bool.and (congrArg₂ Bool.and formation body_replay) guard1)

theorem motive_replay : FormationSensitiveElaboration.termReplayAccepted NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 122 .nil (allEvidenceMotive natTm predicate) motiveType = true := by
  rw [← motiveSource_eq]
  have formation := formation0
  rw [shape0] at formation
  exact (FormationSensitiveElaboration.lambda_replay_factor NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 121 .nil (.lam body) motiveType domain0 type1 view0).trans
      (congrArg₂ Bool.and (congrArg₂ Bool.and formation inner_replay) guard0)

#print axioms motive_replay

private theorem term_produced_of_replay {Head : Type} (R : Rules Head) [DecidableEq Head]
    [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
    [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative] [DecidableRel R.headEq]
    (decoder : StructuralConversionCode.RootDecoder R.computation)
    (choices : FormationSensitiveElaboration.Choices Head decoder.Code) (fuel : Nat) {n : Nat}
    (context : Ctx Head n) (term type : Tm Head n)
    (accepted : FormationSensitiveElaboration.termReplayAccepted R decoder choices fuel context term type = true) :
    (FormationSensitiveElaboration.check R choices fuel context term type).isSome = true := by
  unfold FormationSensitiveElaboration.termReplayAccepted at accepted
  cases produced : FormationSensitiveElaboration.check R choices fuel context term type with
  | none => simp [produced] at accepted
  | some code => rfl

theorem motive_produced :
    (FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
      122 .nil (allEvidenceMotive natTm predicate) motiveType).isSome = true :=
  term_produced_of_replay NativeVectorAll.rules NativeVectorAll.decoder NativeVectorAll.choices
    122 .nil (allEvidenceMotive natTm predicate) motiveType motive_replay

noncomputable def motiveCode : FormationSensitiveElaboration.Code Tower.Head NativeVectorAll.decoder.Code 0 :=
  FormationSensitiveElaboration.producedTermCode NativeVectorAll.rules NativeVectorAll.choices
    122 .nil (allEvidenceMotive natTm predicate) motiveType motive_produced

theorem motiveCode_origin :
    FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
      122 .nil (allEvidenceMotive natTm predicate) motiveType = some motiveCode := by
  unfold motiveCode
  exact FormationSensitiveElaboration.producedTermCode_origin NativeVectorAll.rules NativeVectorAll.choices
    122 .nil (allEvidenceMotive natTm predicate) motiveType motive_produced

theorem motiveCode_replay : StructuralTypingReplay.check
    (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code)
    NativeVectorAll.rules
    (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
    .nil (allEvidenceMotive natTm predicate) motiveType motiveCode = true := by
  unfold motiveCode
  exact (FormationSensitiveElaboration.termReplayAccepted_eq_produced_code NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 122 .nil (allEvidenceMotive natTm predicate) motiveType motive_produced).symm.trans motive_replay

#print axioms motiveCode_origin
#print axioms motiveCode_replay
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.CanonicalChecking.Motive
