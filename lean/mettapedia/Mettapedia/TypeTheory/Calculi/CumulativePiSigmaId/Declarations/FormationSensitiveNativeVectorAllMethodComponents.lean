import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllBaseComponents
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveIntroductionReplay

/-!
# Original native Vector All cons-method acceptance

Five actual formation checks, both pair-component replays and each original
alignment guard compose the original method producer's replay observation.
The retained method code is exactly that producer's result. Closed receipt
constants are proof data; executable production uses the original checker.
-/

set_option autoImplicit false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.ReplayComponents
open Presentation RussellTarski
open NativeNaturalVectorFamilies

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

private def type0 : Tower.Tm 5 := ReplayComponents.methodType
private def domain0 : Tower.Tm 5 := match type0 with | .pi a _ => a | _ => .head .legacyGround
private def type1 : Tower.Tm 6 := match type0 with | .pi _ b => b | _ => .head .legacyGround
private def context1 : Tower.Ctx 6 := .snoc contextAPWNV domain0
private def domain1 : Tower.Tm 6 := match type1 with | .pi a _ => a | _ => .head .legacyGround
private def type2 : Tower.Tm 7 := match type1 with | .pi _ b => b | _ => .head .legacyGround
private def context2 : Tower.Ctx 7 := .snoc context1 domain1
private def domain2 : Tower.Tm 7 := match type2 with | .pi a _ => a | _ => .head .legacyGround
private def type3 : Tower.Tm 8 := match type2 with | .pi _ b => b | _ => .head .legacyGround
private def context3 : Tower.Ctx 8 := .snoc context2 domain2
private def domain3 : Tower.Tm 8 := match type3 with | .pi a _ => a | _ => .head .legacyGround
private def type4 : Tower.Tm 9 := match type3 with | .pi _ b => b | _ => .head .legacyGround
private def context4 : Tower.Ctx 9 := .snoc context3 domain3
private def pairDomain : Tower.Tm 9 := match type4 with | .sigma a _ => a | _ => .head .legacyGround
private def pairBody : Tower.Tm 10 := match type4 with | .sigma _ b => b | _ => .head .legacyGround

private theorem shape0 : type0 = .pi domain0 type1 := rfl
private theorem shape1 : type1 = .pi domain1 type2 := rfl
private theorem shape2 : type2 = .pi domain2 type3 := rfl
private theorem shape3 : type3 = .pi domain3 type4 := rfl
private theorem shape4 : type4 = .sigma pairDomain pairBody := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem view0 : NativeVectorAll.choices.normalize 123 type0 = .pi domain0 type1 := by
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem view1 : NativeVectorAll.choices.normalize 122 type1 = .pi domain1 type2 := by
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem view2 : NativeVectorAll.choices.normalize 121 type2 = .pi domain2 type3 := by
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem view3 : NativeVectorAll.choices.normalize 120 type3 = .pi domain3 type4 := by
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem view4 : NativeVectorAll.choices.normalize 119 type4 = .sigma pairDomain pairBody := by
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

private def formed {n : Nat} (fuel : Nat) (context : Tower.Ctx n) (type : Tower.Tm n) : Bool :=
  FormationSensitiveElaboration.formationReplayAccepted NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices fuel context type

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem formation0 : formed 123 contextAPWNV type0 = true := by
  unfold formed
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem formation1 : formed 122 context1 type1 = true := by
  unfold formed
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem formation2 : formed 121 context2 type2 = true := by
  unfold formed
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem formation3 : formed 120 context3 type3 = true := by
  unfold formed
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem formation4 : formed 119 context4 type4 = true := by
  unfold formed
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

#print axioms formation0
#print axioms formation4

private def first : Tower.Tm 9 := .app (.var 6) (.var 2)
private def second : Tower.Tm 9 := .var 0
private def pairSource : Tower.Tm 9 := .pair first second
private def body3 : Tower.Tm 8 := .lam pairSource
private def body2 : Tower.Tm 7 := .lam body3
private def body1 : Tower.Tm 6 := .lam body2
def methodSource : Tower.Tm 5 := .lam body1

theorem methodSource_eq : methodSource = allEvidenceConsCase (.var 2) := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem first_replay : FormationSensitiveElaboration.termReplayAccepted NativeVectorAll.rules
    NativeVectorAll.decoder NativeVectorAll.choices 119 context4 first pairDomain = true := by
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem second_replay : FormationSensitiveElaboration.termReplayAccepted NativeVectorAll.rules
    NativeVectorAll.decoder NativeVectorAll.choices 119 context4 second (inst0 first pairBody) = true := by
  rw [ReplayComponents.choices_for_proof_evaluation]
  decide +kernel

private theorem guard0 : FormationSensitiveElaboration.alignReplayGuard NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 123 contextAPWNV (.pi domain0 type1) type0 = true := by
  rw [← shape0]
  simp [FormationSensitiveElaboration.alignReplayGuard]
private theorem guard1 : FormationSensitiveElaboration.alignReplayGuard NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 122 context1 (.pi domain1 type2) type1 = true := by
  rw [← shape1]
  simp [FormationSensitiveElaboration.alignReplayGuard]
private theorem guard2 : FormationSensitiveElaboration.alignReplayGuard NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 121 context2 (.pi domain2 type3) type2 = true := by
  rw [← shape2]
  simp [FormationSensitiveElaboration.alignReplayGuard]
private theorem guard3 : FormationSensitiveElaboration.alignReplayGuard NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 120 context3 (.pi domain3 type4) type3 = true := by
  rw [← shape3]
  simp [FormationSensitiveElaboration.alignReplayGuard]
private theorem guard4 : FormationSensitiveElaboration.alignReplayGuard NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 119 context4 (.sigma pairDomain pairBody) type4 = true := by
  rw [← shape4]
  simp [FormationSensitiveElaboration.alignReplayGuard]

private theorem pair_accepted : FormationSensitiveElaboration.termReplayAccepted NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 120 context4 pairSource type4 = true := by
  have formation := formation4
  unfold formed at formation
  rw [shape4] at formation
  exact (FormationSensitiveElaboration.pair_replay_factor NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 119 context4 first second type4 pairDomain pairBody view4).trans
      (congrArg₂ Bool.and (congrArg₂ Bool.and (congrArg₂ Bool.and formation first_replay) second_replay) guard4)

private theorem body3_accepted : FormationSensitiveElaboration.termReplayAccepted NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 121 context3 body3 type3 = true := by
  have formation := formation3
  unfold formed at formation
  rw [shape3] at formation
  exact (FormationSensitiveElaboration.lambda_replay_factor NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 120 context3 pairSource type3 domain3 type4 view3).trans
      (congrArg₂ Bool.and (congrArg₂ Bool.and formation pair_accepted) guard3)

private theorem body2_accepted : FormationSensitiveElaboration.termReplayAccepted NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 122 context2 body2 type2 = true := by
  have formation := formation2
  unfold formed at formation
  rw [shape2] at formation
  exact (FormationSensitiveElaboration.lambda_replay_factor NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 121 context2 body3 type2 domain2 type3 view2).trans
      (congrArg₂ Bool.and (congrArg₂ Bool.and formation body3_accepted) guard2)

private theorem body1_accepted : FormationSensitiveElaboration.termReplayAccepted NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 123 context1 body1 type1 = true := by
  have formation := formation1
  unfold formed at formation
  rw [shape1] at formation
  exact (FormationSensitiveElaboration.lambda_replay_factor NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 122 context1 body2 type1 domain1 type2 view1).trans
      (congrArg₂ Bool.and (congrArg₂ Bool.and formation body2_accepted) guard1)

private theorem method_acceptance_body : FormationSensitiveElaboration.termReplayAccepted NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 124 contextAPWNV methodSource type0 = true := by
  have formation := formation0
  unfold formed at formation
  rw [shape0] at formation
  exact (FormationSensitiveElaboration.lambda_replay_factor NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 123 contextAPWNV body1 type0 domain0 type1 view0).trans
      (congrArg₂ Bool.and (congrArg₂ Bool.and formation body1_accepted) guard0)

#print axioms method_acceptance_body

theorem method_accepted : FormationSensitiveElaboration.termReplayAccepted NativeVectorAll.rules
    NativeVectorAll.decoder NativeVectorAll.choices 124 contextAPWNV methodSource methodType = true := by
  have accepted := method_acceptance_body
  unfold type0 at accepted
  exact accepted

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

theorem method_produced :
    (FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
      124 contextAPWNV methodSource methodType).isSome = true :=
  term_produced_of_replay NativeVectorAll.rules NativeVectorAll.decoder NativeVectorAll.choices
    124 contextAPWNV methodSource methodType method_accepted

noncomputable def methodCode : FormationSensitiveElaboration.Code Tower.Head NativeVectorAll.decoder.Code 5 :=
  FormationSensitiveElaboration.producedTermCode NativeVectorAll.rules NativeVectorAll.choices
    124 contextAPWNV methodSource methodType method_produced

theorem methodCode_origin :
    FormationSensitiveElaboration.check NativeVectorAll.rules NativeVectorAll.choices
      124 contextAPWNV methodSource methodType = some methodCode := by
  unfold methodCode
  exact FormationSensitiveElaboration.producedTermCode_origin NativeVectorAll.rules NativeVectorAll.choices
    124 contextAPWNV methodSource methodType method_produced

theorem methodCode_replay :
    StructuralTypingReplay.check
      (ConversionCode := FormationSensitiveElaboration.ConversionCode Tower.Head NativeVectorAll.decoder.Code)
      NativeVectorAll.rules
      (fun code left right => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right)
      contextAPWNV methodSource methodType methodCode = true := by
  unfold methodCode
  exact (FormationSensitiveElaboration.termReplayAccepted_eq_produced_code NativeVectorAll.rules
    NativeVectorAll.decoder NativeVectorAll.choices 124 contextAPWNV methodSource methodType
    method_produced).symm.trans method_accepted

#print axioms method_accepted
#print axioms method_produced
#print axioms methodCode_origin
#print axioms methodCode_replay
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.ReplayComponents
